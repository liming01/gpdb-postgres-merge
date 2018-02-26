/*-------------------------------------------------------------------------
 *
 * vacuumlazy.c
 *	  Concurrent ("lazy") vacuuming.
 *
 *
 * The major space usage for LAZY VACUUM is storage for the array of dead
 * tuple TIDs, with the next biggest need being storage for per-disk-page
 * free space info.  We want to ensure we can vacuum even the very largest
 * relations with finite memory space usage.  To do that, we set upper bounds
 * on the number of tuples and pages we will keep track of at once.
 *
 * We are willing to use at most maintenance_work_mem memory space to keep
 * track of dead tuples.  We initially allocate an array of TIDs of that size,
 * with an upper limit that depends on table size (this limit ensures we don't
 * allocate a huge area uselessly for vacuuming small tables).	If the array
 * threatens to overflow, we suspend the heap scan phase and perform a pass of
 * index cleanup and page compaction, then resume the heap scan with an empty
 * TID array.
 *
 * If we're processing a table with no indexes, we can just vacuum each page
 * as we go; there's no need to save up multiple tuples to minimize the number
 * of index scans performed.  So we don't use maintenance_work_mem memory for
 * the TID array, just enough to hold as many heap tuples as fit on one page.
 *
 *
 * Portions Copyright (c) 1996-2010, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/commands/vacuumlazy.c,v 1.136 2010/07/06 19:18:56 momjian Exp $
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <math.h>

#include "access/genam.h"
#include "access/heapam.h"
#include "access/nbtree.h"
#include "access/transam.h"
#include "access/aosegfiles.h"
#include "access/aocssegfiles.h"
#include "access/aomd.h"
#include "access/appendonly_compaction.h"
#include "access/aocs_compaction.h"
#include "access/visibilitymap.h"
#include "catalog/catalog.h"
#include "catalog/indexing.h"
#include "catalog/pg_appendonly_fn.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_proc.h"
#include "catalog/storage.h"
#include "commands/dbcommands.h"
#include "commands/vacuum.h"
#include "miscadmin.h"
#include "pgstat.h"
#include "postmaster/autovacuum.h"
#include "storage/bufmgr.h"
#include "storage/freespace.h"
#include "storage/lmgr.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/pg_rusage.h"
#include "utils/tqual.h"

#include "cdb/cdbappendonlyam.h"
#include "cdb/cdbvars.h"
#include "storage/smgr.h"
#include "utils/faultinjector.h"
#include "utils/snapmgr.h"


/*
 * Space/time tradeoff parameters: do these need to be user-tunable?
 *
 * To consider truncating the relation, we want there to be at least
 * REL_TRUNCATE_MINIMUM or (relsize / REL_TRUNCATE_FRACTION) (whichever
 * is less) potentially-freeable pages.
 */
#define REL_TRUNCATE_MINIMUM	1000
#define REL_TRUNCATE_FRACTION	16

/*
 * Guesstimation of number of dead tuples per page.  This is used to
 * provide an upper limit to memory allocated when vacuuming small
 * tables.
 */
#define LAZY_ALLOC_TUPLES		MaxHeapTuplesPerPage

/*
 * Before we consider skipping a page that's marked as clean in
 * visibility map, we must've seen at least this many clean pages.
 */
#define SKIP_PAGES_THRESHOLD	32

typedef struct LVRelStats
{
	/* hasindex = true means two-pass strategy; false means one-pass */
	bool		hasindex;
	bool		scanned_all;	/* have we scanned all pages (this far)? */
	/* Overall statistics about rel */
	BlockNumber rel_pages;		/* total number of pages */
	BlockNumber scanned_pages;	/* number of pages we examined */
	double		scanned_tuples;	/* counts only tuples on scanned pages */
	double		old_rel_tuples; /* previous value of pg_class.reltuples */
	double		new_rel_tuples; /* new estimated total # of tuples */
	BlockNumber pages_removed;
	double		tuples_deleted;
	BlockNumber nonempty_pages; /* actually, last nonempty page + 1 */
	/* List of TIDs of tuples we intend to delete */
	/* NB: this list is ordered by TID address */
	int			num_dead_tuples;	/* current # of entries */
	int			max_dead_tuples;	/* # slots allocated in array */
	ItemPointer dead_tuples;	/* array of ItemPointerData */
	int			num_index_scans;
	TransactionId latestRemovedXid;
} LVRelStats;


/* A few variables that don't seem worth passing around as parameters */
static int	elevel = -1;

static TransactionId OldestXmin;
static TransactionId FreezeLimit;

static BufferAccessStrategy vac_strategy;


/* non-export function prototypes */
static void lazy_vacuum_aorel(Relation onerel, VacuumStmt *vacstmt);
static void lazy_scan_heap(Relation onerel, LVRelStats *vacrelstats,
			   Relation *Irel, int nindexes, bool scan_all);
static void lazy_vacuum_heap(Relation onerel, LVRelStats *vacrelstats);
static void lazy_vacuum_index(Relation indrel,
				  IndexBulkDeleteResult **stats,
				  LVRelStats *vacrelstats);
static void lazy_cleanup_index(Relation indrel,
				   IndexBulkDeleteResult *stats,
				   LVRelStats *vacrelstats);
static int lazy_vacuum_page(Relation onerel, BlockNumber blkno, Buffer buffer,
				 int tupindex, LVRelStats *vacrelstats);
static void lazy_truncate_heap(Relation onerel, LVRelStats *vacrelstats);
static BlockNumber count_nondeletable_pages(Relation onerel,
						 LVRelStats *vacrelstats);
static void lazy_space_alloc(LVRelStats *vacrelstats, BlockNumber relblocks);
static void lazy_record_dead_tuple(LVRelStats *vacrelstats,
					   ItemPointer itemptr);
static bool lazy_tid_reaped(ItemPointer itemptr, void *state);
static int	vac_cmp_itemptr(const void *left, const void *right);


/*
 *	lazy_vacuum_rel() -- perform LAZY VACUUM for one heap relation
 *
 *		This routine vacuums a single heap, cleans out its indexes, and
 *		updates its relpages and reltuples statistics.
 *
 *		At entry, we have already established a transaction and opened
 *		and locked the relation.
 */
void
lazy_vacuum_rel(Relation onerel, VacuumStmt *vacstmt,
				BufferAccessStrategy bstrategy)
{
	LVRelStats *vacrelstats;
	Relation   *Irel;
	int			nindexes;
	BlockNumber possibly_freeable;
	PGRUsage	ru0;
	TimestampTz starttime = 0;
	bool		scan_all;		/* should we scan all pages? */
	TransactionId freezeTableLimit;

	pg_rusage_init(&ru0);

	/* measure elapsed time iff autovacuum logging requires it */
	if (IsAutoVacuumWorkerProcess() && Log_autovacuum_min_duration > 0)
		starttime = GetCurrentTimestamp();

	if (vacstmt->options & VACOPT_VERBOSE)
		elevel = INFO;
	else
		elevel = DEBUG2;

	if (Gp_role == GP_ROLE_DISPATCH)
		elevel = DEBUG2; /* vacuum and analyze messages aren't interesting from the QD */

#ifdef FAULT_INJECTOR
	if (vacstmt->appendonly_phase == AOVAC_DROP)
	{
			FaultInjector_InjectFaultIfSet(
				CompactionBeforeSegmentFileDropPhase,
				DDLNotSpecified,
				"",	// databaseName
				RelationGetRelationName(onerel)); // tableName
	}
	if (vacstmt->appendonly_phase == AOVAC_CLEANUP)
	{
			FaultInjector_InjectFaultIfSet(
				CompactionBeforeCleanupPhase,
				DDLNotSpecified,
				"",	// databaseName
				RelationGetRelationName(onerel)); // tableName
	}
#endif

	/*
	 * MPP-23647.  Update xid limits for heap as well as appendonly
	 * relations.  This allows setting relfrozenxid to correct value
	 * for an appendonly (AO/CO) table.
	 */
	vac_strategy = bstrategy;

	vacuum_set_xid_limits(vacstmt->freeze_min_age, vacstmt->freeze_table_age,
						  onerel->rd_rel->relisshared,
						  &OldestXmin, &FreezeLimit, &freezeTableLimit);
	scan_all = TransactionIdPrecedesOrEquals(onerel->rd_rel->relfrozenxid,
											 freezeTableLimit);

	/*
	 * Execute the various vacuum operations. Appendonly tables are treated
	 * differently.
	 */
	if (RelationIsAoRows(onerel) || RelationIsAoCols(onerel))
	{
		lazy_vacuum_aorel(onerel, vacstmt);
		return;
	}

	vacrelstats = (LVRelStats *) palloc0(sizeof(LVRelStats));

	/* heap relation */

	vacrelstats->num_index_scans = 0;

	/* Open all indexes of the relation */
	vac_open_indexes(onerel, RowExclusiveLock, &nindexes, &Irel);
	vacrelstats->hasindex = (nindexes > 0);

	/* Do the vacuuming */
	lazy_scan_heap(onerel, vacrelstats, Irel, nindexes, scan_all);

	/* Done with indexes */
	vac_close_indexes(nindexes, Irel, NoLock);

	/*
	 * Optionally truncate the relation.
	 *
	 * Don't even think about it unless we have a shot at releasing a goodly
	 * number of pages.  Otherwise, the time taken isn't worth it.
	 */
	possibly_freeable = vacrelstats->rel_pages - vacrelstats->nonempty_pages;
	if (possibly_freeable > 0 &&
		(possibly_freeable >= REL_TRUNCATE_MINIMUM ||
		 possibly_freeable >= vacrelstats->rel_pages / REL_TRUNCATE_FRACTION))
		lazy_truncate_heap(onerel, vacrelstats);

	/* Vacuum the Free Space Map */
	FreeSpaceMapVacuum(onerel);

	/*
	 * Update statistics in pg_class.  But only if we didn't skip any pages;
	 * the tuple count only includes tuples from the pages we've visited, and
	 * we haven't frozen tuples in unvisited pages either.  The page count is
	 * accurate in any case, but because we use the reltuples / relpages ratio
	 * in the planner, it's better to not update relpages either if we can't
	 * update reltuples.
	 */
	if (vacrelstats->scanned_all)
		vac_update_relstats(onerel,
							vacrelstats->rel_pages, vacrelstats->new_rel_tuples,
							vacrelstats->hasindex,
							(vacrelstats->scanned_pages < vacrelstats->rel_pages) ?
							InvalidTransactionId :
							FreezeLimit,
							true /* isvacuum */);

	/* report results to the stats collector, too */
	pgstat_report_vacuum(RelationGetRelid(onerel),
						 onerel->rd_rel->relisshared,
						 vacrelstats->new_rel_tuples);

	if (gp_indexcheck_vacuum == INDEX_CHECK_ALL ||
		(gp_indexcheck_vacuum == INDEX_CHECK_SYSTEM &&
		 PG_CATALOG_NAMESPACE == RelationGetNamespace(onerel)))
	{
		int			i;

		for (i = 0; i < nindexes; i++)
		{
			if (Irel[i]->rd_rel->relam == BTREE_AM_OID)
				_bt_validate_vacuum(Irel[i], onerel, OldestXmin);
		}
	}

	/* and log the action if appropriate */
	if (IsAutoVacuumWorkerProcess() && Log_autovacuum_min_duration >= 0)
	{
		if (Log_autovacuum_min_duration == 0 ||
			TimestampDifferenceExceeds(starttime, GetCurrentTimestamp(),
									   Log_autovacuum_min_duration))
			ereport(LOG,
					(errmsg("automatic vacuum of table \"%s.%s.%s\": index scans: %d\n"
							"pages: %d removed, %d remain\n"
							"tuples: %.0f removed, %.0f remain\n"
							"system usage: %s",
							get_database_name(MyDatabaseId),
							get_namespace_name(RelationGetNamespace(onerel)),
							RelationGetRelationName(onerel),
							vacrelstats->num_index_scans,
							vacrelstats->pages_removed,
							vacrelstats->rel_pages,
							vacrelstats->tuples_deleted,
							vacrelstats->new_rel_tuples,
							pg_rusage_show(&ru0))));
	}
}

/*
 * lazy_vacuum_aorel -- perform LAZY VACUUM for one Append-only relation.
 */
static void
lazy_vacuum_aorel(Relation onerel, VacuumStmt *vacstmt)
{
	LVRelStats *vacrelstats;
	bool		update_relstats = true;

	vacrelstats = (LVRelStats *) palloc0(sizeof(LVRelStats));

	switch (vacstmt->appendonly_phase)
	{
		case AOVAC_PREPARE:
			elogif(Debug_appendonly_print_compaction, LOG,
				   "Vacuum prepare phase %s", RelationGetRelationName(onerel));

			vacuum_appendonly_indexes(onerel, vacstmt);
			if (RelationIsAoRows(onerel))
				AppendOnlyTruncateToEOF(onerel);
			else
				AOCSTruncateToEOF(onerel);

			/*
			 * MPP-23647.  For empty tables, we skip compaction phase
			 * and cleanup phase.  Therefore, we update the stats
			 * (specifically, relfrozenxid) in prepare phase if the
			 * table is empty.  Otherwise, the stats will be updated in
			 * the cleanup phase, when we would have computed the
			 * correct values for stats.
			 */
			if (vacstmt->appendonly_relation_empty)
			{
				update_relstats = true;
				/*
				 * For an empty relation, the only stats we care about
				 * is relfrozenxid and relhasindex.  We need to be
				 * mindful of correctly setting relhasindex here.
				 * relfrozenxid is already taken care of above by
				 * calling vacuum_set_xid_limits().
				 */
				vacrelstats->hasindex = onerel->rd_rel->relhasindex;
			}
			else
			{
				/*
				 * For a non-empty relation, follow the usual
				 * compaction phases and do not update stats in
				 * prepare phase.
				 */
				update_relstats = false;
			}
			break;

		case AOVAC_COMPACT:
		case AOVAC_DROP:
			vacuum_appendonly_rel(onerel, vacstmt);
			update_relstats = false;
			break;

		case AOVAC_CLEANUP:
			elogif(Debug_appendonly_print_compaction, LOG,
				   "Vacuum cleanup phase %s", RelationGetRelationName(onerel));

			vacuum_appendonly_fill_stats(onerel, GetActiveSnapshot(),
										 &vacrelstats->rel_pages,
										 &vacrelstats->new_rel_tuples,
										 &vacrelstats->hasindex);
			/* reset the remaining LVRelStats values */
			vacrelstats->nonempty_pages = 0;
			vacrelstats->num_dead_tuples = 0;
			vacrelstats->max_dead_tuples = 0;
			vacrelstats->tuples_deleted = 0;
			vacrelstats->pages_removed = 0;
			break;

		default:
			elog(ERROR, "invalid AO vacuum phase %d", vacstmt->appendonly_phase);
	}

	if (update_relstats)
	{
		/* Update statistics in pg_class */
		vac_update_relstats(onerel,
							vacrelstats->rel_pages,
							vacrelstats->new_rel_tuples,
							vacrelstats->hasindex,
							FreezeLimit,
							true /* isvacuum */);

		/* report results to the stats collector, too */
		pgstat_report_vacuum(RelationGetRelid(onerel),
							 onerel->rd_rel->relisshared,
							 vacrelstats->new_rel_tuples);
	}
}

/*
 * For Hot Standby we need to know the highest transaction id that will
 * be removed by any change. VACUUM proceeds in a number of passes so
 * we need to consider how each pass operates. The first phase runs
 * heap_page_prune(), which can issue XLOG_HEAP2_CLEAN records as it
 * progresses - these will have a latestRemovedXid on each record.
 * In some cases this removes all of the tuples to be removed, though
 * often we have dead tuples with index pointers so we must remember them
 * for removal in phase 3. Index records for those rows are removed
 * in phase 2 and index blocks do not have MVCC information attached.
 * So before we can allow removal of any index tuples we need to issue
 * a WAL record containing the latestRemovedXid of rows that will be
 * removed in phase three. This allows recovery queries to block at the
 * correct place, i.e. before phase two, rather than during phase three
 * which would be after the rows have become inaccessible.
 */
static void
vacuum_log_cleanup_info(Relation rel, LVRelStats *vacrelstats)
{
	/*
	 * No need to log changes for temp tables, they do not contain data
	 * visible on the standby server.
	 */
	if (rel->rd_istemp || !XLogIsNeeded())
		return;

	/*
	 * No need to write the record at all unless it contains a valid value
	 */
	if (TransactionIdIsValid(vacrelstats->latestRemovedXid))
		(void) log_heap_cleanup_info(rel->rd_node, vacrelstats->latestRemovedXid);
}

/*
 *	lazy_scan_heap() -- scan an open heap relation
 *
 *		This routine sets commit status bits, builds lists of dead tuples
 *		and pages with free space, and calculates statistics on the number
 *		of live tuples in the heap.  When done, or when we run low on space
 *		for dead-tuple TIDs, invoke vacuuming of indexes and heap.
 *
 *		If there are no indexes then we just vacuum each dirty page as we
 *		process it, since there's no point in gathering many tuples.
 */
static void
lazy_scan_heap(Relation onerel, LVRelStats *vacrelstats,
			   Relation *Irel, int nindexes, bool scan_all)
{
	BlockNumber nblocks,
				blkno;
	HeapTupleData tuple;
	char	   *relname;
	BlockNumber empty_pages,
				vacuumed_pages;
	double		num_tuples,
				tups_vacuumed,
				nkeep,
				nunused;
	IndexBulkDeleteResult **indstats;
	int			i;
	int reindex_count = 1;
	PGRUsage	ru0;
	Buffer		vmbuffer = InvalidBuffer;
	BlockNumber all_visible_streak;

	pg_rusage_init(&ru0);

	relname = RelationGetRelationName(onerel);
	ereport(elevel,
			(errmsg("vacuuming \"%s.%s\"",
					get_namespace_name(RelationGetNamespace(onerel)),
					relname)));

	empty_pages = vacuumed_pages = 0;
	num_tuples = tups_vacuumed = nkeep = nunused = 0;

	indstats = (IndexBulkDeleteResult **)
		palloc0(nindexes * sizeof(IndexBulkDeleteResult *));

	nblocks = RelationGetNumberOfBlocks(onerel);
	vacrelstats->rel_pages = nblocks;
	vacrelstats->scanned_pages = 0;
	vacrelstats->nonempty_pages = 0;
	vacrelstats->latestRemovedXid = InvalidTransactionId;

	lazy_space_alloc(vacrelstats, nblocks);

	all_visible_streak = 0;
	for (blkno = 0; blkno < nblocks; blkno++)
	{
		Buffer		buf;
		Page		page;
		OffsetNumber offnum,
					maxoff;
		bool		tupgone,
					hastup;
		int			prev_dead_count;
		OffsetNumber frozen[MaxOffsetNumber];
		int			nfrozen;
		Size		freespace;
		bool		all_visible_according_to_vm = false;
		bool		all_visible;
		bool		has_dead_tuples;

		/*
		 * Skip pages that don't require vacuuming according to the visibility
		 * map. But only if we've seen a streak of at least
		 * SKIP_PAGES_THRESHOLD pages marked as clean. Since we're reading
		 * sequentially, the OS should be doing readahead for us and there's
		 * no gain in skipping a page now and then. You need a longer run of
		 * consecutive skipped pages before it's worthwhile. Also, skipping
		 * even a single page means that we can't update relfrozenxid or
		 * reltuples, so we only want to do it if there's a good chance to
		 * skip a goodly number of pages.
		 */
		if (!scan_all)
		{
			all_visible_according_to_vm =
				visibilitymap_test(onerel, blkno, &vmbuffer);
			if (all_visible_according_to_vm)
			{
				all_visible_streak++;
				if (all_visible_streak >= SKIP_PAGES_THRESHOLD)
				{
					vacrelstats->scanned_all = false;
					continue;
				}
			}
			else
				all_visible_streak = 0;
		}

		vacuum_delay_point();

		vacrelstats->scanned_pages++;

		/*
		 * If we are close to overrunning the available space for dead-tuple
		 * TIDs, pause and do a cycle of vacuuming before we tackle this page.
		 */
		if ((vacrelstats->max_dead_tuples - vacrelstats->num_dead_tuples) < MaxHeapTuplesPerPage &&
			vacrelstats->num_dead_tuples > 0)
		{
			/* Log cleanup info before we touch indexes */
			vacuum_log_cleanup_info(onerel, vacrelstats);

			/* Remove index entries */
			for (i = 0; i < nindexes; i++)
				lazy_vacuum_index(Irel[i], &indstats[i], vacrelstats);

			reindex_count++;

			/* Remove tuples from heap */
			lazy_vacuum_heap(onerel, vacrelstats);

			/*
			 * Forget the now-vacuumed tuples, and press on, but be careful
			 * not to reset latestRemovedXid since we want that value to be
			 * valid.
			 */
			vacrelstats->num_dead_tuples = 0;
			vacrelstats->num_index_scans++;
		}

		buf = ReadBufferExtended(onerel, MAIN_FORKNUM, blkno,
								 RBM_NORMAL, vac_strategy);

		/* We need buffer cleanup lock so that we can prune HOT chains. */
		LockBufferForCleanup(buf);

		page = BufferGetPage(buf);

		if (PageIsNew(page))
		{
			/*
			 * An all-zeroes page could be left over if a backend extends the
			 * relation but crashes before initializing the page. Reclaim such
			 * pages for use.
			 *
			 * We have to be careful here because we could be looking at a
			 * page that someone has just added to the relation and not yet
			 * been able to initialize (see RelationGetBufferForTuple). To
			 * protect against that, release the buffer lock, grab the
			 * relation extension lock momentarily, and re-lock the buffer. If
			 * the page is still uninitialized by then, it must be left over
			 * from a crashed backend, and we can initialize it.
			 *
			 * We don't really need the relation lock when this is a new or
			 * temp relation, but it's probably not worth the code space to
			 * check that, since this surely isn't a critical path.
			 *
			 * Note: the comparable code in vacuum.c need not worry because
			 * it's got exclusive lock on the whole relation.
			 */
			LockBuffer(buf, BUFFER_LOCK_UNLOCK);

			LockRelationForExtension(onerel, ExclusiveLock);
			UnlockRelationForExtension(onerel, ExclusiveLock);

			LockBufferForCleanup(buf);
			if (PageIsNew(page))
			{
				ereport(WARNING,
				(errmsg("relation \"%s\" page %u is uninitialized --- fixing",
						relname, blkno)));
				PageInit(page, BufferGetPageSize(buf), 0);
				empty_pages++;
			}
			freespace = PageGetHeapFreeSpace(page);
			MarkBufferDirty(buf);
			UnlockReleaseBuffer(buf);

			RecordPageWithFreeSpace(onerel, blkno, freespace);
			continue;
		}

		if (PageIsEmpty(page))
		{
			empty_pages++;
			freespace = PageGetHeapFreeSpace(page);

			if (!PageIsAllVisible(page))
			{
				PageSetAllVisible(page);
				MarkBufferDirty(buf);
			}

			LockBuffer(buf, BUFFER_LOCK_UNLOCK);

			/* Update the visibility map */
			if (!all_visible_according_to_vm)
			{
				visibilitymap_pin(onerel, blkno, &vmbuffer);
				LockBuffer(buf, BUFFER_LOCK_SHARE);
				if (PageIsAllVisible(page))
					visibilitymap_set(onerel, blkno, PageGetLSN(page), &vmbuffer);
				LockBuffer(buf, BUFFER_LOCK_UNLOCK);
			}

			ReleaseBuffer(buf);
			RecordPageWithFreeSpace(onerel, blkno, freespace);
			continue;
		}

		/*
		 * Prune all HOT-update chains in this page.
		 *
		 * We count tuples removed by the pruning step as removed by VACUUM.
		 */
		tups_vacuumed += heap_page_prune(onerel, buf, OldestXmin, false,
										 &vacrelstats->latestRemovedXid);

		/*
		 * Now scan the page to collect vacuumable items and check for tuples
		 * requiring freezing.
		 */
		all_visible = true;
		has_dead_tuples = false;
		nfrozen = 0;
		hastup = false;
		prev_dead_count = vacrelstats->num_dead_tuples;
		maxoff = PageGetMaxOffsetNumber(page);
		for (offnum = FirstOffsetNumber;
			 offnum <= maxoff;
			 offnum = OffsetNumberNext(offnum))
		{
			ItemId		itemid;

			itemid = PageGetItemId(page, offnum);

			/* Unused items require no processing, but we count 'em */
			if (!ItemIdIsUsed(itemid))
			{
				nunused += 1;
				continue;
			}

			/* Redirect items mustn't be touched */
			if (ItemIdIsRedirected(itemid))
			{
				hastup = true;	/* this page won't be truncatable */
				continue;
			}

			ItemPointerSet(&(tuple.t_self), blkno, offnum);

			/*
			 * DEAD item pointers are to be vacuumed normally; but we don't
			 * count them in tups_vacuumed, else we'd be double-counting (at
			 * least in the common case where heap_page_prune() just freed up
			 * a non-HOT tuple).
			 */
			if (ItemIdIsDead(itemid))
			{
				lazy_record_dead_tuple(vacrelstats, &(tuple.t_self));
				all_visible = false;
				continue;
			}

			Assert(ItemIdIsNormal(itemid));

			tuple.t_data = (HeapTupleHeader) PageGetItem(page, itemid);
			tuple.t_len = ItemIdGetLength(itemid);

			tupgone = false;

			switch (HeapTupleSatisfiesVacuum(onerel, tuple.t_data, OldestXmin, buf))
			{
				case HEAPTUPLE_DEAD:

					/*
					 * Ordinarily, DEAD tuples would have been removed by
					 * heap_page_prune(), but it's possible that the tuple
					 * state changed since heap_page_prune() looked.  In
					 * particular an INSERT_IN_PROGRESS tuple could have
					 * changed to DEAD if the inserter aborted.  So this
					 * cannot be considered an error condition.
					 *
					 * If the tuple is HOT-updated then it must only be
					 * removed by a prune operation; so we keep it just as if
					 * it were RECENTLY_DEAD.  Also, if it's a heap-only
					 * tuple, we choose to keep it, because it'll be a lot
					 * cheaper to get rid of it in the next pruning pass than
					 * to treat it like an indexed tuple.
					 */
					if (HeapTupleIsHotUpdated(&tuple) ||
						HeapTupleIsHeapOnly(&tuple))
						nkeep += 1;
					else
						tupgone = true; /* we can delete the tuple */
					all_visible = false;
					break;
				case HEAPTUPLE_LIVE:
					/* Tuple is good --- but let's do some validity checks */
					if (onerel->rd_rel->relhasoids &&
						!OidIsValid(HeapTupleGetOid(&tuple)))
						elog(WARNING, "relation \"%s\" TID %u/%u: OID is invalid",
							 relname, blkno, offnum);

					/*
					 * Is the tuple definitely visible to all transactions?
					 *
					 * NB: Like with per-tuple hint bits, we can't set the
					 * PD_ALL_VISIBLE flag if the inserter committed
					 * asynchronously. See SetHintBits for more info. Check
					 * that the HEAP_XMIN_COMMITTED hint bit is set because of
					 * that.
					 */
					if (all_visible)
					{
						TransactionId xmin;

						if (!(tuple.t_data->t_infomask & HEAP_XMIN_COMMITTED))
						{
							all_visible = false;
							break;
						}

						/*
						 * The inserter definitely committed. But is it old
						 * enough that everyone sees it as committed?
						 */
						xmin = HeapTupleHeaderGetXmin(tuple.t_data);
						if (!TransactionIdPrecedes(xmin, OldestXmin))
						{
							all_visible = false;
							break;
						}

						/*
						 * Like in HeapTupleSatisfiesVacuum(), even if the
						 * test against OldestXmin says the tuple is visible
						 * to everyone, we must also check against the distributed
						 * snapshot mechanism.
						 */
						if (TransactionIdIsNormal(HeapTupleHeaderGetXmin(tuple.t_data)) &&
							!(tuple.t_data->t_infomask2 & HEAP_XMIN_DISTRIBUTED_SNAPSHOT_IGNORE))
						{
							if (!localXidSatisfiesAnyDistributedSnapshot(HeapTupleHeaderGetXmin(tuple.t_data)))
							{
								all_visible = false;
								break;
							}
						}
					}
					break;
				case HEAPTUPLE_RECENTLY_DEAD:

					/*
					 * If tuple is recently deleted then we must not remove it
					 * from relation.
					 */
					nkeep += 1;
					all_visible = false;
					break;
				case HEAPTUPLE_INSERT_IN_PROGRESS:
					/* This is an expected case during concurrent vacuum */
					all_visible = false;
					break;
				case HEAPTUPLE_DELETE_IN_PROGRESS:
					/* This is an expected case during concurrent vacuum */
					all_visible = false;
					break;
				default:
					elog(ERROR, "unexpected HeapTupleSatisfiesVacuum result");
					break;
			}

			if (tupgone)
			{
				lazy_record_dead_tuple(vacrelstats, &(tuple.t_self));
				HeapTupleHeaderAdvanceLatestRemovedXid(tuple.t_data,
											 &vacrelstats->latestRemovedXid);
				tups_vacuumed += 1;
				has_dead_tuples = true;
			}
			else
			{
				num_tuples += 1;
				hastup = true;

				/*
				 * Each non-removable tuple must be checked to see if it needs
				 * freezing.  Note we already have exclusive buffer lock.
				 */
				if (heap_freeze_tuple(tuple.t_data, &FreezeLimit,
									  InvalidBuffer, false))
					frozen[nfrozen++] = offnum;
			}
		}						/* scan along page */

		/*
		 * If we froze any tuples, mark the buffer dirty, and write a WAL
		 * record recording the changes.  We must log the changes to be
		 * crash-safe against future truncation of CLOG.
		 */
		if (nfrozen > 0)
		{
			MarkBufferDirty(buf);
			/* no XLOG for temp tables, though */
			if (!onerel->rd_istemp)
			{
				XLogRecPtr	recptr;

				recptr = log_heap_freeze(onerel, buf, FreezeLimit,
										 frozen, nfrozen);
				PageSetLSN(page, recptr);
			}
		}

		/*
		 * If there are no indexes then we can vacuum the page right now
		 * instead of doing a second scan.
		 */
		if (nindexes == 0 &&
			vacrelstats->num_dead_tuples > 0)
		{
			/* Remove tuples from heap */
			lazy_vacuum_page(onerel, blkno, buf, 0, vacrelstats);
			has_dead_tuples = false;

			/*
			 * Forget the now-vacuumed tuples, and press on, but be careful
			 * not to reset latestRemovedXid since we want that value to be
			 * valid.
			 */
			vacrelstats->num_dead_tuples = 0;
			vacuumed_pages++;
		}

		freespace = PageGetHeapFreeSpace(page);

		/* Update the all-visible flag on the page */
		if (!PageIsAllVisible(page) && all_visible)
		{
			PageSetAllVisible(page);
			MarkBufferDirty(buf);
		}
		/*
		 * It's possible for the value returned by GetOldestXmin() to move
		 * backwards, so it's not wrong for us to see tuples that appear to
		 * not be visible to everyone yet, while PD_ALL_VISIBLE is already
		 * set. The real safe xmin value never moves backwards, but
		 * GetOldestXmin() is conservative and sometimes returns a value
		 * that's unnecessarily small, so if we see that contradiction it
		 * just means that the tuples that we think are not visible to
		 * everyone yet actually are, and the PD_ALL_VISIBLE flag is correct.
		 *
		 * There should never be dead tuples on a page with PD_ALL_VISIBLE
		 * set, however.
		 */
		else if (PageIsAllVisible(page) && has_dead_tuples)
		{
			elog(WARNING, "page containing dead tuples is marked as all-visible in relation \"%s\" page %u",
				 relname, blkno);
			PageClearAllVisible(page);
			MarkBufferDirty(buf);

			/*
			 * Normally, we would drop the lock on the heap page before
			 * updating the visibility map, but since this case shouldn't
			 * happen anyway, don't worry about that.
			 */
			visibilitymap_clear(onerel, blkno);
		}

		LockBuffer(buf, BUFFER_LOCK_UNLOCK);

		/* Update the visibility map */
		if (!all_visible_according_to_vm && all_visible)
		{
			visibilitymap_pin(onerel, blkno, &vmbuffer);
			LockBuffer(buf, BUFFER_LOCK_SHARE);
			if (PageIsAllVisible(page))
				visibilitymap_set(onerel, blkno, PageGetLSN(page), &vmbuffer);
			LockBuffer(buf, BUFFER_LOCK_UNLOCK);
		}

		ReleaseBuffer(buf);

		/* Remember the location of the last page with nonremovable tuples */
		if (hastup)
			vacrelstats->nonempty_pages = blkno + 1;

		/*
		 * If we remembered any tuples for deletion, then the page will be
		 * visited again by lazy_vacuum_heap, which will compute and record
		 * its post-compaction free space.	If not, then we're done with this
		 * page, so remember its free space as-is.	(This path will always be
		 * taken if there are no indexes.)
		 */
		if (vacrelstats->num_dead_tuples == prev_dead_count)
			RecordPageWithFreeSpace(onerel, blkno, freespace);
	}

	/* save stats for use later */
	vacrelstats->scanned_tuples = num_tuples;
	vacrelstats->tuples_deleted = tups_vacuumed;

	/* now we can compute the new value for pg_class.reltuples */
	vacrelstats->new_rel_tuples = vac_estimate_reltuples(onerel, false,
														 nblocks,
														 vacrelstats->scanned_pages,
														 num_tuples);

	/* If any tuples need to be deleted, perform final vacuum cycle */
	/* XXX put a threshold on min number of tuples here? */
	if (vacrelstats->num_dead_tuples > 0)
	{
		/* Log cleanup info before we touch indexes */
		vacuum_log_cleanup_info(onerel, vacrelstats);

		/* Remove index entries */
		for (i = 0; i < nindexes; i++)
			lazy_vacuum_index(Irel[i], &indstats[i], vacrelstats);

		reindex_count++;

		/* Remove tuples from heap */
		lazy_vacuum_heap(onerel, vacrelstats);
		vacrelstats->num_index_scans++;
	}

	/* Release the pin on the visibility map page */
	if (BufferIsValid(vmbuffer))
	{
		ReleaseBuffer(vmbuffer);
		vmbuffer = InvalidBuffer;
	}

	/* Do post-vacuum cleanup and statistics update for each index */
	for (i = 0; i < nindexes; i++)
		lazy_cleanup_index(Irel[i], indstats[i], vacrelstats);

	/* If no indexes, make log report that lazy_vacuum_heap would've made */
	if (vacuumed_pages)
		ereport(elevel,
				(errmsg("\"%s\": removed %.0f row versions in %u pages",
						RelationGetRelationName(onerel),
						tups_vacuumed, vacuumed_pages)));

	ereport(elevel,
			(errmsg("\"%s\": found %.0f removable, %.0f nonremovable row versions in %u out of %u pages",
					RelationGetRelationName(onerel),
					tups_vacuumed, num_tuples,
					vacrelstats->scanned_pages, nblocks),
			 errdetail("%.0f dead row versions cannot be removed yet.\n"
					   "There were %.0f unused item pointers.\n"
					   "%u pages are entirely empty.\n"
					   "%s.",
					   nkeep,
					   nunused,
					   empty_pages,
					   pg_rusage_show(&ru0))));
}


/*
 *	lazy_vacuum_heap() -- second pass over the heap
 *
 *		This routine marks dead tuples as unused and compacts out free
 *		space on their pages.  Pages not having dead tuples recorded from
 *		lazy_scan_heap are not visited at all.
 *
 * Note: the reason for doing this as a second pass is we cannot remove
 * the tuples until we've removed their index entries, and we want to
 * process index entry removal in batches as large as possible.
 */
static void
lazy_vacuum_heap(Relation onerel, LVRelStats *vacrelstats)
{
	int			tupindex;
	int			npages;
	PGRUsage	ru0;

	pg_rusage_init(&ru0);
	npages = 0;

	tupindex = 0;

	while (tupindex < vacrelstats->num_dead_tuples)
	{
		BlockNumber tblk;
		Buffer		buf;
		Page		page;
		Size		freespace;

		vacuum_delay_point();

		tblk = ItemPointerGetBlockNumber(&vacrelstats->dead_tuples[tupindex]);

		buf = ReadBufferExtended(onerel, MAIN_FORKNUM, tblk, RBM_NORMAL,
								 vac_strategy);
		LockBufferForCleanup(buf);
		tupindex = lazy_vacuum_page(onerel, tblk, buf, tupindex, vacrelstats);

		/* Now that we've compacted the page, record its available space */
		page = BufferGetPage(buf);
		freespace = PageGetHeapFreeSpace(page);

		UnlockReleaseBuffer(buf);

		RecordPageWithFreeSpace(onerel, tblk, freespace);
		npages++;
	}

	ereport(elevel,
			(errmsg("\"%s\": removed %d row versions in %d pages",
					RelationGetRelationName(onerel),
					tupindex, npages),
			 errdetail("%s.",
					   pg_rusage_show(&ru0))));
}

/*
 *	lazy_vacuum_page() -- free dead tuples on a page
 *					 and repair its fragmentation.
 *
 * Caller must hold pin and buffer cleanup lock on the buffer.
 *
 * tupindex is the index in vacrelstats->dead_tuples of the first dead
 * tuple for this page.  We assume the rest follow sequentially.
 * The return value is the first tupindex after the tuples of this page.
 */
static int
lazy_vacuum_page(Relation onerel, BlockNumber blkno, Buffer buffer,
				 int tupindex, LVRelStats *vacrelstats)
{
	Page		page = BufferGetPage(buffer);
	OffsetNumber unused[MaxOffsetNumber];
	int			uncnt = 0;

	START_CRIT_SECTION();

	for (; tupindex < vacrelstats->num_dead_tuples; tupindex++)
	{
		BlockNumber tblk;
		OffsetNumber toff;
		ItemId		itemid;

		tblk = ItemPointerGetBlockNumber(&vacrelstats->dead_tuples[tupindex]);
		if (tblk != blkno)
			break;				/* past end of tuples for this block */
		toff = ItemPointerGetOffsetNumber(&vacrelstats->dead_tuples[tupindex]);
		itemid = PageGetItemId(page, toff);
		ItemIdSetUnused(itemid);
		unused[uncnt++] = toff;
	}

	PageRepairFragmentation(page);

	MarkBufferDirty(buffer);

	/* XLOG stuff */
	if (!onerel->rd_istemp)
	{
		XLogRecPtr	recptr;

		recptr = log_heap_clean(onerel, buffer,
								NULL, 0, NULL, 0,
								unused, uncnt,
								vacrelstats->latestRemovedXid);
		PageSetLSN(page, recptr);
	}

	END_CRIT_SECTION();

	return tupindex;
}

/*
 *	lazy_vacuum_index() -- vacuum one index relation.
 *
 *		Delete all the index entries pointing to tuples listed in
 *		vacrelstats->dead_tuples, and update running statistics.
 */
static void
lazy_vacuum_index(Relation indrel,
				  IndexBulkDeleteResult **stats,
				  LVRelStats *vacrelstats)
{
	IndexVacuumInfo ivinfo;
	PGRUsage	ru0;

	pg_rusage_init(&ru0);

	ivinfo.index = indrel;
	ivinfo.analyze_only = false;
	ivinfo.estimated_count = true;
	ivinfo.message_level = elevel;
	ivinfo.num_heap_tuples = vacrelstats->old_rel_tuples;
	ivinfo.strategy = vac_strategy;

	/* Do bulk deletion */
	*stats = index_bulk_delete(&ivinfo, *stats,
							   lazy_tid_reaped, (void *) vacrelstats);

	ereport(elevel,
			(errmsg("scanned index \"%s\" to remove %d row versions",
					RelationGetRelationName(indrel),
					vacrelstats->num_dead_tuples),
			 errdetail("%s.", pg_rusage_show(&ru0))));
}

/*
 *	lazy_cleanup_index() -- do post-vacuum cleanup for one index relation.
 */
static void
lazy_cleanup_index(Relation indrel,
				   IndexBulkDeleteResult *stats,
				   LVRelStats *vacrelstats)
{
	IndexVacuumInfo ivinfo;
	PGRUsage	ru0;

	pg_rusage_init(&ru0);

	ivinfo.index = indrel;
	ivinfo.analyze_only = false;
	ivinfo.estimated_count = !vacrelstats->scanned_all;
	ivinfo.message_level = elevel;
	ivinfo.num_heap_tuples = vacrelstats->new_rel_tuples;
	ivinfo.strategy = vac_strategy;

	stats = index_vacuum_cleanup(&ivinfo, stats);

	if (!stats)
		return;

	/*
	 * Now update statistics in pg_class, but only if the index says the count
	 * is accurate.
	 */
	if (!stats->estimated_count)
		vac_update_relstats(indrel,
							stats->num_pages, stats->num_index_tuples,
							false, InvalidTransactionId,
							true /* isvacuum */);

	ereport(elevel,
			(errmsg("index \"%s\" now contains %.0f row versions in %u pages",
					RelationGetRelationName(indrel),
					stats->num_index_tuples,
					stats->num_pages),
			 errdetail("%.0f index row versions were removed.\n"
			 "%u index pages have been deleted, %u are currently reusable.\n"
					   "%s.",
					   stats->tuples_removed,
					   stats->pages_deleted, stats->pages_free,
					   pg_rusage_show(&ru0))));

	pfree(stats);
}

/*
 * lazy_truncate_heap - try to truncate off any empty pages at the end
 */
static void
lazy_truncate_heap(Relation onerel, LVRelStats *vacrelstats)
{
	BlockNumber old_rel_pages = vacrelstats->rel_pages;
	BlockNumber new_rel_pages;
	PGRUsage	ru0;

	pg_rusage_init(&ru0);

	/*
	 * We need full exclusive lock on the relation in order to do truncation.
	 * If we can't get it, give up rather than waiting --- we don't want to
	 * block other backends, and we don't want to deadlock (which is quite
	 * possible considering we already hold a lower-grade lock).
	 */
	if (!ConditionalLockRelation(onerel, AccessExclusiveLock))
		return;

	/*
	 * Now that we have exclusive lock, look to see if the rel has grown
	 * whilst we were vacuuming with non-exclusive lock.  If so, give up; the
	 * newly added pages presumably contain non-deletable tuples.
	 */
	new_rel_pages = RelationGetNumberOfBlocks(onerel);
	if (new_rel_pages != old_rel_pages)
	{
		/* might as well use the latest news when we update pg_class stats */
		vacrelstats->rel_pages = new_rel_pages;
		UnlockRelation(onerel, AccessExclusiveLock);
		return;
	}

	/*
	 * Scan backwards from the end to verify that the end pages actually
	 * contain no tuples.  This is *necessary*, not optional, because other
	 * backends could have added tuples to these pages whilst we were
	 * vacuuming.
	 */
	new_rel_pages = count_nondeletable_pages(onerel, vacrelstats);

	if (new_rel_pages >= old_rel_pages)
	{
		/* can't do anything after all */
		UnlockRelation(onerel, AccessExclusiveLock);
		return;
	}

	/*
	 * Okay to truncate.
	 */
	RelationTruncate(onerel, new_rel_pages);

	/*
	 * We can release the exclusive lock as soon as we have truncated.	Other
	 * backends can't safely access the relation until they have processed the
	 * smgr invalidation that smgrtruncate sent out ... but that should happen
	 * as part of standard invalidation processing once they acquire lock on
	 * the relation.
	 */
	UnlockRelation(onerel, AccessExclusiveLock);

	/* update statistics */
	vacrelstats->rel_pages = new_rel_pages;
	vacrelstats->pages_removed = old_rel_pages - new_rel_pages;

	ereport(elevel,
			(errmsg("\"%s\": truncated %u to %u pages",
					RelationGetRelationName(onerel),
					old_rel_pages, new_rel_pages),
			 errdetail("%s.",
					   pg_rusage_show(&ru0))));
}


/*
 * Fills in the relation statistics for an append-only relation.
 *
 *	This information is used to update the reltuples and relpages information
 *	in pg_class. reltuples is the same as "pg_aoseg_<oid>:tupcount"
 *	column and we simulate relpages by subdividing the eof value
 *	("pg_aoseg_<oid>:eof") over the defined page size.
 */
void
vacuum_appendonly_fill_stats(Relation aorel, Snapshot snapshot,
							 BlockNumber *rel_pages, double *rel_tuples,
							 bool *relhasindex)
{
	FileSegTotals *fstotal;
	BlockNumber nblocks;
	char	   *relname;
	double		num_tuples;
	double		totalbytes;
	double		eof;
	int64       hidden_tupcount;
	AppendOnlyVisimap visimap;

	Assert(RelationIsAoRows(aorel) || RelationIsAoCols(aorel));

	relname = RelationGetRelationName(aorel);

	/* get updated statistics from the pg_aoseg table */
	if (RelationIsAoRows(aorel))
	{
		fstotal = GetSegFilesTotals(aorel, snapshot);
	}
	else
	{
		Assert(RelationIsAoCols(aorel));
		fstotal = GetAOCSSSegFilesTotals(aorel, snapshot);
	}

	/* calculate the values we care about */
	eof = (double)fstotal->totalbytes;
	num_tuples = (double)fstotal->totaltuples;
	totalbytes = eof;
	nblocks = (uint32)RelationGuessNumberOfBlocks(totalbytes);

	AppendOnlyVisimap_Init(&visimap,
						   aorel->rd_appendonly->visimaprelid,
						   aorel->rd_appendonly->visimapidxid,
						   AccessShareLock,
						   snapshot);
	hidden_tupcount = AppendOnlyVisimap_GetRelationHiddenTupleCount(&visimap);
	num_tuples -= hidden_tupcount;
	Assert(num_tuples > -1.0);
	AppendOnlyVisimap_Finish(&visimap, AccessShareLock);

	elogif (Debug_appendonly_print_compaction, LOG,
			"Gather statistics after vacuum for append-only relation %s: "
			"page count %d, tuple count %f",
			relname,
			nblocks, num_tuples);

	*rel_pages = nblocks;
	*rel_tuples = num_tuples;
	*relhasindex = aorel->rd_rel->relhasindex;

	ereport(elevel,
			(errmsg("\"%s\": found %.0f rows in %u pages.",
					relname, num_tuples, nblocks)));
	pfree(fstotal);
}

/*
 *	vacuum_appendonly_rel() -- vaccum an append-only relation
 *
 *		This procedure will be what gets executed both for VACUUM
 *		and VACUUM FULL (and also ANALYZE or any other thing that
 *		needs the pg_class stats updated).
 *
 *		The function can compact append-only segment files or just
 *		truncating the segment file to its existing eof.
 *
 *		Afterwards, the reltuples and relpages information in pg_class
 *		are updated. reltuples is the same as "pg_aoseg_<oid>:tupcount"
 *		column and we simulate relpages by subdividing the eof value
 *		("pg_aoseg_<oid>:eof") over the defined page size.
 *
 *
 *		There are txn ids, hint bits, free space, dead tuples,
 *		etc. these are all irrelevant in the append only relation context.
 *
 */
void
vacuum_appendonly_rel(Relation aorel, VacuumStmt *vacstmt)
{
	char	   *relname;

	Assert(RelationIsAoRows(aorel) || RelationIsAoCols(aorel));

	relname = RelationGetRelationName(aorel);
	ereport(elevel,
			(errmsg("vacuuming \"%s.%s\"",
					get_namespace_name(RelationGetNamespace(aorel)),
					relname)));

	if (Gp_role == GP_ROLE_DISPATCH)
	{
		return;
	}

	if (vacstmt->appendonly_phase == AOVAC_DROP)
	{
		Assert(!vacstmt->appendonly_compaction_insert_segno);

		elogif(Debug_appendonly_print_compaction, LOG,
			"Vacuum drop phase %s", RelationGetRelationName(aorel));

		if (RelationIsAoRows(aorel))
		{
			AppendOnlyDrop(aorel, vacstmt->appendonly_compaction_segno);
		}
		else
		{
			Assert(RelationIsAoCols(aorel));
			AOCSDrop(aorel, vacstmt->appendonly_compaction_segno);
		}
	}
	else
	{
		Assert(vacstmt->appendonly_phase == AOVAC_COMPACT);
		Assert(list_length(vacstmt->appendonly_compaction_insert_segno) == 1);

		int insert_segno = linitial_int(vacstmt->appendonly_compaction_insert_segno);

		if (insert_segno == APPENDONLY_COMPACTION_SEGNO_INVALID)
		{
			elogif(Debug_appendonly_print_compaction, LOG,
			"Vacuum pseudo-compaction phase %s", RelationGetRelationName(aorel));
		}
		else
		{
			elogif(Debug_appendonly_print_compaction, LOG,
				"Vacuum compaction phase %s", RelationGetRelationName(aorel));
			if (RelationIsAoRows(aorel))
			{
				AppendOnlyCompact(aorel,
								  vacstmt->appendonly_compaction_segno,
								  insert_segno, (vacstmt->options & VACOPT_FULL));
			}
			else
			{
				Assert(RelationIsAoCols(aorel));
				AOCSCompact(aorel,
							vacstmt->appendonly_compaction_segno,
							insert_segno, (vacstmt->options & VACOPT_FULL));
			}
		}
	}
}

/*
 * Rescan end pages to verify that they are (still) empty of tuples.
 *
 * Returns number of nondeletable pages (last nonempty page + 1).
 */
static BlockNumber
count_nondeletable_pages(Relation onerel, LVRelStats *vacrelstats)
{
	BlockNumber blkno;

	/* Strange coding of loop control is needed because blkno is unsigned */
	blkno = vacrelstats->rel_pages;
	while (blkno > vacrelstats->nonempty_pages)
	{
		Buffer		buf;
		Page		page;
		OffsetNumber offnum,
					maxoff;
		bool		hastup;

		/*
		 * We don't insert a vacuum delay point here, because we have an
		 * exclusive lock on the table which we want to hold for as short a
		 * time as possible.  We still need to check for interrupts however.
		 */
		CHECK_FOR_INTERRUPTS();

		blkno--;

		buf = ReadBufferExtended(onerel, MAIN_FORKNUM, blkno,
								 RBM_NORMAL, vac_strategy);

		/* In this phase we only need shared access to the buffer */
		LockBuffer(buf, BUFFER_LOCK_SHARE);

		page = BufferGetPage(buf);

		if (PageIsNew(page) || PageIsEmpty(page))
		{
			/* PageIsNew probably shouldn't happen... */
			UnlockReleaseBuffer(buf);
			continue;
		}

		hastup = false;
		maxoff = PageGetMaxOffsetNumber(page);
		for (offnum = FirstOffsetNumber;
			 offnum <= maxoff;
			 offnum = OffsetNumberNext(offnum))
		{
			ItemId		itemid;

			itemid = PageGetItemId(page, offnum);

			/*
			 * Note: any non-unused item should be taken as a reason to keep
			 * this page.  We formerly thought that DEAD tuples could be
			 * thrown away, but that's not so, because we'd not have cleaned
			 * out their index entries.
			 */
			if (ItemIdIsUsed(itemid))
			{
				hastup = true;
				break;			/* can stop scanning */
			}
		}						/* scan along page */

		UnlockReleaseBuffer(buf);

		/* Done scanning if we found a tuple here */
		if (hastup)
			return blkno + 1;
	}

	/*
	 * If we fall out of the loop, all the previously-thought-to-be-empty
	 * pages still are; we need not bother to look at the last known-nonempty
	 * page.
	 */
	return vacrelstats->nonempty_pages;
}

/*
 * lazy_space_alloc - space allocation decisions for lazy vacuum
 *
 * See the comments at the head of this file for rationale.
 */
static void
lazy_space_alloc(LVRelStats *vacrelstats, BlockNumber relblocks)
{
	long		maxtuples;

	if (vacrelstats->hasindex)
	{
		maxtuples = (maintenance_work_mem * 1024L) / sizeof(ItemPointerData);
		maxtuples = Min(maxtuples, INT_MAX);
		maxtuples = Min(maxtuples, MaxAllocSize / sizeof(ItemPointerData));

		/* curious coding here to ensure the multiplication can't overflow */
		if ((BlockNumber) (maxtuples / LAZY_ALLOC_TUPLES) > relblocks)
			maxtuples = relblocks * LAZY_ALLOC_TUPLES;

		/* stay sane if small maintenance_work_mem */
		maxtuples = Max(maxtuples, MaxHeapTuplesPerPage);
	}
	else
	{
		maxtuples = MaxHeapTuplesPerPage;
	}

	vacrelstats->num_dead_tuples = 0;
	vacrelstats->max_dead_tuples = (int) maxtuples;
	vacrelstats->dead_tuples = (ItemPointer)
		palloc(maxtuples * sizeof(ItemPointerData));
}

/*
 * lazy_record_dead_tuple - remember one deletable tuple
 */
static void
lazy_record_dead_tuple(LVRelStats *vacrelstats,
					   ItemPointer itemptr)
{
	/*
	 * The array shouldn't overflow under normal behavior, but perhaps it
	 * could if we are given a really small maintenance_work_mem. In that
	 * case, just forget the last few tuples (we'll get 'em next time).
	 */
	if (vacrelstats->num_dead_tuples < vacrelstats->max_dead_tuples)
	{
		vacrelstats->dead_tuples[vacrelstats->num_dead_tuples] = *itemptr;
		vacrelstats->num_dead_tuples++;
	}
}

/*
 *	lazy_tid_reaped() -- is a particular tid deletable?
 *
 *		This has the right signature to be an IndexBulkDeleteCallback.
 *
 *		Assumes dead_tuples array is in sorted order.
 */
static bool
lazy_tid_reaped(ItemPointer itemptr, void *state)
{
	LVRelStats *vacrelstats = (LVRelStats *) state;
	ItemPointer res;

	res = (ItemPointer) bsearch((void *) itemptr,
								(void *) vacrelstats->dead_tuples,
								vacrelstats->num_dead_tuples,
								sizeof(ItemPointerData),
								vac_cmp_itemptr);

	return (res != NULL);
}

/*
 * Comparator routines for use with qsort() and bsearch().
 */
static int
vac_cmp_itemptr(const void *left, const void *right)
{
	BlockNumber lblk,
				rblk;
	OffsetNumber loff,
				roff;

	lblk = ItemPointerGetBlockNumber((ItemPointer) left);
	rblk = ItemPointerGetBlockNumber((ItemPointer) right);

	if (lblk < rblk)
		return -1;
	if (lblk > rblk)
		return 1;

	loff = ItemPointerGetOffsetNumber((ItemPointer) left);
	roff = ItemPointerGetOffsetNumber((ItemPointer) right);

	if (loff < roff)
		return -1;
	if (loff > roff)
		return 1;

	return 0;
}
