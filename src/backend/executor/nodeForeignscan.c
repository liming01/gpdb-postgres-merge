/*-------------------------------------------------------------------------
 *
 * nodeForeignscan.c
 *	  Routines to support scans of foreign tables
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/nodeForeignscan.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * INTERFACE ROUTINES
 *
 *		ExecForeignScan			scans a foreign table.
 *		ExecInitForeignScan		creates and initializes state info.
 *		ExecReScanForeignScan	rescans the foreign relation.
 *		ExecEndForeignScan		releases any resources allocated.
 */
#include "postgres.h"

#include "executor/executor.h"
#include "executor/nodeForeignscan.h"
#include "foreign/fdwapi.h"
#include "utils/rel.h"

#include "utils/guc.h"
#include "cdb/cdbvars.h"        //for GpIdentity
#include "cdb/cdbgang.h"        //for CdbProcess 
#include "executor/execdesc.h"  //for Slice
#include "executor/execUtils.h" //for getCurrentSlice()

static TupleTableSlot *ForeignNext(ForeignScanState *node);
static bool ForeignRecheck(ForeignScanState *node, TupleTableSlot *slot);


/* ----------------------------------------------------------------
 *		ForeignNext
 *
 *		This is a workhorse for ExecForeignScan
 * ----------------------------------------------------------------
 */
static TupleTableSlot *
ForeignNext(ForeignScanState *node)
{
	TupleTableSlot *slot = NULL;
	ForeignScan *plan = (ForeignScan *) node->ss.ps.plan;
	ExprContext *econtext = node->ss.ps.ps_ExprContext;
	MemoryContext oldcontext;

	/* Call the Iterate function in short-lived context */
	oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);
	if (GpIdentity.segindex==0 && Gp_role == GP_ROLE_EXECUTE)
	{
		slot = node->fdwroutine->IterateForeignScan(node);
	}

	// ??????????????????
	if (Gp_role == GP_ROLE_EXECUTE){ //on all segments, need motion node
		//for fdw motion child node
		Plan *fdwMotionNode = outerPlanState(node);
		if(fdwMotionNode)
			slot = ExecProcNode(fdwMotionNode);
	}

	MemoryContextSwitchTo(oldcontext);

	/*
	 * If any system columns are requested, we have to force the tuple into
	 * physical-tuple form to avoid "cannot extract system attribute from
	 * virtual tuple" errors later.  We also insert a valid value for
	 * tableoid, which is the only actually-useful system column.
	 */
	if (plan->fsSystemCol && !TupIsNull(slot))
	{
		(void) ExecMaterializeSlot(slot);

		//tup->t_tableOid = RelationGetRelid(node->ss.ss_currentRelation);
	}

	return slot;
}

/*
 * ForeignRecheck -- access method routine to recheck a tuple in EvalPlanQual
 */
static bool
ForeignRecheck(ForeignScanState *node, TupleTableSlot *slot)
{
	/* There are no access-method-specific conditions to recheck. */
	return true;
}

/* ----------------------------------------------------------------
 *		ExecForeignScan(node)
 *
 *		Fetches the next tuple from the FDW, checks local quals, and
 *		returns it.
 *		We call the ExecScan() routine and pass it the appropriate
 *		access method functions.
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecForeignScan(ForeignScanState *node)
{
	return ExecScan((ScanState *) node,
					(ExecScanAccessMtd) ForeignNext,
					(ExecScanRecheckMtd) ForeignRecheck);
}


/* ----------------------------------------------------------------
 *		ExecInitForeignScan
 * ----------------------------------------------------------------
 */
ForeignScanState *
ExecInitForeignScan(ForeignScan *node, EState *estate, int eflags)
{
	ForeignScanState *scanstate;
	Relation	currentRelation;
	FdwRoutine *fdwroutine;

	/* check for unsupported flags */
	Assert(!(eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK)));

	/*
	 * create state structure
	 */
	scanstate = makeNode(ForeignScanState);
	scanstate->ss.ps.plan = (Plan *) node;
	scanstate->ss.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &scanstate->ss.ps);

	//scanstate->ss.ps.ps_TupFromTlist = false;

	/*
	 * initialize child expressions
	 */
	scanstate->ss.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->scan.plan.targetlist,
					 (PlanState *) scanstate);
	scanstate->ss.ps.qual = (List *)
		ExecInitExpr((Expr *) node->scan.plan.qual,
					 (PlanState *) scanstate);

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &scanstate->ss.ps);
	ExecInitScanTupleSlot(estate, &scanstate->ss);

	/*
	 * open the base relation and acquire appropriate lock on it.
	 */
	currentRelation = ExecOpenScanRelation(estate, node->scan.scanrelid);
	scanstate->ss.ss_currentRelation = currentRelation;

	/*
	 * get the scan type from the relation descriptor.
	 */
	ExecAssignScanType(&scanstate->ss, RelationGetDescr(currentRelation));

	/*
	 * Initialize result tuple type and projection info.
	 */
	ExecAssignResultTypeFromTL(&scanstate->ss.ps);
	ExecAssignScanProjectionInfo(&scanstate->ss);

	/*
	 * Acquire function pointers from the FDW's handler, and init fdw_state.
	 */
	fdwroutine = GetFdwRoutineByRelId(RelationGetRelid(currentRelation));
	scanstate->fdwroutine = fdwroutine;
	scanstate->fdw_state = NULL;

	if (GpIdentity.segindex==0 && Gp_role == GP_ROLE_EXECUTE){ // only send remote query at seg0
		
		// get motion receiver info (hostip, port) of this gang in this slice
		Slice *currentSlice = getCurrentSlice(estate, LocallyExecutingSliceIndex(estate));

		int i=0;
		ListCell   *lc = NULL;
		foreach(lc, currentSlice->primaryProcesses)
		{
			CdbProcess *cdbProc = (CdbProcess *) lfirst(lc);

			if (cdbProc)
			{
				// get info: cdbProc->listenerAddr and cdbProc->listenerPort
				switch(i++){
				case 0:
					gp_fdw_motion_recv_port1 = cdbProc->listenerPort;
					break;
				case 1:
					gp_fdw_motion_recv_port2 = cdbProc->listenerPort;
					break;
				case 2:
					gp_fdw_motion_recv_port3 = cdbProc->listenerPort;
					break;
				}
			}
		}

		/*
		 * Tell the FDW to initiate the scan.
		 */
		fdwroutine->BeginForeignScan(scanstate, eflags);
	}

//	 if (Gp_role == GP_ROLE_EXECUTE){ //on all segments, need motion node
	 	//for fdw motion child node
	 	Plan *fdwMotionNode = outerPlan(node);
	 	if(fdwMotionNode)
	 		outerPlanState(scanstate) = ExecInitNode(fdwMotionNode, estate, eflags);
//	 }

	return scanstate;
}

/* ----------------------------------------------------------------
 *		ExecEndForeignScan
 *
 *		frees any storage allocated through C routines.
 * ----------------------------------------------------------------
 */
void
ExecEndForeignScan(ForeignScanState *node)
{
	ExecEndNode(outerPlanState(node));
	if (Gp_role == GP_ROLE_EXECUTE){ //on all segments, need motion node
		//for fdw motion child node
		Plan *fdwMotionNode = outerPlan(node);
		if(fdwMotionNode)
			ExecEndNode(fdwMotionNode);
	}

	/* Let the FDW shut down */
	if (GpIdentity.segindex==0 && Gp_role == GP_ROLE_EXECUTE){
		node->fdwroutine->EndForeignScan(node);
	}

	/* Free the exprcontext */
	ExecFreeExprContext(&node->ss.ps);

	/* clean out the tuple table */
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->ss.ss_ScanTupleSlot);

	/* close the relation. */
	ExecCloseScanRelation(node->ss.ss_currentRelation);
}

/* ----------------------------------------------------------------
 *		ExecReScanForeignScan
 *
 *		Rescans the relation.
 * ----------------------------------------------------------------
 */
void
ExecReScanForeignScan(ForeignScanState *node)
{
	node->fdwroutine->ReScanForeignScan(node);

	ExecScanReScan(&node->ss);
}
