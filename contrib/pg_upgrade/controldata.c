/*
 *	controldata.c
 *
 *	controldata functions
 *
 *	Copyright (c) 2010-2011, PostgreSQL Global Development Group
 *	contrib/pg_upgrade/controldata.c
 */

#include "pg_upgrade.h"

#include <ctype.h>

<<<<<<< HEAD
static void putenv2(migratorContext *ctx, const char *var, const char *val);

=======
>>>>>>> a4bebdd92624e018108c2610fc3f2c1584b6c687
/*
 * get_control_data()
 *
 * gets pg_control information in "ctrl". Assumes that bindir and
 * datadir are valid absolute paths to postgresql bin and pgdata
 * directories respectively *and* pg_resetxlog is version compatible
 * with datadir. The main purpose of this function is to get pg_control
 * data in a version independent manner.
 *
 * The approach taken here is to invoke pg_resetxlog with -n option
 * and then pipe its output. With little string parsing we get the
 * pg_control data.  pg_resetxlog cannot be run while the server is running
 * so we use pg_controldata;  pg_controldata doesn't provide all the fields
<<<<<<< HEAD
 * we need to actually perform the migration, but it provides enough for
 * check mode.  We do not implement pg_resetxlog -n because it is hard to
=======
 * we need to actually perform the upgrade, but it provides enough for
 * check mode.	We do not implement pg_resetxlog -n because it is hard to
>>>>>>> a4bebdd92624e018108c2610fc3f2c1584b6c687
 * return valid xid data for a running server.
 */
void
get_control_data(ClusterInfo *cluster, bool live_check)
{
	char		cmd[MAXPGPATH];
	char		bufin[MAX_STRING];
	FILE	   *output;
	char	   *p;
	bool		got_xid = false;
	bool		got_oid = false;
	bool		got_log_id = false;
	bool		got_log_seg = false;
	bool		got_tli = false;
	bool		got_align = false;
	bool		got_blocksz = false;
	bool		got_largesz = false;
	bool		got_walsz = false;
	bool		got_walseg = false;
	bool		got_ident = false;
	bool		got_index = false;
	bool		got_toast = false;
	bool		got_date_is_int = false;
	bool		got_float8_pass_by_value = false;
<<<<<<< HEAD
	bool		got_data_checksums = false;
=======
>>>>>>> a4bebdd92624e018108c2610fc3f2c1584b6c687
	char	   *lc_collate = NULL;
	char	   *lc_ctype = NULL;
	char	   *lc_monetary = NULL;
	char	   *lc_numeric = NULL;
	char	   *lc_time = NULL;
	char	   *lang = NULL;
	char	   *language = NULL;
	char	   *lc_all = NULL;
	char	   *lc_messages = NULL;

	/*
	 * Because we test the pg_resetxlog output as strings, it has to be in
	 * English.  Copied from pg_regress.c.
	 */
	if (getenv("LC_COLLATE"))
<<<<<<< HEAD
		lc_collate = pg_strdup(ctx, getenv("LC_COLLATE"));
	if (getenv("LC_CTYPE"))
		lc_ctype = pg_strdup(ctx, getenv("LC_CTYPE"));
	if (getenv("LC_MONETARY"))
		lc_monetary = pg_strdup(ctx, getenv("LC_MONETARY"));
	if (getenv("LC_NUMERIC"))
		lc_numeric = pg_strdup(ctx, getenv("LC_NUMERIC"));
	if (getenv("LC_TIME"))
		lc_time = pg_strdup(ctx, getenv("LC_TIME"));
	if (getenv("LANG"))
		lang = pg_strdup(ctx, getenv("LANG"));
	if (getenv("LANGUAGE"))
		language = pg_strdup(ctx, getenv("LANGUAGE"));
	if (getenv("LC_ALL"))
		lc_all = pg_strdup(ctx, getenv("LC_ALL"));
	if (getenv("LC_MESSAGES"))
		lc_messages = pg_strdup(ctx, getenv("LC_MESSAGES"));

	putenv2(ctx, "LC_COLLATE", NULL);
	putenv2(ctx, "LC_CTYPE", NULL);
	putenv2(ctx, "LC_MONETARY", NULL);
	putenv2(ctx, "LC_NUMERIC", NULL);
	putenv2(ctx, "LC_TIME", NULL);
	putenv2(ctx, "LANG",
#ifndef WIN32
			NULL);
#else
			/* On Windows the default locale cannot be English, so force it */
			"en");
#endif
	putenv2(ctx, "LANGUAGE", NULL);
	putenv2(ctx, "LC_ALL", NULL);
	putenv2(ctx, "LC_MESSAGES", "C");
=======
		lc_collate = pg_strdup(getenv("LC_COLLATE"));
	if (getenv("LC_CTYPE"))
		lc_ctype = pg_strdup(getenv("LC_CTYPE"));
	if (getenv("LC_MONETARY"))
		lc_monetary = pg_strdup(getenv("LC_MONETARY"));
	if (getenv("LC_NUMERIC"))
		lc_numeric = pg_strdup(getenv("LC_NUMERIC"));
	if (getenv("LC_TIME"))
		lc_time = pg_strdup(getenv("LC_TIME"));
	if (getenv("LANG"))
		lang = pg_strdup(getenv("LANG"));
	if (getenv("LANGUAGE"))
		language = pg_strdup(getenv("LANGUAGE"));
	if (getenv("LC_ALL"))
		lc_all = pg_strdup(getenv("LC_ALL"));
	if (getenv("LC_MESSAGES"))
		lc_messages = pg_strdup(getenv("LC_MESSAGES"));

	pg_putenv("LC_COLLATE", NULL);
	pg_putenv("LC_CTYPE", NULL);
	pg_putenv("LC_MONETARY", NULL);
	pg_putenv("LC_NUMERIC", NULL);
	pg_putenv("LC_TIME", NULL);
	pg_putenv("LANG",
#ifndef WIN32
			  NULL);
#else
	/* On Windows the default locale cannot be English, so force it */
			  "en");
#endif
	pg_putenv("LANGUAGE", NULL);
	pg_putenv("LC_ALL", NULL);
	pg_putenv("LC_MESSAGES", "C");
>>>>>>> a4bebdd92624e018108c2610fc3f2c1584b6c687

	snprintf(cmd, sizeof(cmd), SYSTEMQUOTE "\"%s/%s \"%s\"" SYSTEMQUOTE,
			 cluster->bindir,
			 live_check ? "pg_controldata\"" : "pg_resetxlog\" -n",
			 cluster->pgdata);
	fflush(stdout);
	fflush(stderr);

	if ((output = popen(cmd, "r")) == NULL)
		pg_log(PG_FATAL, "Could not get control data: %s\n",
			   getErrorText(errno));

	/* Only pre-8.4 has these so if they are not set below we will check later */
	cluster->controldata.lc_collate = NULL;
	cluster->controldata.lc_ctype = NULL;

	/* Only in <= 8.3 */
	if (GET_MAJOR_VERSION(cluster->major_version) <= 803)
	{
		cluster->controldata.float8_pass_by_value = false;
		got_float8_pass_by_value = true;
	}

	/*
	 * In PostgreSQL, checksums were introduced in 9.3 so the test for checksum
	 * version applies to <= 9.2. Greenplum backported checksums into 5.x which
	 * is based on PostgreSQL 8.3 so this test need to go on <= 8.3 instead.
	 */
	if (GET_MAJOR_VERSION(cluster->major_version) <= 803)
	{
		cluster->controldata.data_checksum_version = false;
		got_data_checksums = true;
	}

	/* we have the result of cmd in "output". so parse it line by line now */
	while (fgets(bufin, sizeof(bufin), output))
	{
		if (log_opts.debug)
			fputs(bufin, log_opts.debug_fd);

#ifdef WIN32

		/*
		 * Due to an installer bug, LANG=C doesn't work for PG 8.3.3, but does
		 * work 8.2.6 and 8.3.7, so check for non-ASCII output and suggest a
		 * minor upgrade.
		 */
		if (GET_MAJOR_VERSION(cluster->major_version) <= 803)
		{
			for (p = bufin; *p; p++)
				if (!isascii(*p))
					pg_log(PG_FATAL,
						   "The 8.3 cluster's pg_controldata is incapable of outputting ASCII, even\n"
						   "with LANG=C.  You must upgrade this cluster to a newer version of Postgres\n"
						   "8.3 to fix this bug.  Postgres 8.3.7 and later are known to work properly.\n");
		}
#endif

		if ((p = strstr(bufin, "pg_control version number:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: pg_resetxlog problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.ctrl_ver = str2uint(p);
		}
		else if ((p = strstr(bufin, "Catalog version number:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.cat_ver = str2uint(p);
		}
		else if ((p = strstr(bufin, "First log file ID after reset:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.logid = str2uint(p);
			got_log_id = true;
		}
		else if ((p = strstr(bufin, "First log file segment after reset:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.nxtlogseg = str2uint(p);
			got_log_seg = true;
		}
		/* GPDB 4.3 (and PostgreSQL 8.2) wording of the above two. */
		else if ((p = strstr(bufin, "Current log file ID:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(ctx, PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.logid = str2uint(p);
			got_log_id = true;
		}
		else if ((p = strstr(bufin, "Next log file segment:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(ctx, PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.nxtlogseg = str2uint(p);
			got_log_seg = true;
		}
		/*---*/
		else if ((p = strstr(bufin, "Latest checkpoint's TimeLineID:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.chkpnt_tli = str2uint(p);
			got_tli = true;
		}
		else if ((p = strstr(bufin, "Latest checkpoint's NextXID:")) != NULL)
		{
			char	   *op = strchr(p, '/');

			if (op == NULL)
				op = strchr(p, ':');

			if (op == NULL || strlen(op) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			op++;				/* removing ':' char */
			cluster->controldata.chkpnt_nxtxid = str2uint(op);
			got_xid = true;
		}
		else if ((p = strstr(bufin, "Latest checkpoint's NextOID:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.chkpnt_nxtoid = str2uint(p);
			got_oid = true;
		}
		else if ((p = strstr(bufin, "Maximum data alignment:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.align = str2uint(p);
			got_align = true;
		}
		else if ((p = strstr(bufin, "Database block size:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.blocksz = str2uint(p);
			got_blocksz = true;
		}
		else if ((p = strstr(bufin, "Blocks per segment of large relation:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.largesz = str2uint(p);
			got_largesz = true;
		}
		else if ((p = strstr(bufin, "WAL block size:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.walsz = str2uint(p);
			got_walsz = true;
		}
		else if ((p = strstr(bufin, "Bytes per WAL segment:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.walseg = str2uint(p);
			got_walseg = true;
		}
		else if ((p = strstr(bufin, "Maximum length of identifiers:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.ident = str2uint(p);
			got_ident = true;
		}
		else if ((p = strstr(bufin, "Maximum columns in an index:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.index = str2uint(p);
			got_index = true;
		}
		else if ((p = strstr(bufin, "Maximum size of a TOAST chunk:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.toast = str2uint(p);
			got_toast = true;
		}
		else if ((p = strstr(bufin, "Date/time type storage:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			cluster->controldata.date_is_int = strstr(p, "64-bit integers") != NULL;
			got_date_is_int = true;
		}
		else if ((p = strstr(bufin, "Float8 argument passing:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			/* used later for contrib check */
			cluster->controldata.float8_pass_by_value = strstr(p, "by value") != NULL;
			got_float8_pass_by_value = true;
		}
		else if ((p = strstr(bufin, "checksum")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(ctx, PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			/* used later for contrib check */
			cluster->controldata.data_checksum_version = str2uint(p);
			got_data_checksums = true;
		}
		/* In pre-8.4 only */
		else if ((p = strstr(bufin, "LC_COLLATE:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			/* skip leading spaces and remove trailing newline */
			p += strspn(p, " ");
			if (strlen(p) > 0 && *(p + strlen(p) - 1) == '\n')
				*(p + strlen(p) - 1) = '\0';
			cluster->controldata.lc_collate = pg_strdup(p);
		}
		/* In pre-8.4 only */
		else if ((p = strstr(bufin, "LC_CTYPE:")) != NULL)
		{
			p = strchr(p, ':');

			if (p == NULL || strlen(p) <= 1)
				pg_log(PG_FATAL, "%d: controldata retrieval problem\n", __LINE__);

			p++;				/* removing ':' char */
			/* skip leading spaces and remove trailing newline */
			p += strspn(p, " ");
			if (strlen(p) > 0 && *(p + strlen(p) - 1) == '\n')
				*(p + strlen(p) - 1) = '\0';
			cluster->controldata.lc_ctype = pg_strdup(p);
		}
	}

	if (output)
		pclose(output);

	/*
<<<<<<< HEAD
	 *	Restore environment variables
	 */
	putenv2(ctx, "LC_COLLATE", lc_collate);
	putenv2(ctx, "LC_CTYPE", lc_ctype);
	putenv2(ctx, "LC_MONETARY", lc_monetary);
	putenv2(ctx, "LC_NUMERIC", lc_numeric);
	putenv2(ctx, "LC_TIME", lc_time);
	putenv2(ctx, "LANG", lang);
	putenv2(ctx, "LANGUAGE", language);
	putenv2(ctx, "LC_ALL", lc_all);
	putenv2(ctx, "LC_MESSAGES", lc_messages);
=======
	 * Restore environment variables
	 */
	pg_putenv("LC_COLLATE", lc_collate);
	pg_putenv("LC_CTYPE", lc_ctype);
	pg_putenv("LC_MONETARY", lc_monetary);
	pg_putenv("LC_NUMERIC", lc_numeric);
	pg_putenv("LC_TIME", lc_time);
	pg_putenv("LANG", lang);
	pg_putenv("LANGUAGE", language);
	pg_putenv("LC_ALL", lc_all);
	pg_putenv("LC_MESSAGES", lc_messages);

	pg_free(lc_collate);
	pg_free(lc_ctype);
	pg_free(lc_monetary);
	pg_free(lc_numeric);
	pg_free(lc_time);
	pg_free(lang);
	pg_free(language);
	pg_free(lc_all);
	pg_free(lc_messages);
>>>>>>> a4bebdd92624e018108c2610fc3f2c1584b6c687

	pg_free(lc_collate);
	pg_free(lc_ctype);
	pg_free(lc_monetary);
	pg_free(lc_numeric);
	pg_free(lc_time);
	pg_free(lang);
	pg_free(language);
	pg_free(lc_all);
	pg_free(lc_messages);
 
	/* verify that we got all the mandatory pg_control data */
	if (!got_xid || !got_oid ||
		(!live_check && !got_log_id) ||
		(!live_check && !got_log_seg) ||
		!got_tli ||
		!got_align || !got_blocksz || !got_largesz || !got_walsz ||
		!got_walseg || !got_ident || !got_index || /* !got_toast || */
		!got_date_is_int || !got_float8_pass_by_value || !got_data_checksums)
	{
		pg_log(PG_REPORT,
			"Some required control information is missing;  cannot find:\n");

		if (!got_xid)
			pg_log(PG_REPORT, "  checkpoint next XID\n");

		if (!got_oid)
			pg_log(PG_REPORT, "  latest checkpoint next OID\n");

		if (!live_check && !got_log_id)
			pg_log(PG_REPORT, "  first log file ID after reset\n");

		if (!live_check && !got_log_seg)
			pg_log(PG_REPORT, "  first log file segment after reset\n");

		if (!got_tli)
			pg_log(PG_REPORT, "  latest checkpoint timeline ID\n");

		if (!got_align)
			pg_log(PG_REPORT, "  maximum alignment\n");

		if (!got_blocksz)
			pg_log(PG_REPORT, "  block size\n");

		if (!got_largesz)
			pg_log(PG_REPORT, "  large relation segment size\n");

		if (!got_walsz)
			pg_log(PG_REPORT, "  WAL block size\n");

		if (!got_walseg)
			pg_log(PG_REPORT, "  WAL segment size\n");

		if (!got_ident)
			pg_log(PG_REPORT, "  maximum identifier length\n");

		if (!got_index)
			pg_log(PG_REPORT, "  maximum number of indexed columns\n");

#if 0	/* not mandatory in GPDB, see above */
		if (!got_toast)
<<<<<<< HEAD
			pg_log(ctx, PG_REPORT, "  maximum TOAST chunk size\n");
#endif
=======
			pg_log(PG_REPORT, "  maximum TOAST chunk size\n");
>>>>>>> a4bebdd92624e018108c2610fc3f2c1584b6c687

		if (!got_date_is_int)
			pg_log(PG_REPORT, "  dates/times are integers?\n");

		/* value added in Postgres 8.4 */
		if (!got_float8_pass_by_value)
			pg_log(PG_REPORT, "  float8 argument passing method\n");

<<<<<<< HEAD
		/* value added in Postgres 9.3 */
		if (!got_data_checksums)
			pg_log(ctx, PG_REPORT, "  data checksums\n");

		pg_log(ctx, PG_FATAL,
			   "Cannot continue without required control information, terminating\n");
=======
		pg_log(PG_FATAL,
			   "Unable to continue without required control information, terminating\n");
>>>>>>> a4bebdd92624e018108c2610fc3f2c1584b6c687
	}
}


/*
 * check_control_data()
 *
 * check to make sure the control data settings are compatible
 */
void
check_control_data(ControlData *oldctrl,
				   ControlData *newctrl)
{
	if (oldctrl->align == 0 || oldctrl->align != newctrl->align)
		pg_log(PG_FATAL,
			   "old and new pg_controldata alignments are invalid or do not match\n");

	if (oldctrl->blocksz == 0 || oldctrl->blocksz != newctrl->blocksz)
		pg_log(PG_FATAL,
			   "old and new pg_controldata block sizes are invalid or do not match\n");

	if (oldctrl->largesz == 0 || oldctrl->largesz != newctrl->largesz)
		pg_log(PG_FATAL,
			   "old and new pg_controldata maximum relation segement sizes are invalid or do not match\n");

	if (oldctrl->walsz == 0 || oldctrl->walsz != newctrl->walsz)
		pg_log(PG_FATAL,
			   "old and new pg_controldata WAL block sizes are invalid or do not match\n");

	if (oldctrl->walseg == 0 || oldctrl->walseg != newctrl->walseg)
		pg_log(PG_FATAL,
			   "old and new pg_controldata WAL segment sizes are invalid or do not match\n");

	if (oldctrl->ident == 0 || oldctrl->ident != newctrl->ident)
		pg_log(PG_FATAL,
			   "old and new pg_controldata maximum identifier lengths are invalid or do not match\n");

	if (oldctrl->index == 0 || oldctrl->index != newctrl->index)
		pg_log(PG_FATAL,
			   "old and new pg_controldata maximum indexed columns are invalid or do not match\n");

	/*
	 * PostgreSQL's pg_upgrade checks for the maximum TOAST chunk size, because
	 * the tuptoaster code assumes all chunks to have the same size. GPDB's
	 * tuptoaster code has been modified to work with any chunk size, to support
	 * upgrading from GPDB 4.3 to 5.0, because the chunk size was changed between
	 * those releases (that is, between PostgreSQL 8.2 and 8.3). Hence,
	 * 'got_toast' is not mandatory in GPDB.
	 */
	if (oldctrl->toast == 0 || oldctrl->toast != newctrl->toast)
<<<<<<< HEAD
		pg_log(ctx, PG_WARNING,
=======
		pg_log(PG_FATAL,
>>>>>>> a4bebdd92624e018108c2610fc3f2c1584b6c687
			   "old and new pg_controldata maximum TOAST chunk sizes are invalid or do not match\n");

	if (oldctrl->date_is_int != newctrl->date_is_int)
	{
		pg_log(PG_WARNING,
			   "\nOld and new pg_controldata date/time storage types do not match.\n");

		/*
		 * This is a common 8.3 -> 8.4 upgrade problem, so we are more verbose
		 */
		pg_log(PG_FATAL,
			   "You will need to rebuild the new server with configure\n"
			   "--disable-integer-datetimes or get server binaries built\n"
			   "with those options.\n");
	}

	/*
	 * Check for allowed combinations of data checksums
	 */
	if (oldctrl->data_checksum_version == 0 &&
		newctrl->data_checksum_version != 0 &&
		ctx->checksum_mode != CHECKSUM_ADD)
		pg_log(ctx, PG_FATAL, "old cluster does not use data checksums but the new one does\n");
	else if (oldctrl->data_checksum_version != 0 &&
			 newctrl->data_checksum_version == 0 &&
			 ctx->checksum_mode != CHECKSUM_REMOVE)
		pg_log(ctx, PG_FATAL, "old cluster uses data checksums but the new one does not\n");
	else if (oldctrl->data_checksum_version == newctrl->data_checksum_version &&
			 ctx->checksum_mode != CHECKSUM_NONE)
		pg_log(ctx, PG_FATAL, "old and new cluster data checksum configuration match, cannot %s data checksums\n",
				 (ctx->checksum_mode == CHECKSUM_ADD ? "add" : "remove"));
	else if (oldctrl->data_checksum_version != 0 && ctx->checksum_mode == CHECKSUM_ADD)
		pg_log(ctx, PG_FATAL, "--add-checksum option not supported for old cluster which uses data checksums\n");
	else if (oldctrl->data_checksum_version != newctrl->data_checksum_version
			 && ctx->checksum_mode == CHECKSUM_NONE)
		pg_log(ctx, PG_FATAL, "old and new cluster pg_controldata checksum versions do not match\n");
}


void
rename_old_pg_control(void)
{
	char		old_path[MAXPGPATH],
				new_path[MAXPGPATH];

	prep_status("Adding \".old\" suffix to old global/pg_control");

	snprintf(old_path, sizeof(old_path), "%s/global/pg_control", old_cluster.pgdata);
	snprintf(new_path, sizeof(new_path), "%s/global/pg_control.old", old_cluster.pgdata);
	if (pg_mv_file(old_path, new_path) != 0)
		pg_log(PG_FATAL, "Unable to rename %s to %s.\n", old_path, new_path);
	check_ok();
}


/*
 *	putenv2()
 *
 *	This is like putenv(), but takes two arguments.
 *	It also does unsetenv() if val is NULL.
 */
static void
putenv2(migratorContext *ctx, const char *var, const char *val)
{
	if (val)
	{
#ifndef WIN32
		char	   *envstr = (char *) pg_malloc(ctx, strlen(var) +
												strlen(val) + 2);

		sprintf(envstr, "%s=%s", var, val);
		putenv(envstr);
		/*
		 *	Do not free envstr because it becomes part of the environment
		 *	on some operating systems.  See port/unsetenv.c::unsetenv.
		 */
#else
		SetEnvironmentVariableA(var, val);
#endif
	}
	else
	{
#ifndef WIN32
		unsetenv(var);
#else
		SetEnvironmentVariableA(var, "");
#endif
	}
}
