/* -*- mode: C; tab-width: 2; indent-tabs-mode: nil; -*- */

/*
 * Copyright (c) 2015-2016 Cray Inc.  All rights reserved.
 *
 * This software is available to you under a choice of one of two
 * licenses.  You may choose to be licensed under the terms of the GNU
 * General Public License (GPL) Version 2, available from the file
 * COPYING in the main directory of this source tree, or the
 * BSD license below:
 *
 *     Redistribution and use in source and binary forms, with or
 *     without modification, are permitted provided that the following
 *     conditions are met:
 *
 *      - Redistributions of source code must retain the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer.
 *
 *      - Redistributions in binary form must reproduce the above
 *        copyright notice, this list of conditions and the following
 *        disclaimer in the documentation and/or other materials
 *        provided with the distribution.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AWV
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#include <config.h>

#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <assert.h>
#include <time.h>
#include <sys/time.h>
#include <string.h>
#include <stdint.h>

#include <rdma/fabric.h>
#include <rdma/fi_domain.h>
#include <rdma/fi_errno.h>
#include <rdma/fi_endpoint.h>
#include <rdma/fi_cm.h>
#include <rdma/fi_rma.h>
#include <rdma/fi_tagged.h>
#include <rdma/fi_atomic.h>
#include <rdma/fi_ext_gni.h>

#include "ct_utils.h"
#include "rdmacred.h"

#define PRINT(stream, fmt, args...) \
	do { \
		fprintf(stream, fmt, ##args); \
		fflush(stream); \
	} while (0)

#define VERBOSE(fmt, args...) \
	do { \
		if (tunables.verbose) { \
			PRINT(stdout, "rank %d: " fmt, rank, ##args); \
		} \
	} while (0)

#define ERROR(fmt, args...) PRINT(stderr, "[ERROR] rank %d: " fmt, ##args)
#define DEBUG(fmt, args...) \
	do { \
		if (tunables.debug) { \
			PRINT(stderr, "[DEBUG %s:%d rank_%d] " fmt, \
				__FILE__, __LINE__, rank, ##args); \
			fflush(stderr); \
		} \
	} while (0)

#define GNIX_EP_RDM_PRIMARY_CAPS                                               \
	(FI_MSG | FI_RMA | FI_TAGGED | FI_ATOMICS |                            \
	 FI_DIRECTED_RECV | FI_READ |                                          \
	 FI_WRITE | FI_SEND | FI_RECV | FI_REMOTE_READ | FI_REMOTE_WRITE)

/* Program-level defines */
#define MAX_ALIGNMENT 65536
#define MAX_MSG_SIZE (8*1024) /* Current GNI provider max send size */
#define MYBUFSIZE (MAX_MSG_SIZE + MAX_ALIGNMENT)

#define TEST_DESC "Libfabric Authorization Key Test"
#define HEADER "# " TEST_DESC " \n"
#ifndef FIELD_WIDTH
#   define FIELD_WIDTH 20
#endif
#ifndef FLOAT_PRECISION
#   define FLOAT_PRECISION 2
#endif

/* Random number generator */
#define POLY 0x0000000000000007UL
#define PERIOD 1317624576693539401L

/* Define 64-bit types and corresponding format strings
 * for printf() and constants
 */
#define FSTR64 "%ld"
#define FSTRU64 "%lu"
#define ZERO64B 0LL
#define HEAD_RANK (rank == 0)
#define UNLOCKED 0
#define LOCKED(rank) (rank + 1)
#define SCRATCH_SIZE 8

typedef enum _program_state {
	STATE_PROCESS_DATA = 0,
	STATE_PROCESS_CONNECTIONS,
	MAX_STATE,
} program_state_t;

/* global variables */
static struct fi_gni_auth_key auth_key;

/* Allocate main table (in global memory) */
static int rx_depth = 512;
static int thread_safe = 1; // default

static double start_time;

struct peer_data {
	void *r_table_addr;
	uint64_t r_table_key;
};

struct peer {
	struct fid_ep *ep;
	struct fid_cq *scq;
	struct fid_cq *rcq;
	struct peer_data remote_data;
};

typedef struct workspace {
	int type;
	int seconds;
	int last_completed_iteration;
	void *data[0];
} workspace_t;

typedef struct shared_data {
	size_t workspace_size;
	uint64_t lf_workspace_key;
	workspace_t workspace; /* must be last element */
} shared_data_t;

typedef struct application_data {
	shared_data_t *shared_data;
	struct fid_mr *l_data_mr;
} app_data_t;

typedef struct communicator {
	void *addrs;
	int addrlen;
	int num_ranks;
        fi_addr_t *fi_addrs;
        struct peer *peers;
} communicator_t;


typedef struct fabric {
	struct fi_info *hints;
	struct fi_info *info;
	struct fid_fabric *fab;
	struct fid_domain *dom;
	struct fid_av *av;
	app_data_t local_data;
} fabric_t;

static fabric_t prov;

int rank, num_ranks;

struct test_tunables {
	int credential_id;
	int seconds;
	int is_data_generator;
	char *server_address;
};

static struct test_tunables tunables = {0};

static double usec_time(void)
{
	struct timeval tp;
	gettimeofday(&tp, NULL);
	return tp.tv_sec + tp.tv_usec / (double)1.0e6;
}

static inline void exchange_registration_data(fabric_t *fabric)
{
	uint64_t *keys;
	void **addresses;
	uint64_t local_table_key, local_lock_key;
	int i;
	app_data_t *data = &fabric->data;
	struct peer *peers = fabric->peers;

	keys = calloc(num_ranks, sizeof(*keys));
	assert(keys);

	addresses = calloc(num_ranks, sizeof(*addresses));
	assert(addresses);

	local_table_key = fi_mr_key(data->l_table_mr);
	local_lock_key = fi_mr_key(data->l_lock_mr);

	DEBUG("Exchanging registration data\n");

	ctpm_Barrier();

	DEBUG("Allgather 1\n");
	/* first, table addr */
	ctpm_Allgather(&local_table_key, sizeof(local_table_key), keys);

	for (i = 0; i < num_ranks; i++)
		peers[i].data.r_table_key = keys[i];

	ctpm_Barrier();

	DEBUG("Allgather 2\n");
	ctpm_Allgather(&local_lock_key, sizeof(local_lock_key), keys);

	for (i = 0; i < num_ranks; i++)
		peers[i].data.r_lock_key = keys[i];

	ctpm_Barrier();

	DEBUG("Allgather 3\n");

	DEBUG("Sending table %p, size=%d, dest=%p\n", hpcc_table, sizeof(void *),
			addresses);
	ctpm_Allgather(&hpcc_table, sizeof(void *), addresses);
	ctpm_Barrier();

	for (i = 0; i < num_ranks; i++)
		peers[i].data.r_table_addr = addresses[i];

	ctpm_Barrier();

	DEBUG("Allgather 4\n");DEBUG("Sending lock %p, size=%d, dest=%p\n",
			hpcc_lock, sizeof(void *), addresses);
	ctpm_Allgather(&hpcc_lock, sizeof(void *), addresses);

	for (i = 0; i < num_ranks; i++)
		peers[i].data.r_lock_addr = addresses[i];

	ctpm_Barrier();
	DEBUG("Finished exchanging data\n");
}

/* function declarations */
CT_ALLREDUCE_FUNC(int_sum, int, +);
CT_ALLREDUCE_FUNC(int64_sum, int64_t, +);

static inline void cq_readerr(struct fid_cq *cq, const char *cq_str)
{
	struct fi_cq_err_entry cq_err;
	const char *err_str;
	int ret;

	ret = fi_cq_readerr(cq, &cq_err, 0);
	if (unlikely(ret < 0)) {
		ct_print_fi_error("fi_cq_readerr", ret);
		return;
	}

	err_str = fi_cq_strerror(cq, cq_err.prov_errno, cq_err.err_data, NULL, 0);
	ERROR("%s: %d %s\n", cq_str, cq_err.err, fi_strerror(cq_err.err));
	ERROR("%s: prov_err: %s (%d)\n", cq_str, err_str, cq_err.prov_errno);
}

/*
 * fi_cq_err_entry can be cast to any CQ entry format.
 */
static inline int wait_for_comp(struct fid_cq *cq, int num_completions)
{
	struct fi_cq_err_entry comp;
	int ret;

	while (num_completions > 0) {
		ret = fi_cq_read(cq, &comp, 1);
		if (ret > 0) {
			num_completions--;
		} else if (unlikely(ret < 0 && ret != -FI_EAGAIN)) {
			if (ret == -FI_EAVAIL) {
				cq_readerr(cq, "cq");
			} else {
				ct_print_fi_error("fi_cq_read", ret);
			}
			return ret;
		}
	}
	return 0;
}

static inline void lf_atomic_xor(void *addr, uint64_t val, int remote_rank)
{
	ssize_t rc;
	struct peer *p = &prov.peers[remote_rank];
	struct fid_ep *ep = p->ep;
	struct fid_cq *scq = p->scq;
	fi_addr_t dest_addr = prov.fi_addrs[remote_rank];
	uint64_t rem_addr, key;
	void *tmp = &scratch[0];
	app_data_t *data = &prov.data;

	// assume same sized tables with identical offsets
	rem_addr = (uint64_t)(p->data.r_table_addr);
	rem_addr += ((uint64_t)addr) - ((uint64_t)hpcc_table);
	key = p->data.r_table_key;
	*(uint64_t *)tmp = val;

	rc = fi_atomic(ep, tmp, 1, fi_mr_desc(data->l_scratch_mr), dest_addr,
			rem_addr, key, FI_UINT64, FI_BXOR, NULL);

	ASSERT_MSG(!rc, "failed to xor a value, rc=%d", rc);

	wait_for_comp(scq, 1);
}

static inline void print_usage(void)
{
	if (!rank) {
		ERROR("\n%s\n", TEST_DESC);
		ERROR("\nOptions:\n");

		ct_print_opts_usage("-h", "display this help message");
		ct_print_opts_usage("-m", "memory in bytes per PE");
		ct_print_opts_usage("-n", "number of updates per PE");
    ct_print_std_usage();
	}
}

static inline void free_ep_res(fabric_t *fabric, int remote_rank)
{
	struct peer *p = &fabric->peers[remote_rank];
	int ret;

	ret = fi_close(&p->rcq->fid);
	if (ret != FI_SUCCESS)
		ct_print_fi_error("fi_close: rcq", ret);
	else
		p->rcq = NULL;

	ret = fi_close(&p->scq->fid);
	if (ret != FI_SUCCESS)
		ct_print_fi_error("fi_close: scq", ret);
	else
		p->scq = NULL;
}

static inline int alloc_ep_res(fabric_t *fabric, int remote_rank)
{
	struct peer *p = &fabric->peers[remote_rank];
	struct fi_cq_attr cq_attr;
	int ret;

	memset(&cq_attr, 0, sizeof(cq_attr));
	cq_attr.format = FI_CQ_FORMAT_CONTEXT;
	cq_attr.wait_obj = FI_WAIT_NONE;
	cq_attr.size = rx_depth;

	/* Open completion queue for send completions */
	ret = fi_cq_open(fabric->dom, &cq_attr, &p->scq, NULL);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_cq_open", ret);
		goto err_scq_open;
	}

	/* Open completion queue for recv completions */
	ret = fi_cq_open(fabric->dom, &cq_attr, &p->rcq, NULL);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_cq_open", ret);
		goto err_rcq_open;
	}

	return 0;

	err_rcq_open: fi_close(&p->scq->fid);
	p->scq = NULL;
	err_scq_open: return ret;
}

static inline int bind_ep_res(fabric_t *fabric, int remote_rank)
{
	struct peer *p = &fabric->peers[remote_rank];
	int ret;

	/* Bind Send CQ with endpoint to collect send completions */
	ret = fi_ep_bind(p->ep, &p->scq->fid, FI_TRANSMIT);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_ep_bind", ret);
		return ret;
	}

	/* Bind Recv CQ with endpoint to collect recv completions */
	ret = fi_ep_bind(p->ep, &p->rcq->fid, FI_RECV);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_ep_bind", ret);
		return ret;
	}

	/* Bind AV with the endpoint to map addresses */
	ret = fi_ep_bind(p->ep, &fabric->av->fid, 0);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_ep_bind", ret);
		return ret;
	}

	ret = fi_enable(p->ep);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_enable", ret);
		return ret;
	}

	return ret;
}

static inline int init_fabric(fabric_t *fabric)
{
	int ret;
	uint64_t flags = 0;

	/* Get fabric info */
	ret = fi_getinfo(CT_FIVERSION, NULL, NULL, flags, fabric->hints,
			&fabric->info);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_getinfo", ret);
		return ret;
	}

	/* Open fabric */
	ret = fi_fabric(fabric->info->fabric_attr, &fabric->fab, NULL);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_fabric", ret);
		goto err_fabric_open;
	}

	/* Open domain */
	ret = fi_domain(fabric->fab, fabric->info, &fabric->dom, NULL);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_domain", ret);
		goto err_domain_open;
	}

	return 0;

	err_domain_open: fi_close(&fabric->fab->fid);
	err_fabric_open: return ret;
}

static int init_endpoint(fabric_t *fabric, int remote_rank)
{
	struct peer *p = &fabric->peers[remote_rank];
	int ret;
	int i;

	/* Open endpoint */
	ret = fi_endpoint(fabric->dom, fabric->info, &p->ep, NULL);
	if (ret) {
		ct_print_fi_error("fi_endpoint", ret);
		goto err_fi_endpoint;
	}

	/* Allocate endpoint resources */
	ret = alloc_ep_res(fabric, remote_rank);
	if (ret)
		goto err_alloc_ep_res;

	/* Bind EQs and AVs with endpoint */
	ret = bind_ep_res(fabric, remote_rank);
	if (ret)
		goto err_bind_ep_res;

	return 0;

	err_bind_ep_res: free_ep_res(fabric, remote_rank);
	err_alloc_ep_res: fi_close(&p->ep->fid);
	err_fi_endpoint: return ret;
}

static int init_av(fabric_t *fabric)
{
	void *addr;
	size_t addrlen = 0;
	int ret;
	int i;
	struct peer *peers = fabric->peers;

	/* use first ep since they will all have the same source addr */
	for (i = 0; i < num_ranks; i++)
		if (fabric->peers[i].ep)
			break;
	assert(i < num_ranks);

	fi_getname(&peers[i].ep->fid, NULL, &addrlen);

	addr = malloc(addrlen);
	assert(addr);

	ret = fi_getname(&peers[i].ep->fid, addr, &addrlen);
	if (ret != 0) {
		ct_print_fi_error("fi_getname", ret);
		free(addr);
		return ret;
	}

	fabric->addrs = calloc(num_ranks, addrlen);
	assert(fabric->addrs);

	ctpm_Allgather(addr, addrlen, fabric->addrs);

	fabric->fi_addrs = calloc(num_ranks, sizeof(fi_addr_t));
	assert(fabric->fi_addrs);

	/* Insert address to the AV and get the fabric address back */
	ret = fi_av_insert(fabric->av, fabric->addrs, num_ranks, fabric->fi_addrs,
			0, NULL);
	if (ret != num_ranks) {
		ct_print_fi_error("fi_av_insert", ret);
		return ret;
	}

	free(addr);

	return 0;
}

static int connect_to_server(void)
{
	return 0;
}

static int listen_for_connections(void)
{
	return 0;
}

static int read_data(void)
{
	return 0;
}


static int setup(void)
{
	hpcc_table = malloc(local_table_size * sizeof(uint64_t));
	if (!hpcc_table)
		send_abort = 1;

	ctpm_Barrier();
	recv_abort = ct_allreduce_int_sum(&send_abort, num_ranks);
	ctpm_Barrier();

	if (recv_abort > 0) {
		if (HEAD_RANK)
			fprintf(outFile, "Failed to allocate memory for the main table.\n");
		/* check all allocations in case there are new added and their order changes */
		if (hpcc_table)
			free(hpcc_table);
		goto failed_table;
	}

	for (i = 0; i < num_ranks; i++)
		hpcc_lock[i] = UNLOCKED;

	/* register memory */
	rc = fi_mr_reg(prov.dom, hpcc_table, local_table_size * sizeof(uint64_t),
			FI_REMOTE_READ | FI_REMOTE_WRITE | FI_SEND | FI_RECV | FI_READ
					| FI_WRITE, 0, 0, 0, &prov.data.l_table_mr, NULL);
	if (rc != FI_SUCCESS)
		DEBUG("rc=%d\n", rc);
	assert(rc == FI_SUCCESS);

	/* distribute memory keys */
	exchange_registration_data(&prov);

	/* Default number of global updates to table: 4x number of table entries */
	default_num_updates = 4 * table_size;
	proc_num_updates = 4 * local_table_size;
	actual_num_updates = default_num_updates;

	if (HEAD_RANK) {
		fprintf(outFile, "Running on %d processors\n", num_ranks);
		fprintf(outFile,
				"Total Main table size = 2^" FSTR64 " = " FSTR64 " words\n",
				log_table_size, table_size);
		fprintf(outFile,
				"PE Main table size = (2^" FSTR64 ")/%d  = " FSTR64 " words/PE MAX\n",
				log_table_size, num_ranks, local_table_size);

		fprintf(outFile,
				"Default number of updates (RECOMMENDED) = " FSTR64 "\n",
				default_num_updates);
	}

	/* Initialize main table */
	for (i = 0; i < local_table_size; i++)
		hpcc_table[i] = i + global_start_my_proc;

	saved_initial_ran_val = generate_initial_xor_val(4 * global_start_my_proc);
}

static int generate_data(void)
{
	double current_time = usec_time();
	double elapsed = current_time - start_time;


}

static int check_for_disconnect(void)
{

}

static int teardown(void)
{
	/* End verification phase */

	rc = fi_close(&prov.data.l_lock_mr->fid);
	assert(rc == FI_SUCCESS);

	rc = fi_close(&prov.data.l_table_mr->fid);
	assert(rc == FI_SUCCESS);

	rc = fi_close(&prov.data.l_scratch_mr->fid);
	assert(rc == FI_SUCCESS);

	free(hpcc_table);
	free(hpcc_lock);
	failed_table:

	if (HEAD_RANK)
		if (outFile != stderr)
			fclose(outFile);

	ctpm_Barrier();

	return 0;
}

static inline int init_gnix_prov(fabric_t *fabric)
{
	int ret;
	int i;
	struct fi_av_attr av_attr;

	/* Fabric initialization */
	ret = init_fabric(fabric);
	if (unlikely(ret)) {
		ERROR("Problem in fabric initialization\n");
		return ret;
	}

	fabric->peers = calloc(num_ranks, sizeof(*fabric->peers));
	assert(fabric->peers);

	// Set AV attributes
	memset(&av_attr, 0, sizeof(av_attr));
	av_attr.type =
			fabric->info->domain_attr->av_type ?
					fabric->info->domain_attr->av_type : FI_AV_MAP;
	av_attr.count = num_ranks;
	av_attr.name = NULL;

	/* Open address vector (AV) for mapping address */
	ret = fi_av_open(fabric->dom, &av_attr, &fabric->av, NULL);
	if (unlikely(ret)) {
		ct_print_fi_error("fi_av_open", ret);
		return ret;
	}

	// initialize all endpoints
	for (i = 0; i < num_ranks; i++) {
		ret = init_endpoint(fabric, i);
		if (ret) {
			ERROR("Problem in endpoint initialization\n");
			return ret;
		}
	}

	// init av
	ret = init_av(fabric);
	if (unlikely(ret)) {
		ERROR("Problem in AV initialization\n");
		return ret;
	}

	return 0;
}

static inline void fini_gnix_prov(fabric_t *fabric)
{
	int ret;
	int i;

	if (fabric->info)
		free(fabric->info);
	if (fabric->hints)
		free(fabric->hints);

	// close all endpoints
	for (i = 0; i < num_ranks; i++) {
		free_ep_res(fabric, i);

		fi_close(&fabric->peers[i].ep->fid);
	}

	if (fabric->av) {
		ret = fi_close(&fabric->av->fid);
		if (ret != FI_SUCCESS)
			ct_print_fi_error("fi_close: av", ret);
	}

	if (fabric->dom) {
		fi_close(&fabric->dom->fid);
		if (ret != FI_SUCCESS)
			ct_print_fi_error("fi_close: dom", ret);
	}

	if (fabric->fab) {
		fi_close(&fabric->fab->fid);
		if (ret != FI_SUCCESS)
			ct_print_fi_error("fi_close: fab", ret);
	}

	if (fabric->peers)
		free(fabric->peers);
	if (fabric->addrs)
		free(fabric->addrs);
}

int main(int argc, char **argv)
{
	int i, j;
	int size;
	int op, ret;
	struct fi_info *hints;
	int credential;
	int *credential_arr;
	drc_info_handle_t info;
	program_state_t state = 0;
	int done = 0;

	tunables.is_data_generator = 1;
	tunables.credential_id = -1;

	ctpm_Init(&argc, &argv);
	ctpm_Rank(&rank);
	ctpm_Job_size(&num_ranks);

	prov.hints = fi_allocinfo();
	if (!prov.hints)
		return EXIT_FAILURE;

	hints = prov.hints;

	while ((op = getopt(argc, argv, "hs:S:C:" CT_STD_OPTS)) != -1) {
		switch(op) {
		default:
			ct_parse_std_opts(op, optarg, hints);
			break;
		case 's': /* seconds to generate data */
			tunables.seconds = atoi(optarg);
			break;
		case 'S': /* server address */
			tunables.is_data_generator = 0;
			tunables.server_address = strdup(optarg);
			break;
		case 'C': /* credential ID */
			tunables.credential_id = atoi(optarg);
			break;
		case 'd': /* enable debug */
			tunables.debug = 1;
		case 'v': /* enable verbose */
			tunables.verbose = 1;
			break;
		case '?':
		case 'h':
			print_usage();
			return EXIT_FAILURE;
		}
	}

	auth_key.type = GNIX_AKT_RAW;
	if (tunables.is_data_generator) {
		VERBOSE("creating drc credential for communication "
			"with other jobs\n");
		if (HEAD_RANK) {
			DEBUG("acquiring credential\n");
			ret = drc_acquire(&credential, 0);
			if (ret) {
				ERROR("failed to acquire credential, ret=%d\n", ret);
				exit(-1);
			}
		}

		ctpm_Bcast(&credential, sizeof(int));
	} else {
		if (tunables.credential_id < 0) {
                        ERROR("credential ID not provided in client mode\n");
                        exit(-1);
                }

		credential = tunables.credential_id;
	}
	
	DEBUG("accessing credential, credential_id=%d\n", credential);
	ret = drc_access(credential, 0, &info);
	if (ret) {
		ERROR("failed to access credential, ret=%d\n", ret);
		if (HEAD_RANK) {
			DEBUG("releasing credential, credential_id=%d\n",
				credential);
			ret = drc_release(credential, 0);
			if (ret)
				ERROR("failed to release credential, ret=%d\n", ret);
		}
		exit(-1);
	}

	auth_key.raw.protection_key = drc_get_first_cookie(info);
	if (HEAD_RANK) {
		PRINT("drc_credential_id=%d\n", credential);
		VERBOSE("Using protection key %08x.\n", auth_key.raw.protection_key);
	}

	// modify hints as needed prior to fabric initialization
	hints->ep_attr->type = FI_EP_RDM;
	hints->caps = FI_TAGGED | FI_DIRECTED_RECV;
	hints->mode = FI_CONTEXT | FI_LOCAL_MR;
	hints->caps |= GNIX_EP_RDM_PRIMARY_CAPS;

	if (!thread_safe) {
		hints->domain_attr->threading = FI_THREAD_COMPLETION;
		hints->domain_attr->data_progress = FI_PROGRESS_MANUAL;
		hints->domain_attr->control_progress = FI_PROGRESS_MANUAL;
	}

	// initialize the gnix provider fabric
	init_gnix_prov(&prov);

	start_time = usec_time();

	// run random access test
	ctpm_Barrier();

	if (!tunables.is_data_generator) {
		ret = connect_to_server();
		if (ret) {
			ERROR("failed to connect to server, ret=%d\n",
				ret);
			goto connection_failure;
		}
		
	}

	while (done) {
		switch (state) {
		case STATE_PROCESS_DATA:
			ret = (tunables.is_data_generator) ? 
				generate_data() : read_data();
			if (ret) { 
				ERROR("failed to generate or read data, ret=%d\n",
					ret);
				done = 1;
			}
			
			break;
		case STATE_PROCESS_CONNECTIONS:	
			ret = (tunables.is_data_generator) ?
				listen_for_connections(): check_for_disconnect();
			if (ret) {
				ERROR("failed to process connections, ret=%d\n", 
					ret);
				done = 1;
			}
			break;
		default:
			ERROR("unrecognized state, state=%d\n", state);
			exit(-1);
		}	
		state = (state + 1) % MAX_STATE;
	}

	if (!tunables.is_data_generator)
		disconnect_from_server();
	else
		send_disconnect_events();

connection_failure:
	ctpm_Barrier();

	// close the gnix provider fabric
	fini_gnix_prov(&prov);

	if (tunables.server_address)
		free(tunables.server_address);

#if HAVE_DRC
	if (HEAD_RANK)
		ret = drc_release(credential, 0);
#endif

	// barrier and finalize
	ctpm_Barrier();

	ctpm_Finalize();

	return 0;
}

/* vi:set sw=8 sts=8 */
