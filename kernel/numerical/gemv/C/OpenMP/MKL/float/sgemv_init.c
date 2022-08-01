/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: Matrix Multiply, BLAS, MKL (C) - OpenMP version
 *******************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "interface.h"
#include <omp.h>
#include "sgemv.h"

void bi_getinfo(bi_info* infostruct) {
   char *p = 0;

   /* get environment variables for the kernel */
   /* parameter list */
   p = bi_getenv("BENCHIT_KERNEL_PROBLEMLIST", 0);
   bi_parselist(p);

	infostruct->kerneldescription = bi_strdup("Matrix Vector Multiply, BLAS, MKL (C) - OpenMP version");	
	infostruct->codesequence=bi_strdup("SGEMV");
	infostruct->xaxistext=bi_strdup("Matrix Size");
	infostruct->num_measurements = infostruct->listsize;
  
	/* allocating memory for y axis texts and properties */
  allocYAxis(infostruct);
  
	infostruct->yaxistexts[0] = bi_strdup ("FLOPS");
	infostruct->selected_result[0] = SELECT_RESULT_HIGHEST;
	infostruct->legendtexts[0]=bi_strdup("FLOPS");
	infostruct->base_yaxis[0] = 0;

	infostruct->num_processes = 1;
	infostruct->num_threads_per_process = omp_get_num_threads();
	infostruct->kernel_execs_mpi1 = 0;
	infostruct->kernel_execs_mpi2 = 0;
	infostruct->kernel_execs_pvm = 0;
	infostruct->kernel_execs_omp = 1;
	infostruct->kernel_execs_pthreads = 0;
	infostruct->numfunctions = 1;
}

void* bi_init(int problemSizemax) {

	fds *myfds;
	long lMaxSize;

	IDL(3, printf("Enter init\n"));
	myfds=malloc(sizeof(fds));
	if(myfds==NULL) {
		printf("Allocation of structure myfds failed\n");
		exit(127);
	}

	return (myfds);
}

extern void bi_cleanup(void *mcb) {
	fds *data=mcb;
	free(data);
}
