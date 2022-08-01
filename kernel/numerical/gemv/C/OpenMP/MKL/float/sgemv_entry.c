/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: Matrix Vector Multiply, BLAS, MKL (C) - OpenMP version
 *******************************************************************/

#include <mkl_cblas.h>
#include <stdio.h>
#include <stdlib.h>
#include "sgemv.h"
#include "interface.h"
#include <omp.h>

void init_data(fds *myfds, int size) {
	long x, index, max;
  #pragma omp parallel for schedule(static,1) private(x,index,max) shared(myfds,size)
	for(x = 0; x < size; x++) {
		index = x * size;
		max = index + size;
		myfds->source_vec[x] = 30.0;
		myfds->target_vec[x] = 0.0;
		for(index; index < max; index++) {
			myfds->mat[index] = 0.01;
		}
	}
	IDL(5, printf("init_data done\n"));
}


int bi_entry(void *mcb, int problemSize,double *results){
	float one=1.0;
	double time=0, start, stop;
	double nOperations=0.0;
	long lCurrentSize;
	unsigned long long size;
	char N='N';
	float *f1, *f2, *f3;
	int ii, jj;
	double dummy = 0.0;

	if(results == NULL)
		return -1;
	
	size = (unsigned long)bi_get_list_element(problemSize);
	results[0] = size;
	nOperations = (1.0*size)*(2.0*size-1.0);
	

	((fds*)mcb)->source_vec=malloc(size*sizeof(float));
	((fds*)mcb)->mat=malloc(size*size*sizeof(float));
	((fds*)mcb)->target_vec=malloc(size*sizeof(float));

	f1=((fds*)mcb)->source_vec; f2=((fds*)mcb)->mat; f3=((fds*)mcb)->target_vec;

	if((f1==NULL) || (f2==NULL) || (f3==NULL)) {
		printf("\nmalloc (%ld bytes) failed in bi_entry()\n",(long) (2.0*size*sizeof(float)+size*size*sizeof(float))); 
		bi_cleanup(mcb);
		exit(127);
		}

	init_data(mcb, size);

	/* ************************** */
	start=bi_gettime();
	
	cblas_sgemv(CblasRowMajor,CblasNoTrans, size, size, one, f2, size, f1, one, one, f3, one);
	stop=bi_gettime();
	/* ************************** */

	time=stop-start - dTimerOverhead;
	if (time < 3*dTimerGranularity)   {
		results[1]=INVALID_MEASUREMENT;
	}
	else {
		results[1]=nOperations/time;
	}

	if(mcb!=NULL) {
		if(f1!=NULL) {
			free(f1);
			f1=NULL;
		}
		if(f2!=NULL) {
			free(f2);
			f2=NULL;
		}
		if(f3!=NULL) {
			free(f3);
			f3=NULL;
		}
	}

	return 0;
}


