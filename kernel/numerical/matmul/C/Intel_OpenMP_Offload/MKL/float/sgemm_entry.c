/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: dgemm_entry.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/numerical/matmul/C/OpenMP/MKL/double/dgemm_entry.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: Matrix Multiply, BLAS, MKL (C) - OpenMP version
 *******************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "sgemm.h"
#include "interface.h"
#include <omp.h>

#include <mkl.h>
#include <mkl_omp_offload.h>

void init_data(fds *myfds, unsigned long long size) {
	long x, index, max;
  #pragma omp parallel for schedule(static,1) private(x,index,max) shared(myfds,size)
	for(x = 0; x < size; x++) {
		index = x * size;
		max = index + size;
		for(index; index < max; index++) {
			myfds->feld1[index] = 30.0;
			myfds->feld2[index] = 0.01;
			myfds->feld3[index] = 0.0;
		}
	}
	IDL(5, printf("init_data done\n"));
}


int bi_entry(void *mcb_in, int problemSize,double *results){
	float one=1.0;
	double time=0, start, stop;
	double nOperations=0.0;
	long lCurrentSize;
	unsigned long long size;
	char N='N';
	float *f1, *f2, *f3;
	int ii, jj;
	double dummy = 0.0;
	int dnum = 0;
	fds* mcb = (fds*)mcb_in;

	if(results == NULL)
		return -1;
	
	size = (unsigned long long)bi_get_list_element(problemSize);
	results[0] = size;
	size_t size2=size*size;
	nOperations = (1.0*size)*(1.0*size)*(2.0*size-1.0);
	
	lCurrentSize = size*size*sizeof(float);

	((fds*)mcb)->feld1=(float*)mkl_malloc(lCurrentSize, 64);
	((fds*)mcb)->feld2=(float*)mkl_malloc(lCurrentSize, 64);
	((fds*)mcb)->feld3=(float*)mkl_malloc(lCurrentSize, 64);

	f1=((fds*)mcb)->feld1; f2=((fds*)mcb)->feld2; f3=((fds*)mcb)->feld3;

	if((f1==NULL) || (f2==NULL) || (f3==NULL)) {
		printf("\nmalloc (%ld bytes) failed in bi_entry()\n",(long) (3.0*lCurrentSize)); 
		bi_cleanup(mcb);
		exit(127);
		}

	init_data(mcb, size);

	/* ************************** */
	start=bi_gettime();
#pragma omp target data map(to:f1[0:size2],f2[0:size2]) map(tofrom:f3[0:size2]) device(dnum)
{
 #pragma omp target variant  dispatch device(dnum) use_device_ptr(f1, f2, f3)
 {
   cblas_sgemm(CblasColMajor, CblasNoTrans, CblasNoTrans, size, size, size, one, f1, size, f2, size, one, f3, size);
 }
}
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
			mkl_free(f1);
			f1=NULL;
		}
		if(f2!=NULL) {
			mkl_free(f2);
			f2=NULL;
		}
		if(f3!=NULL) {
			mkl_free(f3);
			f3=NULL;
		}
	}

	return 0;
}


