/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: Matrix Vector Multiply, BLAS, MKL (C) - OpenMP version
 *******************************************************************/

#ifndef SGEMV__

#define SGEMV__
	typedef struct floating_data_struct {
	  float *source_vec, *mat, *target_vec;
	} fds;

//	long MIN, MAX, INCREMENT; 

#else
//	extern long MIN, MAX, INCREMENT; 

#endif


