/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: pointerchasing_entry.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/memory/latencies/C/0/0/pointerchasing/pointerchasing_entry.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: Memory Access Time (C)
 *******************************************************************/

#include "interface.h"
#include "pointerchasing.h"
#include <stdlib.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <omp.h>
#include <x86intrin.h>

#define ONE {ptr=(void **) *ptr;}
#define TEN ONE ONE ONE ONE ONE ONE ONE ONE ONE ONE
#define HUN TEN TEN TEN TEN TEN TEN TEN TEN TEN TEN
#define THO HUN HUN HUN HUN HUN HUN HUN HUN HUN HUN

#define rdtsc(X)        asm volatile("rdtsc":"=A" (X))
#if defined (__i386__)
	#define rdtscll(val) do { \
     unsigned int __a,__d; \
     asm volatile("rdtsc" : "=a" (__a), "=d" (__d)); \
     (val) = ((unsigned long long)__a) | (((unsigned long long)__d)<<32); \
	} while(0)
//	#define rdtscll(val)  asm volatile("rdtsc":"=A" (val))
//__asm__ __volatile__("rdtsc" : "=A" (val))
#elif defined(__x86_64__)
	#define rdtscll(val) do { \
     unsigned int __a,__d; \
     asm volatile("rdtsc" : "=a" (__a), "=d" (__d)); \
     (val) = ((unsigned long long)__a) | (((unsigned long long)__d)<<32); \
	} while(0)
#elif defined(__ia64__)
#include <ia64intrin.h>
	#define rdtscll(val) do { \
     unsigned long __a; \
     __a=__getReg(_IA64_REG_AR_ITC);\
     (val) = __a * 4; \
	} while(0)
	//define rdtscll(val) val=(long long)(1.6E9*bi_gettime());//PAPI_get_real_cyc();
#else
	#define rdtscll(val) do { \
	   asm volatile("mrs %0, PMCCNTR_EL0" : "=r"(val)); \
	} while(0)
#endif

extern long cacheline_size;

void *jump_around(void *mem, long n);


/** generates a random number between 0 and (max-1)
 *  @param  max maximum random number
 *  @return a random number between 0 and (max-1)
 */
unsigned int random_number(unsigned long max)
{
  return (unsigned int) (((double)max)*rand()/(RAND_MAX+1.0));
}


/** creates a memory are that is randomly linked 
 *  @param mem     the memory area to be used
 *  @param length  the number of bytes that should be used
 */
void make_linked_memory(void *mem, long length) {

  /* some pointers to generate the list */
  void **ptr, **first;
  /** how many ptr we create within the memory */
  long num_ptr=length/cacheline_size; //sizeof(void *);
  /** the list for all memory locations that are linked */
  long *ptr_numbers;
  /** for the loops */
  long loop_ptrs;
  /** actual random number */
  long act_num;

  /* allocate memory for ptr numbers */
  ptr_numbers=(long *) malloc(num_ptr*sizeof(long));
  if(num_ptr>0 && ptr_numbers==NULL)
    {
      printf("no more core in make_linked_mem()\n");
      bi_cleanup(mem);
      exit(1);
    }
  /* initialize ptr numbers, the 0 is used as the first
   * number
   */

  for(loop_ptrs=1; loop_ptrs<num_ptr; loop_ptrs++)
    ptr_numbers[loop_ptrs-1]=loop_ptrs;

  /* init first ptr with first memory location */
  ptr=(void **)mem;
  first=ptr;
   
  num_ptr--;

  while(num_ptr>1) {
    /* get a random position within the
       remaining list */
    act_num=random_number(num_ptr);
    /* create a link from the last ptr 
       to this ptr */
    *ptr=(void *) (first+(cacheline_size/sizeof(void**))*ptr_numbers[act_num]);
    /* move pointer to new memory location */
    ptr=first+(cacheline_size/sizeof(void**))*ptr_numbers[act_num];
    /* remove used ptr number from list of
       pointer numbers, just copies the last 
       number to the actual position */
    ptr_numbers[act_num]=ptr_numbers[num_ptr-1];
    num_ptr--;
  }

  /* the last number is linked to the first */
  *ptr=(void *) first;

  /* free the ptr list */
  free(ptr_numbers);
  IDL(4,printf("\n"));
}

int ext_res;

void flush()
{
  static int* fill=NULL;
	extern long cachelength;
	if (fill==NULL)
  { fill=malloc(cachelength);
    int x=rand();
     for (long i=0;i<cachelength/sizeof(int);i++)
       fill[i]=x*i;
  }
  unsigned int res=0;
  for (long i=0;i<cachelength/sizeof(int);i++)
     res =res ^ fill[i];
  ext_res=res;
}

int bi_entry(void *mcb,int problemSize,double *results) {

	static double timeroh=0, calloh=0;
	long long start, stop;
	int i;

	long length;
	long long c[4];
	void *ptr;
	
	extern double dMemFactor;
	extern long minlength;

	length = (long)(((double)minlength)*pow(dMemFactor, (problemSize-1)));

	results[0]=(double) length;


omp_set_num_threads(2);
#pragma omp parallel
{
  flush();
#pragma omp barrier
  if (omp_get_thread_num() == 0) {
  	  jump_around_w(mcb, length/cacheline_size);
  }
#pragma omp barrier
  flush();
#pragma omp barrier
  if (omp_get_thread_num() == 0) {
  	  jump_around(mcb, length/cacheline_size);
  }
#pragma omp barrier
  _mm_mfence();
  if (omp_get_thread_num() == 1) {
    rdtscll(start);
	  jump_around(mcb, length/cacheline_size);
    _mm_lfence();
    rdtscll(stop);
	}
}
	 results[1]=(double)(stop-start)/((double)length/cacheline_size);
   

  return (0);
}
