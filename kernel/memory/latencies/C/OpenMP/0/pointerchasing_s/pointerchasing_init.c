/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: pointerchasing_init.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/memory/latencies/C/0/0/pointerchasing/pointerchasing_init.c $
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

#if BENCHIT_KERNEL_USE_HUGE_PAGES == 1
#include <sys/mman.h>
#endif

#ifndef BENCHIT_KERNEL_MIN_ACCESS_LENGTH
#define BENCHIT_KERNEL_MIN_ACCESS_LENGTH (2048)
#endif

#ifndef BENCHIT_KERNEL_MAX_ACCESS_LENGTH
#define BENCHIT_KERNEL_MAX_ACCESS_LENGTH (1024*1024)
#endif

#ifndef BENCHIT_KERNEL_ACCESS_STEPS
#define BENCHIT_KERNEL_ACCESS_STEPS (100)
#endif

#ifndef BENCHIT_KERNEL_CACHELINE_SIZE
#define BENCHIT_KERNEL_DEFAULT_CACHELINE_SIZE (128)
#endif

#ifndef BENCHIT_KERNEL_NUMBER_OF_JUMPS
#define BENCHIT_KERNEL_NUMBER_OF_JUMPS (4000000)
#endif


unsigned int random_number(unsigned long max);
void make_linked_memory(void *mem, long count);
void init_global_vars(void);

long minlength, maxlength, accessstride, numjumps,cachelength;
double dMemFactor;
long nMeasurements;

static int use_hugepages;
long cacheline_size;

void bi_getinfo(bi_info* infostruct){
  int i;
  char buf[200], *s;
 

  init_global_vars();
  /*infostruct->kernelstring=bi_strdup("Random Memory Access");*/
  infostruct->kerneldescription = bi_strdup("Memory Access Time (C)");
  infostruct->codesequence=bi_strdup("for i=1,N#  var=memory[random(0..size)]#");
  infostruct->xaxistext=bi_strdup("Accessed Memory in Byte");
  
  infostruct->numfunctions= 1;
  infostruct->num_measurements=nMeasurements;
  
	/* allocating memory for y axis texts and properties */
  allocYAxis(infostruct);
  
  for (i=0; i< infostruct->numfunctions; i++)
  		infostruct->selected_result[i] = SELECT_RESULT_AVERAGE;
		
  infostruct->base_xaxis=10.0;
  infostruct->base_yaxis[0]=0.0;  
  infostruct->legendtexts[0]=bi_strdup("Average Access Time");
  infostruct->yaxistexts[0]=bi_strdup("Average Access Time [cycles]");
}

void init_global_vars() {
    
  char *envir;
    

  IDL(3,printf("Init global variables ... "));
  envir=bi_getenv("BENCHIT_KERNEL_MIN_ACCESS_LENGTH",1);
  minlength=(envir != 0) ? 1000*atoi(envir) : BENCHIT_KERNEL_MIN_ACCESS_LENGTH;
  if(minlength==0) {
    minlength=BENCHIT_KERNEL_MIN_ACCESS_LENGTH;
  }
  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_MAX_ACCESS_LENGTH",1);
  maxlength=(envir != 0) ? 1000*atoi(envir) : BENCHIT_KERNEL_MAX_ACCESS_LENGTH;
  if(maxlength==0) {
    maxlength=BENCHIT_KERNEL_MIN_ACCESS_LENGTH;
  }
  
  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_FLUSH_LENGTH",1);
  cachelength=(envir != 0) ? 1000*atoi(envir) : BENCHIT_KERNEL_MAX_ACCESS_LENGTH;
  if(cachelength==0) {
    cachelength=BENCHIT_KERNEL_MAX_ACCESS_LENGTH;
  }
  
  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_CACHELINE_SIZE",1);
  cacheline_size=(envir != 0) ? atoi(envir) : BENCHIT_KERNEL_DEFAULT_CACHELINE_SIZE;
  if(cacheline_size==0) {
    cacheline_size=BENCHIT_KERNEL_DEFAULT_CACHELINE_SIZE;
  }
  
  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_ACCESS_STEPS",1);
  nMeasurements = (envir != 0) ? atoi(envir) : BENCHIT_KERNEL_ACCESS_STEPS;
  dMemFactor =((double)maxlength)/((double)minlength);
  dMemFactor = pow(dMemFactor, 1.0/((double)nMeasurements-1));
  
  envir=bi_getenv("BENCHIT_KERNEL_USE_HUGE_PAGES",1);
  use_hugepages=(envir != 0) ? atoi(envir) : 0;
  IDL(3,printf("done\n"));
}

BI_GET_CALL_OVERHEAD_FUNC((),jump_around(NULL,0))

void *bi_init(int problemSizemax){
  void *mem;

  IDL(3, printf("Enter init ... "));
#if BENCHIT_KERNEL_USE_HUGE_PAGES == 1
  if (use_hugepages) {
    mem = mmap(NULL, maxlength*2, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    madvise(mem, maxlength*2, MADV_HUGEPAGE);
    if (mem==NULL){
      printf("No more core, need %.3f MByte\n", 
	     (double)maxlength);
      exit(127);
    }
  } else
#endif  
  {
    mem = malloc(maxlength*2);
  }
  IDL(3, printf("allocated %.3f MByte\n",
		(double)maxlength));

  make_linked_memory(mem, maxlength);
  return (mem);
}

void bi_cleanup(void *mcb){
  return;
}
