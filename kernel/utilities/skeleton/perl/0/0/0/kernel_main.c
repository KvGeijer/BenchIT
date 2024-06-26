/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: kernel_main.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/perl/0/0/0/kernel_main.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: perl kernel skeleton
 *******************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "interface.h"
#include "kernel_main.h"
#include "tools/benchscript.h"

/* FIRST: implement the BenchIT Interface functions */

/**  The implementation of the bi_getinfo from the BenchIT interface.
 *   Here the infostruct is filled with information about the
 *   kernel.
 *   @param infostruct  a pointer to a structure filled with zeros
 */
void bi_getinfo(bi_info * infostruct)
{
   int i, j, graph = 0;
   char* legend_text;
   mydata_t * penv;
   
   penv = (mydata_t *) malloc(sizeof(mydata_t));

   /* get environment variables for the kernel */
   evaluate_environment(penv);
   infostruct->codesequence = bi_strdup("start kernel; do nothing; ");
   infostruct->kerneldescription = 
     bi_strdup("blockwise reading from database");
   infostruct->xaxistext = bi_strdup("Stripe Size read from Database");
   infostruct->base_xaxis = 2;
   infostruct->num_measurements = penv->steps;
   infostruct->num_processes = 1;
   infostruct->num_threads_per_process = 0;
   infostruct->kernel_execs_mpi1 = 0;
   infostruct->kernel_execs_mpi2 = 0;
   infostruct->kernel_execs_pvm = 0;
   infostruct->kernel_execs_omp = 0;
   infostruct->kernel_execs_pthreads = 0;
   infostruct->numfunctions = penv->num_processes * penv->num_threads;

   /* allocating memory for y axis texts and properties */
   allocYAxis(infostruct);
   /* setting up y axis texts and properties */
   for(i=1; i <= penv->num_processes; i++)
   {
     for(j=1; j <= penv->num_threads; j++)
     {
       infostruct->yaxistexts[graph] = bi_strdup("s");
       infostruct->selected_result[graph] = SELECT_RESULT_HIGHEST;
       infostruct->base_yaxis[graph] = penv->logbase;
       
       /* build legend text */
       legend_text = bi_strdup("read speed");
       if(penv->num_processes > 1)
       {
         legend_text = bi_strcat(legend_text, " processes: ");
         legend_text = bi_strcat(legend_text, int2char(i));   
       }
       if(penv->num_threads > 1)
       {
         legend_text = bi_strcat(legend_text, " threads: ");
         legend_text = bi_strcat(legend_text, int2char(j));
       }
       
       infostruct->legendtexts[graph] = bi_strdup(legend_text);
       graph++;
     }
   }

   /* free all used space */
   if (penv) free(penv);
}

/* SECOND implement local functions */

/* Reads the environment variables used by this kernel. */
void evaluate_environment(mydata_t * pmydata)
{
  int errors = 0;
  char * p = 0;

  /* read the kernel specific values */ 
  p = bi_getenv("BENCHIT_KERNEL_LOGBASE", 0);
  if (p == NULL) errors++;
  else pmydata->logbase = atoi(p);
   
  p = bi_getenv("BENCHIT_KERNEL_PROBLEMSIZE_MIN_POWER", 0);
  if (p == NULL) errors++;
  else pmydata->min = atoi(p);

  p = bi_getenv("BENCHIT_KERNEL_PROBLEMSIZE_MAX_POWER", 0);
  if (p == NULL) errors++;
  else pmydata->max = atoi(p);

 	p = bi_getenv("BENCHIT_KERNEL_MAX_PROCESSES", 1);
  if (p == NULL) errors++;
  else pmydata->num_processes = atoi(p);
  
  p = bi_getenv("BENCHIT_KERNEL_MAX_THREADS", 0);
  if (p == NULL) errors++;
  else pmydata->num_threads = atoi(p);

  /* read the script specifics */
  p = bi_getenv("BENCHIT_PERL_INTERPRETER", 0);
  if (p == NULL) errors++;
  else pmydata->interpreter = bi_strdup(p);

  p = bi_getenv("KERNELDIR", 0);
  if (p == NULL) errors++;
  else pmydata->kerneldir = bi_strdup(p);

  p = bi_getenv("BENCHIT_KERNEL_MIN_RUNTIME", 0);
  if (p == NULL) errors++;
  else pmydata->min_runtime = atoi(p);

  if (errors > 0)
  {
    fprintf(stderr, 
      "There's at least one environment variable not set!\n");
    fflush(stderr);
    exit(1);
  }

  /* calculate the number of steps to run   */
  pmydata->steps = (int) (pmydata->max - pmydata->min + 1);
}

char* bi_build_work_script(char* script_file, char *meas_mode, 
  void* pdata)
{
  char *work_script;

  mydata_t * pmydata = (mydata_t *) pdata;

  work_script = bi_strcat(pmydata->interpreter, " ");
  work_script = bi_strcat(work_script, pmydata->kerneldir);
  work_script = bi_strcat(work_script, "/");
  work_script = bi_strcat(work_script, script_file);
  work_script = bi_strcat(work_script, " -BIMode ");
  work_script = bi_strcat(work_script, meas_mode);

  return work_script;
}

/** Implementation of the bi_init of the BenchIT interface.
 *  Here you have the chance to allocate the memory you need.
 *  It is also possible to allocate the memory at the beginning
 *  of every single measurement and to free the memory thereafter.
 *  But always making use of the same memory is faster.
 *  HAVE A LOOK INTO THE HOWTO !
 */
void* bi_init(int problemSizemax)
{
  char *work_script;
  mydata_t * pmydata;

  pmydata = (mydata_t*)malloc(sizeof(mydata_t));
  if (pmydata == 0)
  {
    fprintf(stderr, "Allocation of structure mydata_t failed\n"); 
    fflush(stderr);
    exit(127);
  }
  evaluate_environment(pmydata);

  /* initialize the database for measurement */
  work_script = bi_build_work_script("work_script.pl", "init", pmydata);
  work_script = bi_strcat(work_script, " -BIProblemSize ");
  work_script = bi_strcat(work_script, int2char(pow(pmydata->logbase, 
    pmydata->max)));

  /* call the interpreter without multiprocessing or -threading */
  printf("%s",work_script);
  bi_script((void*) work_script, 1, 1);
 
  return (void *)pmydata;
}

/** The central function within each kernel. This function
 *  is called for each measurement step seperately.
 *  @param  mdpv         a pointer to the structure created in bi_init,
 *                       it is the pointer the bi_init returns
 *  @param  problemSize  the actual problemSize
 *  @param  results      a pointer to a field of doubles, the
 *                       size of the field depends on the number
 *                       of functions, there are #functions+1
 *                       doubles
 *  @return 0 if the measurement was sucessfull, something
 *          else in the case of an error
 */
int bi_entry(void* mdpv, int iproblemSize, double* dresults)
{
  /* time: the time for a single measurement in seconds */
  double timeInSecs = 0.0, time = 0.0;
  
  /* i: is used for loop iterations */
  int normalize_count = 0, proc_count, thread_count, graph_count = 1;
  int myproblemSize = (int) iproblemSize;

  /* work_script:  is used to store th script na/me and params */
  char *work_script;

  /* cast void* pointer */
  mydata_t * pmydata = (mydata_t *) mdpv;

  /* calculate real problemSize */
  myproblemSize = pow(pmydata->logbase, (myproblemSize - 1 + pmydata->min));

  /* check wether the pointer to store the results in is valid or not */
  if (dresults == NULL) return 1;

  work_script = bi_build_work_script("work_script.pl", "read", pmydata);
  work_script = bi_strcat(work_script, " -BIProblemSize ");
  work_script = bi_strcat(work_script, int2char(myproblemSize));

  /* start */
  for(proc_count = 1; proc_count <= pmydata->num_processes; proc_count++)
  {
    for(thread_count = 1; thread_count <= pmydata->num_threads; 
      thread_count++)
    {
	    //reset the normalize counter
    	normalize_count = 0;
  		timeInSecs = 0;
      do
      {
        bi_startTimer();
        /* do measurement */
        bi_script((void*) work_script, proc_count, thread_count);
        /* get actual time */
        time = bi_stopTimer();
        
        if(time>=0){
        	timeInSecs += time;
          normalize_count++;
        }
      }
      while(timeInSecs <= (float) pmydata->min_runtime && normalize_count < 1.0e+10); 
  
      /* calculate the average time used for a run */
      /* if the operation was too fast to be measured mark as invalid */
      if(timeInSecs >= 0 && normalize_count > 0)
        timeInSecs /= normalize_count;

      /* store the result */
      dresults[graph_count] = time;
      
      graph_count++;
    }
  }

  /* store the problemSize */
  dresults[0] = (double) myproblemSize;

  return 0;
}

/** 
  Clean up the memory
  currently not used
*/
void bi_cleanup(void* dummy)
{ 
   return;
}
