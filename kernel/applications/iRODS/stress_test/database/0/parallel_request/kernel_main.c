/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 *
 * Kernel:
 *
 *******************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "interface.h"

#include "data_struct.h"


/* Reads the environment variables used by this kernel. */
void evaluate_environment(mydata_t * pmydata)
{
   int errors = 0;
   char * p = 0;
   p = bi_getenv("BENCHIT_KERNEL_PROCESS_MIN", 0);
   if (p == NULL)
   	errors++;
   else
   	pmydata->meta_min = atoi(p);
   p = bi_getenv("BENCHIT_KERNEL_PROCESS_MAX", 0);
   if (p == NULL)
   	errors++;
   else
   	pmydata->meta_max = atoi(p);
   p = bi_getenv("BENCHIT_KERNEL_PROCESS_INC", 0);
   if (p == NULL)
   	errors++;
   else
   	pmydata->meta_inc = atoi(p);
   p = bi_getenv("BENCHIT_KERNEL_NUMBER_RUNS", 0);
   if (p == NULL)
      errors++;
   else
      pmydata->number_runs = atoi(p);
   p = bi_getenv("BENCHIT_KERNEL_PROCESS_LOOP", 0);
   if (p == NULL)
      errors++;
   else
      pmydata->threads_loop = atoi(p);
   p = bi_getenv("BENCHIT_SPEZIAL_SCRIPT", 0);
   if (p == NULL)
      errors++;
   else
   {
     strncpy(pmydata->path_script,p,500);
   }
   p = bi_getenv("BENCHIT_SPEZIAL_RESULT", 0);
   if (p == NULL)
      errors++;
   else
   {
     strncpy(pmydata->path_temp,p,500);
   }

   if((pmydata->meta_inc == 1) && (pmydata->meta_min == 0))
   	pmydata->steps = pmydata->meta_max - pmydata->meta_min;
   else
   {
	 	myinttype diff;
	 	diff = pmydata->meta_max - pmydata->meta_min;
   	myinttype test = diff / pmydata->meta_inc;
   	if((diff % pmydata->meta_inc) != 0)
   		pmydata->steps = test + 2;
   	else
   		pmydata->steps = test + 1;
	 }

   if (errors > 0)
   {
      fprintf(stderr, "There's at least one environment variable not set!\n");
      exit(1);
   }
}

/**  The implementation of the bi_getinfo from the BenchIT interface.
 *   Here the infostruct is filled with information about the
 *   kernel.
 *   @param infostruct  a pointer to a structure filled with zeros
 */
void bi_getinfo(bi_info * infostruct)
{
   mydata_t * penv;
   char file_info[100];

   penv = (mydata_t *) malloc(sizeof(mydata_t));

   /* get environment variables for the kernel */
   evaluate_environment(penv);
   infostruct->codesequence = bi_strdup("start kernel; do nothing; ");
   infostruct->kerneldescription = bi_strdup("iRods: Parallel requests to test the behaviour of iRODS");
   infostruct->xaxistext = bi_strdup("Number of Processes");
   infostruct->num_measurements = penv->steps * penv->number_runs;
   infostruct->num_processes = 1;
   infostruct->num_threads_per_process = 0;
   infostruct->kernel_execs_mpi1 = 0;
   infostruct->kernel_execs_mpi2 = 0;
   infostruct->kernel_execs_pvm = 0;
   infostruct->kernel_execs_omp = 0;
   infostruct->kernel_execs_pthreads = 0;
   infostruct->numfunctions = 2;

   /* allocating memory for y axis texts and properties */
   allocYAxis(infostruct);
   /* setting up y axis texts and properties */
	 /* setting up x axis texts and properties */
   infostruct->yaxistexts[0] = bi_strdup("time in s");
   infostruct->selected_result[0] = 1;
   //infostruct->base_yaxis[0] = 0; //logarythmic axis 10^x
   sprintf(file_info,"<imeta> [Operations per Process: %d]",penv->threads_loop);
   infostruct->legendtexts[0] = bi_strdup(file_info);

   infostruct->yaxistexts[1] = bi_strdup("operations per sec");
   infostruct->selected_result[1] = 1;
   //infostruct->base_yaxis[0] = 0; //logarythmic axis 10^x
   sprintf(file_info,"<imeta> [Operations per Process: %d] [op/sec]",penv->threads_loop);
   infostruct->legendtexts[1] = bi_strdup(file_info);

   /* free all used space */
   if (penv) free(penv);
}



/** Implementation of the bi_init of the BenchIT interface.
 *  Here you have the chance to allocate the memory you need.
 *  It is also possible to allocate the memory at the beginning
 *  of every single measurment and to free the memory thereafter.
 *  But making usage always of the same memory is faster.
 *  HAVE A LOOK INTO THE HOWTO !
 *
 *  In this case it also execute all given measurements.
 */
void* bi_init(int problemsizemax)
{
   mydata_t * pmydata;
   pmydata = (mydata_t*)malloc(sizeof(mydata_t));
   if (pmydata == 0)
   {
      fprintf(stderr, "Allocation of structure mydata_t failed\n"); fflush(stderr);
      exit(127);
   }
   evaluate_environment(pmydata);

   if(pmydata->meta_min < 0)
   {
      fprintf(stderr,"Error: BENCHIT_KERNEL_FILES_MIN is not high enough");
      exit(1);
   }

   int i,j;
   myinttype meta_number;
   /* Executes all different measurements */
   for(i = 0; i < pmydata->steps; i++)
   {
      meta_number = 0;
       /* Sets the new metadata number for the measurement*/
      if(pmydata->meta_min == 0)
      {
      	if((i == 0) || (pmydata->meta_inc==1))
      		meta_number = pmydata->meta_min + 1 + (i * pmydata->meta_inc);
      	else
      		meta_number = pmydata->meta_min + (i * pmydata->meta_inc);
      }
      else
      	meta_number = pmydata->meta_min + (i * pmydata->meta_inc);
      if(pmydata->meta_max < meta_number)
      	meta_number = pmydata->meta_max;
      char help[50];
      sprintf(help,"$BENCHIT_SPEZIAL_SCRIPT %d",meta_number);
     /* Executes all repetitions of one measurement */
	   for(j = 0; j < pmydata->number_runs; j++)
	   {
     	fprintf(stdout,"\n\t\t<<<< Processes: %d , Run: %d >>>>\n", meta_number, (j + 1));
     	fflush(stdout);
     	/*Starts the script defined in $BENCHIT_SPEZIAL_SCRIPT*/
     	if (system(help) != 0)
      	fprintf(stderr,"Error: Couldn't start the script %s.", pmydata->path_script);
		 }
   }
   pmydata->CSV = fopen(pmydata->path_temp, "r");
   if(NULL == pmydata->CSV)
   {
      fprintf(stderr, "Error: Can't open the result file\n");
      exit(1);
   }

   return (void *)pmydata;
}



/** The central function within each kernel. This function
 *  is called for each measurment step seperately.
 *  @param  mdpv         a pointer to the structure created in bi_init,
 *                       it is the pointer the bi_init returns
 *  @param  problemsize  the actual problemsize
 *  @param  results      a pointer to a field of doubles, the
 *                       size of the field depends on the number
 *                       of functions, there are #functions+1
 *                       doubles
 *  @return 0 if the measurment was sucessfull, something
 *          else in the case of an error
 *
 *  In this case no measurement will started. Only the results will collected.
 */
int bi_entry(void * mdpv, int iproblemsize, double * dresults)
{
   /* cast void* pointer */
   mydata_t * pmydata = (mydata_t *) mdpv;

   /* check wether the pointer to store the results in is valid or not */
   if (dresults == NULL) return 1;

  int value;
	double time_real, time_user, time_system;

   if(fscanf(pmydata->CSV,"%lf;%lf;%lf\n",&time_real,&time_user,&time_system) != EOF)
   {
      if(fscanf(pmydata->CSV,"%d\n",&value) != EOF)
      dresults[0] = (double) value; // process id
      dresults[1] = time_real; // time
      //operations per second
      if(time_real > 0)
      	dresults[2] = (double) (pmydata->threads_loop * value) / time_real;
   		else
   		{
   			dresults[2] = 0;
   			fprintf(stderr,"Error: Measured time is 0 or less");
   		}
   }
   else
   	fprintf(stderr,"Error: No more entries in th result file");



   return 0;
}

/** Clean up the memory
 */
void bi_cleanup(void* mdpv)
{
   mydata_t * pmydata = (mydata_t*)mdpv;
   fclose(pmydata->CSV);
   if (system("rm $BENCHIT_SPEZIAL_RESULT") != 0)
   	fprintf(stderr,"Error: Couldn't delete %s",pmydata->path_temp);
   if (pmydata) free(pmydata);

   return;
}
