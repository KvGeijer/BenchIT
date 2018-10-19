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

   p = bi_getenv("BENCHIT_KERNEL_NUMBER_RUNS", 0);
   if (p == NULL)
      errors++;
   else
      pmydata->number_runs = atoi(p);

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
 *
 *  In this case it also executes all given measurements to get the
 *  name and the number of the measured Micro-Services for the plot.
 */
void bi_getinfo(bi_info * infostruct)
{
   mydata_t * penv;

   penv = (mydata_t *) malloc(sizeof(mydata_t));

   /* get environment variables for the kernel */
   evaluate_environment(penv);

   infostruct->codesequence = bi_strdup("start kernel; do nothing; ");
   infostruct->kerneldescription = bi_strdup("iRods (Micro-Service): Time measurement of user defined Micro-Services");
   infostruct->xaxistext = bi_strdup("Run Number");
   infostruct->num_measurements = penv->number_runs;
   infostruct->num_processes = 1;
   infostruct->num_threads_per_process = 0;
   infostruct->kernel_execs_mpi1 = 0;
   infostruct->kernel_execs_mpi2 = 0;
   infostruct->kernel_execs_pvm = 0;
   infostruct->kernel_execs_omp = 0;
   infostruct->kernel_execs_pthreads = 0;

   /* Starts the measurement */
   if (system(penv->path_script) != 0)
   {
   	fprintf(stderr,"Error: Couldn't start the script %s.", penv->path_script);
		exit(1);
	 }
	penv->CSV = fopen(penv->path_temp, "r");
   if(NULL == penv->CSV)
   {
      fprintf(stderr, "Error: Can't open the result file\n");
      exit(1);
   }
   /* Determines the number of measured Micro-Services */
   double time;
   myinttype number_func = 0;
   char text1[10],text2[FUNC_NAME];
   while(fscanf(penv->CSV,"%s\t%s\t%lf\n",text1,text2,&time) != EOF)
   {
   	number_func++;
   }
   if(number_func == 0)
   {
   	fprintf(stderr,"\nError: Empty result file\n");
   	exit(1);
   }
   infostruct->numfunctions = number_func - 1;

   /* allocating memory for y axis texts and properties */
   allocYAxis(infostruct);
   /* setting up y axis texts and properties */
  if(fseek(penv->CSV, 0L, SEEK_SET) == -1)
  {
  	fprintf(stderr,"Error: Can't reset the file pointer");
  	exit(1);
  }

  /* setting up axis texts and properties */
  myinttype counter = 0;
	if(fscanf(penv->CSV,"%s\t%s\t%lf\n",text1,text2,&time) != EOF)
	 {
	 	if(strcmp(text2,"start") != 0)
	 	{
	 		fprintf(stderr,"\nError: No start time found\n");
	 		exit(1);
	 	}
	 }
	 else
	 {
	 	fprintf(stderr,"\nError: Empty result file\n");
	 	exit(1);
	 }
	 /* Gets the names of the Micro-Services from the result file*/
   while(fscanf(penv->CSV,"%s\t%s\t%lf\n",text1,text2,&time) != EOF)
   {
      infostruct->yaxistexts[counter] = bi_strdup("time in s");
      infostruct->selected_result[counter] = 1;
      infostruct->legendtexts[counter] = bi_strdup(text2);
      counter++;
   }
	fclose(penv->CSV);

   /* free all used space */
   if (penv) free(penv);
}



/** Implementation of the bi_init of the BenchIT interface.
 *  Here you have the chance to allocate the memory you need.
 *  It is also possible to allocate the memory at the beginning
 *  of every single measurment and to free the memory thereafter.
 *  But making usage always of the same memory is faster.
 *  HAVE A LOOK INTO THE HOWTO !
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

   if(iproblemsize > 1)
   {
   	if (system(pmydata->path_script) != 0)
   	{
   		fprintf(stderr,"Error: Couldn't start the script %s.", pmydata->path_script);
   		exit(1);
   	}
   }
   pmydata->CSV = fopen(pmydata->path_temp, "r");
   if(NULL == pmydata->CSV)
   {
      fprintf(stderr, "Error: Can't open the result file\n");
      exit(1);
   }

   double time,time_temp;
   double start_time = 0;
   char text1[10],text2[FUNC_NAME];
	  /* Gets the measured time of the measured Micro-Services */
	 if(fscanf(pmydata->CSV,"%s\t%s\t%lf\n",text1,text2,&time) != EOF)
	 {
	 	if(strcmp(text2,"start") == 0) // first time stamp
	 		start_time = time;
	 	else
	 	{
	 		fprintf(stderr,"\nError: No start time found\n");
	 		exit(1);
	 	}
	 }
	 else
	 {
	 	fprintf(stderr,"\nError: Empty resultfile\n");
	 	exit(1);
	 }
	 time_temp = start_time;
	 myinttype counter = 1;
	 dresults[0] = (double) iproblemsize; // measurement run id
   while(fscanf(pmydata->CSV,"%s\t%s\t%lf\n",text1,text2,&time) != EOF)
   {
		dresults[counter] = time - time_temp;
		printf("\n\n %lf,%lf,%lf \n\n",time, time_temp,dresults[counter]);
		time_temp = time;
		counter++;
   }

	fclose(pmydata->CSV);

   return 0;
}

/** Clean up the memory
 */
void bi_cleanup(void* mdpv)
{
   mydata_t * pmydata = (mydata_t*)mdpv;

   if (system("rm $BENCHIT_SPEZIAL_RESULT") != 0)
   	fprintf(stderr,"Error: Couldn't delete %s",pmydata->path_temp);
   if (pmydata) free(pmydata);

   return;
}
