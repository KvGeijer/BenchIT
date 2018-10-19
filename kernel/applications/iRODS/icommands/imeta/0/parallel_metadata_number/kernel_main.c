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


/* Reads some environment variables used by this kernel and
   calculates some values for the measurements */
int set_inc(mydata_t * pmydata)
{
   int errors = 0;
   char * p = 0;

   p = bi_getenv("BENCHIT_KERNEL_META_INC_FUNC", 0);
   if (p == NULL)
      errors++;
   else
      pmydata->meta_func = atoi(p);
   p = bi_getenv("BENCHIT_KERNEL_META_MIN", 0);
   if (p == NULL)
      errors++;
   else
      pmydata->meta_min = atoi(p);
   p = bi_getenv("BENCHIT_KERNEL_META_MAX", 0);
   if (p == NULL)
      errors++;
   else
      pmydata->meta_max = atoi(p);

   /* Calculates the number of measurements for BENCHIT_KERNEL_FILES_INC_FUNC=0 */
   if(pmydata->meta_func == 0)
   {
      p = bi_getenv("BENCHIT_KERNEL_META_INC", 0);
      if (p == NULL)
         errors++;
      else
         pmydata->meta_inc = atoi(p);

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
   }
   /* Calculates the number of measurements for BENCHIT_KERNEL_FILES_INC_FUNC > 0 */
   else
   {
      if(pmydata->meta_min == 0)
      {
         fprintf(stderr,"\nError: BENCHIT_KERNEL_META_MIN == 0 is not allowed for BENCHIT_KERNEL_META_INC_FUNC>0\n");
         exit(1);
      }
      if(pmydata->meta_max == 0)
      {
         fprintf(stderr,"\nError: BENCHIT_KERNEL_META_MAX == 0 is not allowed for BENCHIT_KERNEL_META_INC_FUNC>0\n");
         exit(1);
      }
      /* BENCHIT_KERNEL_FILES_INC_FUNC = 1 */
      if(pmydata->meta_func == 1)
      {
         double test_value = 0.0000001;
         double exp_min = log(pmydata->meta_min) / log(2);
         double exp_max = log(pmydata->meta_max) / log(2);
         myinttype help = 1;
         if(fabs(exp_max - (double) ((myinttype) exp_max)) > test_value)
            help++;
         pmydata->steps = (myinttype) exp_max - (myinttype) exp_min + help;
      }
      /* BENCHIT_KERNEL_FILES_INC_FUNC = 2 */
      else if(pmydata->meta_func == 2)
      {
         double test_value = 0.0000001;
         double exp_min = log10(pmydata->meta_min);
         double exp_max = log10(pmydata->meta_max);
         myinttype help = 1;
         if(fabs(exp_max - (double) ((myinttype) exp_max)) > test_value)
            help++;
         pmydata->steps = (myinttype) (exp_max - exp_min) + help;
      }
      else
      {
      	fprintf(stderr,"\nError: BENCHIT_KERNEL_META_INC_FUNC -> Undefined value\n");
      	exit(1);
      }

   }

   return errors;
}

/* Reads the environment variables used by this kernel. */
void evaluate_environment(mydata_t * pmydata)
{
   int errors = 0;
   char * p = 0;

   errors += set_inc(pmydata);
   p = bi_getenv("BENCHIT_KERNEL_META_ATTRIBUTE", 0);
   if (p == NULL)
      errors++;
   else
   {
      if(atoi(p) == 0)
      	strcpy(pmydata->meta_attr,"Different Values");
      else
      	strcpy(pmydata->meta_attr,"Different Attribute Names");
   }
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
 */
void bi_getinfo(bi_info * infostruct)
{
   mydata_t * penv;
   char file_info[100];

   penv = (mydata_t *) malloc(sizeof(mydata_t));

   /* get environment variables for the kernel */
   evaluate_environment(penv);
   infostruct->codesequence = bi_strdup("start kernel; do nothing; ");
   infostruct->kerneldescription = bi_strdup("iRods (imeta): Parallel transfer for a specific amount of metadata");
   infostruct->xaxistext = bi_strdup("Number of Metadata");
   infostruct->num_measurements = penv->steps * penv->number_runs;
   infostruct->num_processes = 1;
   infostruct->num_threads_per_process = 0;
   infostruct->kernel_execs_mpi1 = 0;
   infostruct->kernel_execs_mpi2 = 0;
   infostruct->kernel_execs_pvm = 0;
   infostruct->kernel_execs_omp = 0;
   infostruct->kernel_execs_pthreads = 0;
   infostruct->numfunctions = 1;

   /* allocating memory for y axis texts and properties */
   allocYAxis(infostruct);
   /* setting up y axis texts and properties */
   infostruct->yaxistexts[0] = bi_strdup("time in s");
   infostruct->selected_result[0] = 1;

   /* setting up x axis texts and properties */
   //infostruct->base_yaxis[0] = 0; //logarythmic axis 10^x
   sprintf(file_info,"<imeta> [%s]",penv->meta_attr);
   infostruct->legendtexts[0] = bi_strdup(file_info);

 	 if(penv->meta_func != 0)
   	infostruct->base_xaxis = 10; //logarythmic axis 10^x

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

   if((pmydata->meta_min < 0) || (pmydata->meta_min > pmydata->meta_max))
   {
      fprintf(stderr,"Error: BENCHIT_KERNEL_META_MIN is not big enough or bigger than BENCHIT_KERNEL_META_MAX");
      exit(1);
   }

   int i,j;
   myinttype meta_number, min_exp, max_exp;
   /* Calculate the minimum and maximum exponent for the different logarithm. */
   if(pmydata->meta_func == 1)
   {
      min_exp = log(pmydata->meta_min) / log(2);
      max_exp = log(pmydata->meta_max) / log(2);
   }
   if(pmydata->meta_func == 2)
   {
      min_exp = log10(pmydata->meta_min);
      max_exp = log10(pmydata->meta_max);
   }

   /* Executes all different measurements */
   for(i = 0; i < pmydata->steps; i++)
   {
      meta_number = 0;
      /* Sets the new metadata number for the measurement, dependent on the defined
         Parameter BENCHIT_KERNEL_META_INC_FUNC */
      if(pmydata->meta_func == 0)
      {
         if(pmydata->meta_min == 0)
         {
            if((i == 0) || (pmydata->meta_inc==1))
               meta_number = pmydata->meta_min + 1 + (i * pmydata->meta_inc);
            else
               meta_number = pmydata->meta_min + (i * pmydata->meta_inc);
         }
         else
            meta_number = pmydata->meta_min + (i * pmydata->meta_inc);
      }
      if(pmydata->meta_func == 1)
      {
         if(i == 0)
            meta_number = pmydata->meta_min;
         else
            meta_number = pow(2,min_exp + i);
      }
      if(pmydata->meta_func == 2)
      {
         if(i == 0)
            meta_number = pmydata->meta_min;
         else
            meta_number = pow(10,min_exp + i);
      }
      if(pmydata->meta_max < meta_number)
      	meta_number = pmydata->meta_max;

      char help[50];
      sprintf(help,"$BENCHIT_SPEZIAL_SCRIPT %d",meta_number);
     /* Executes all repetitions of one measurement */
	   for(j = 0; j < pmydata->number_runs; j++)
	   {
     	fprintf(stdout,"\n\t\t<<<< Metadata: %d , Run: %d >>>>\n", meta_number, (j + 1));
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
	 /* Gets the results of the result file */
   if(fscanf(pmydata->CSV,"%lf;%lf;%lf\n",&time_real,&time_user,&time_system) != EOF)
   {
      if(fscanf(pmydata->CSV,"%d\n",&value) != EOF)
      dresults[0] = (double) value; // number metadata
      dresults[1] = time_real; // time
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
