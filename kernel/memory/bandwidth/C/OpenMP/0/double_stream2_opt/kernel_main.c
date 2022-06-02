
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
/*  Header for local functions
 */
#include "work.h"

/* aligned memory allocation */
#include <errno.h>
#include <stddef.h> /* ptrdiff_t */
#include <stdint.h> /* uintptr_t */

#define NOT_POWER_OF_TWO(n) (((n) & ((n) - 1)))
#define UI(p) ((uintptr_t) p)

/*  Header for local functions
 */
void evaluate_environment(void);
void *_aligned_malloc(size_t size, size_t alignment);
void _aligned_free(void *memblock);
/*
  aligned alloc/free
*/

static void *ptr_align(void *p0, size_t alignment, size_t offset)
{
     return (void *) (((UI(p0) + (alignment + sizeof(void*)) + offset)
		       & (~UI(alignment - 1)))
		       - offset);
}


void *_aligned_offset_malloc(size_t size, size_t alignment, size_t offset)
{
    void *p0, *p;
    if (NOT_POWER_OF_TWO(alignment)) {
        errno = EINVAL;
	return((void*) 0);
    }
    if (size == 0)
	return((void*) 0);
    if (alignment < sizeof(void *))
	alignment = sizeof(void *);
/* including the extra sizeof(void*) is overkill on a 32-bit
    machine, since malloc is already 8-byte aligned, as long
    as we enforce alignment >= 8 ...but oh well */
    p0 = (void*) malloc(size + (alignment + sizeof(void*)));
    if (!p0)
	return((void*) 0);
    p = ptr_align(p0, alignment, offset);
    *(((void **) p) - 1) = p0;
    return p;
}

void *_aligned_malloc(size_t size, size_t alignment)
{
    return _aligned_offset_malloc(size, alignment, 0);
}

void _aligned_free(void *memblock)
{
    if (memblock)
	free(*(((void **) memblock) - 1));
}

/**
* this defines the number of works. There'll be 4 copy, scale, add, triad
**/

int functionCount=4;

/**
* minlength: minimal length to measure (defined in parameters)
* maxlength: maximal length to measure (defined in parameters)
* accessstride: used to calculate the problemSizes between
* internal_repeats: additional repeats (defined in parameters,
*                   multiplies with BENCHIT_ACCURACY)
* offset: offset for memory access (defined in parameters)
* alignment: alignment for memory (defined in parameters)
* nMeasurements: number of problemSizes measured (defined in parameters)
* localAlloc: whether to handle memory local to threads
* threadPinning: whether to pin threads to cores
**/

unsigned long long minlength, maxlength;
long accessstride,internal_repeats,offset,alignment,
     nMeasurements, localAlloc, threadPinning;

/**
* dMemFactor: used to calculate the problemSizes
* minTimeForOneMeasurement: minimal time allowed for one benchmark
*                           (defined in parameters)
**/

double dMemFactor,minTimeForOneMeasurement;


/**  The implementation of the bi_getinfo from the BenchIT interface.
 *   Here the infostruct is filled with information about the
 *   kernel.
 *   @param infostruct  a pointer to a structure filled with zeros
 */
void bi_getinfo(bi_info * infostruct)
{
  char buf[200];
  char buf2[200];
   int i = 0; /* loop var for functionCount */
   /* get environment variables for the kernel */
   evaluate_environment();

   sprintf(buf2,"STREAM inspired benchmark (C+OpenMP)#"
               "OFFSET=%i#"
               "ALIGNMENT=%i#"
               "NTIMES=%i#"
               "THREADS=%i#"
#ifdef BENCHIT_KERNEL_ENABLE_ALIGNED_ACCESS
		           "pragma vector aligned enabled#"
#else
		           "pragma vector aligned disabled#"
#endif
#ifdef BENCHIT_KERNEL_ENABLE_NONTEMPORAL_STORES
		           "pragma vector nontemporal enabled#"
#else
		           "pragma vector nontemporal disabled#"
#endif
               ,
               (int)offset,
               (int)alignment,
               (int)internal_repeats,
               (int)omp_get_max_threads());


				if (localAlloc){
					sprintf(buf,"%slocal alloc#",buf2);
				} else{
					sprintf(buf,"%sglobal alloc#",buf2);
				}
				if (threadPinning){
					sprintf(buf2,"%sthread pinning enabled",buf);
				} else{
					sprintf(buf2,"%sthread pinning disabled",buf);
				}
   infostruct->codesequence = bi_strdup(buf2);
   infostruct->xaxistext = bi_strdup("Used Memory in kByte");
   infostruct->num_measurements = nMeasurements;
   infostruct->num_processes = 1;
   infostruct->num_threads_per_process = omp_get_max_threads();
   infostruct->kernel_execs_mpi1 = 0;
   infostruct->kernel_execs_mpi2 = 0;
   infostruct->kernel_execs_pvm = 0;
   infostruct->kernel_execs_omp = 1;
   infostruct->kernel_execs_pthreads = 0;
   infostruct->numfunctions = functionCount;
   infostruct->base_xaxis = 10;

   /* allocating memory for y axis texts and properties */
   allocYAxis(infostruct);
   /* setting up y axis texts and properties */
   for (i=0;i<infostruct->numfunctions;i++){
      infostruct->yaxistexts[i] = bi_strdup("Bandwidth in GByte/s");
      infostruct->selected_result[i] = 0;
      infostruct->base_yaxis[i] = 10;
   }
            infostruct->legendtexts[3] =
               bi_strdup("Bandwidth Sum");
            infostruct->legendtexts[2] =
               bi_strdup("Bandwidth DAXPY");
            infostruct->legendtexts[1] =
               bi_strdup("Bandwidth Copy");
            infostruct->legendtexts[0] =
               bi_strdup("Bandwidth Fill");
   if (DEBUGLEVEL > 3)
   {
      /* the next for loop: */
      /* this is for your information only and can be ereased if the kernel works fine */
      for (i = 0; i < infostruct->numfunctions; i++)
      {
         printf("yaxis[%2d]=%s\t\t\tlegend[%2d]=%s\n",
            i, infostruct->yaxistexts[i], i, infostruct->legendtexts[i]);
      }
   }
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
   mydata_t* mdp;
   mdp = (mydata_t*)malloc(sizeof(mydata_t));
   if (mdp == 0)
   {
      fprintf(stderr, "Allocation of structure mydata_t failed\n"); fflush(stderr);
      exit(127);
   }
   /* malloc our own arrays in here */
   mdp->a=(double**)malloc(sizeof(double*)*omp_get_max_threads());
   if (mdp->a==0)
   {
      fprintf(stderr, "Allocation of structure a failed\n"); fflush(stderr);
      exit(127);
   }
   mdp->b=(double**)malloc(omp_get_max_threads()*sizeof(double*));
   if (mdp->b==0)
   {
      fprintf(stderr, "Allocation of structure b failed\n"); fflush(stderr);
      exit(127);
   }
   /* allocate memory on the correct threads! */
   #pragma omp parallel
   {
      double * a;
      double * b;
      long long mask;
      unsigned long long i;
      int num;
      num=omp_get_thread_num();
#ifdef BENCHIT_KERNEL_COMPILE_FOR_PIN_THREADS_TO_CORES
    if(threadPinning){
      /* pin to correct core */
      mask=1<<num;
      sched_setaffinity(0,sizeof(long long),&mask);
      /* done pinning to correct core */
    }
#endif
    if (localAlloc||(num==0)){
       /* allocating memory local to thread or using memory from thread 0 */
        mdp->a[num]=_aligned_malloc((maxlength+offset)*sizeof(double),alignment);
        a =mdp->a[num];
        IDL(2,printf ("Thread %i/%i: allocated a:%i\n",
                      (int)omp_get_thread_num(),
                      (int)omp_get_num_threads(),
                      (int)(maxlength+offset)));
        if (a==0){
          fprintf(stderr, "Allocation of structure a[%i] failed\n",num);
          fflush(stderr);
          exit(127);
        }
        mdp->b[num]=_aligned_malloc((maxlength/2+offset)*sizeof(double),alignment);
        b=mdp->b[num];
        IDL(2,printf ("Thread %i/%i: allocated b:%i\n",
                      (int)omp_get_thread_num(),
                      (int)omp_get_num_threads(),
                      (int)(maxlength/2+offset)));
        if (b==0){
          fprintf(stderr, "Allocation of structure b[%i] failed\n",num);
          fflush(stderr);
          exit(127);
        }
        for (i=0;i<maxlength+offset;i++) a[i]=1.0;
        for (i=0;i<maxlength/2+offset;i++) b[i]=2.0;
      }
   }
   /*########################################################*/
   return (void*)mdp;
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
 */
int bi_entry(void* mdpv, int problemsize, double* results)
{
  double time[4][internal_repeats];
  double best[4];
  /* gbpersec stores the calculated GB/s */
  double gbpersec = 0.0;
  int k=0;
  /* j is used for loop iterations */
  int j = 0;
  /* helps to gain accuracy for minimal time for one measurement */
  long long repeats=1;
  /* cast void* pointer */
  mydata_t* mdp = (mydata_t*)mdpv;
  /* shorten names */
	double** a=mdp->a;
	double** b=mdp->b;
	double scalar=3.0;
	double result;
	unsigned long long numberOfMovedDoubles=0;
	/* calculating problemsize for this run */
  numberOfMovedDoubles=(unsigned long long)(((double)minlength)*pow(dMemFactor, (problemsize-1)));
  numberOfMovedDoubles-=(numberOfMovedDoubles%(6*omp_get_max_threads()*8));
  if (numberOfMovedDoubles == 0) {
    numberOfMovedDoubles=6*omp_get_max_threads()*8;
  }
   IDL(3,printf ("current number of moved doubles:%lluu\n",
                    numberOfMovedDoubles));
  /* check wether the pointer to store the results in is valid or not */
  if (results == NULL) return 1;
  /* do the measurement */
	for (k=0;k<internal_repeats;k++)
	{
      IDL(3,printf ("start fill"));
	  /* measure copy, unless it needs more then the minimal time,
	     always increasing the number of repititions */
	  do{
        time[0][k]=fill_(a,scalar,numberOfMovedDoubles,offset,repeats,localAlloc,threadPinning);
        repeats=repeats*10;
        // check whether overflow
        if (repeats<0) break;
	  }while(time[0][k]<minTimeForOneMeasurement);
    repeats=repeats/10;
	  time[0][k]=time[0][k]/repeats;
      IDL(3,printf ("start copy"));
	  /* use the (now higher) number of repitions for all other measurements  */
	  do{
        time[1][k]=copy_(b,a,numberOfMovedDoubles/2,offset,repeats,localAlloc,threadPinning);
        repeats=repeats*10;
        // check whether overflow
        if (repeats<0) break;
	  }while(time[1][k]<minTimeForOneMeasurement);
    repeats=repeats/10;
	  time[1][k]=time[1][k]/repeats;
      IDL(3,printf ("start daxpy"));

	  do{
        time[2][k]=daxpy_(b,a,scalar,numberOfMovedDoubles/3,offset,repeats,localAlloc,threadPinning);
        repeats=repeats*10;
        // check whether overflow
        if (repeats<0) break;
	  }while(time[2][k]<minTimeForOneMeasurement);
    repeats=repeats/10;
	  time[2][k]=time[2][k]/repeats;
      IDL(3,printf ("start sum"));
	  do{
        time[3][k]=sum_(a,&result,numberOfMovedDoubles,offset,repeats,localAlloc,threadPinning);
        repeats=repeats*10;
        // check whether overflow
        if (repeats<0) break;
	  }while(time[3][k]<minTimeForOneMeasurement);
    repeats=repeats/10;
	  time[3][k]=time[3][k]/repeats;
      IDL(3,printf ("done"));
  }
  /* calculating the best time of all internal repititions */
  best[0]=time[0][0];
  best[1]=time[1][0];
  best[2]=time[2][0];
  best[3]=time[3][0];
  for (j=0;j<4;j++)
  for (k=1;k<internal_repeats;k++)
  {
  	if (best[j]>(time[j][k]))
  		best[j]=time[j][k];
  }
  /* store the problemsize */
  results[0] = (1.0*numberOfMovedDoubles*sizeof(double))/1000.0;
  if (localAlloc)
    results[0] *= omp_get_max_threads();
   IDL(3,printf ("current problemsize:%e\n",
                  results[0]));
  for (j = 0; j < functionCount; j++)
  {
    /* remember resuls[0] is in kByte */
    gbpersec = (1.0E-6*results[0])/(best[j]);
    if(gbpersec <=0.0) gbpersec = INVALID_MEASUREMENT;
    // store the results
    results[j + 1] = gbpersec;
  }
  return 0;
}

/** Clean up the memory
 */
void bi_cleanup(void* mdpv)
{
   mydata_t* mdp = (mydata_t*)mdpv;
   int i=0;
   // free a and its sub-arrays
   if (mdp->a!=0){
     for (i=0;i<omp_get_max_threads();i++){
       if (mdp->a[i]!=0)
         _aligned_free(mdp->a[i]);
     }
     free(mdp->a);
   }
   // free b and its sub-arrays
   if (mdp->b!=0){
     for (i=0;i<omp_get_max_threads();i++){
       if (mdp->b[i]!=0)
         _aligned_free(mdp->b[i]);
     }
     free(mdp->b);
   }
   // free structure
   if (mdp) free(mdp);
   return;
}

/* Reads the environment variables used by this kernel. */
void evaluate_environment()
{
  char *envir;
  IDL(3,printf("Init global variables ... "));
  envir=bi_getenv("BENCHIT_KERNEL_MIN_ACCESS_LENGTH",1);
  if (envir==0)
  {
  	printf("BENCHIT_KERNEL_MIN_ACCESS_LENGTH not found! Exiting");
  	exit(127);
  }
  minlength=(atoi(envir)*1000)/(sizeof(double));
  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_MAX_ACCESS_LENGTH",1);
  if (envir==0)
  {
  	printf("BENCHIT_KERNEL_MAX_ACCESS_LENGTH not found! Exiting");
  	exit(127);
  }
  maxlength=(atoi(envir)*1000)/(sizeof(double));
  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_ACCESS_STEPS",1);
  if (envir==0)
  {
  	printf("BENCHIT_KERNEL_ACCESS_STEPS not found! Exiting");
  	exit(127);
  }
  nMeasurements =atoi(envir);
  dMemFactor =((double)maxlength)/((double)minlength);
  dMemFactor = pow(dMemFactor, 1.0/((double)nMeasurements-1));
  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_INTERNAL_NUM_MEASUREMENT",1);
  if (envir==NULL)
  {
  	printf("BENCHIT_KERNEL_INTERNAL_NUM_MEASUREMENT not found! Using 1");
    internal_repeats=1;
  }
  else
    internal_repeats=atoi(envir);

  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_OFFSET",1);
  if (envir==NULL)
  {
  	printf("BENCHIT_KERNEL_OFFSET not found! Using 0");
    offset=0;
  }
  else
    offset=atoi(envir);
  if (offset%8!=0){
    offset=(offset-offset%8)/8;
  	printf("BENCHIT_KERNEL_OFFSET is not a multiple of 8! Using %i instead.",
  	        (int)offset);
  }

  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_ALIGNMENT_BORDER",1);
  if (envir==NULL)
  {
  	printf("BENCHIT_KERNEL_ALIGNMENT_BORDER not found! Using 128 byte");
  	alignment=128;
  }
  else
    alignment=atoi(envir);

  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_MIN_TIME_FOR_ONE_MEASUREMENT",1);
  if (envir==NULL)
  {
  	printf("BENCHIT_KERNEL_MIN_TIME_FOR_ONE_MEASUREMENT not found! Using 10 microseconds");
  	minTimeForOneMeasurement=1.0E-5;
  } else
    minTimeForOneMeasurement=atoi(envir)*1.0E-6;

  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_LOCAL_ALLOC",1);
  if (envir==NULL)
  {
  	printf("BENCHIT_KERNEL_LOCAL_ALLOC not found! Allocating local (default)");
  	localAlloc=1;
  } else
    localAlloc=atoi(envir);
  envir=0;
  envir=bi_getenv("BENCHIT_KERNEL_PIN_THREADS_TO_CORES",1);
  if (envir==NULL)
  {
  	printf("BENCHIT_KERNEL_PIN_THREADS_TO_CORES not found! No thread pinning");
  	threadPinning=0;
  } else
    threadPinning=atoi(envir);

  if(localAlloc){
	  minlength=(1.0*minlength)/(1.0*omp_get_max_threads());
	  maxlength=(1.0*maxlength)/(1.0*omp_get_max_threads());
  }
  IDL(3,printf("done\n"));
}
