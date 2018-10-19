/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: kernel_main.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/numerical/cannon/F95/MPI/0/double/kernel_main.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: a MPI version of matrix-matrix multiplication
 *         (cannon algotithm)
 *******************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <mpi.h>

#include "cannon.h"
#include "matrix.h"
#include "mpicomm.h"
#include "interface.h"

#define NUM_FUNC 6

/* Reads the environment variables used by this kernel. */
void evaluate_environment(mydata_t * pmydata) {
   int errors = 0;
   char *p = 0;

   p = bi_getenv("BENCHIT_KERNEL_OUTPUT", 0);
   if (p == NULL)
      errors++;
   else
      pmydata->output = atoi(p);

   if (errors > 0) {
      fprintf(stderr, "There's at least one environment variable not set!\n");
      exit(1);
   }
}

/**  The implementation of the bi_getinfo from the BenchIT interface.
 *   Here the infostruct is filled with information about the
 *   kernel.
 *   @param infostruct  a pointer to a structure filled with zeros
 */
void bi_getinfo(bi_info * infostruct) {
   myinttype ii;
   char *p = 0;
   mydata_t *penv;

   penv = (mydata_t *) malloc(sizeof(mydata_t));

   /* get environment variables for the kernel */
   /* parameter list */
   p = bi_getenv("BENCHIT_KERNEL_PROBLEMLIST", 0);
   bi_parselist(p);
   /* additional parameters */
   evaluate_environment(penv);

   infostruct->codesequence =
      bi_strdup
      ("generate matries; multiply matries, communicate, multiply, comm...");
   infostruct->kerneldescription = bi_strdup("cannon algorithm");
   infostruct->xaxistext = bi_strdup("Matrix Size");
   infostruct->num_measurements = infostruct->listsize;
   infostruct->num_processes = 1;
   infostruct->num_threads_per_process = 0;
   infostruct->kernel_execs_mpi1 = 1;
   infostruct->kernel_execs_mpi2 = 0;
   infostruct->kernel_execs_pvm = 0;
   infostruct->kernel_execs_omp = 0;
   infostruct->kernel_execs_pthreads = 0;
   infostruct->numfunctions = NUM_FUNC;

   /* allocating memory for y axis texts and properties */
   allocYAxis(infostruct);
   /* setting up y axis texts and properties */
   for (ii = 0; ii < NUM_FUNC; ii++) {
      if (penv->output) {
         infostruct->yaxistexts[ii] = bi_strdup("s");
         infostruct->selected_result[ii] = 1;
         infostruct->base_yaxis[ii] = 10;   // logarythmic axis 10^x
         switch (ii) {
            case 0:
               infostruct->legendtexts[ii] = bi_strdup("time in s (ijk)");
               break;
            case 1:
               infostruct->legendtexts[ii] = bi_strdup("time in s (ikj)");
               break;
            case 2:
               infostruct->legendtexts[ii] = bi_strdup("time in s (jik)");
               break;
            case 3:
               infostruct->legendtexts[ii] = bi_strdup("time in s (jki)");
               break;
            case 4:
               infostruct->legendtexts[ii] = bi_strdup("time in s (kij)");
               break;
            case 5:
               infostruct->legendtexts[ii] = bi_strdup("time in s (kji)");
               break;
         }
      } else {
         infostruct->yaxistexts[ii] = bi_strdup("flop/s");
         infostruct->selected_result[ii] = 0;
         infostruct->base_yaxis[ii] = 0;    // logarythmic axis 10^x
         switch (ii) {
            case 0:
               infostruct->legendtexts[ii] = bi_strdup("FLOPS (ijk)");
               break;
            case 1:
               infostruct->legendtexts[ii] = bi_strdup("FLOPS (ikj)");
               break;
            case 2:
               infostruct->legendtexts[ii] = bi_strdup("FLOPS (jik)");
               break;
            case 3:
               infostruct->legendtexts[ii] = bi_strdup("FLOPS (jki)");
               break;
            case 4:
               infostruct->legendtexts[ii] = bi_strdup("FLOPS (kij)");
               break;
            case 5:
               infostruct->legendtexts[ii] = bi_strdup("FLOPS (kji)");
               break;
         }
      }
   }

   /* free all used space */
   if (penv)
      free(penv);
}

/** Implementation of the bi_init of the BenchIT interface.
 *  Here you have the chance to allocate the memory you need.
 *  It is also possible to allocate the memory at the beginning
 *  of every single measurment and to free the memory thereafter.
 *  But making usage always of the same memory is faster.
 *  HAVE A LOOK INTO THE HOWTO !
 */
void *bi_init(int problemsizemax) {
   mydata_t *pmydata;

   pmydata = (mydata_t *) malloc(sizeof(mydata_t));
   if (pmydata == 0) {
      fprintf(stderr, "Allocation of structure mydata_t failed\n");
      fflush(stderr);
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
 */
int bi_entry(void *mdpv, int iproblemsize, double *dresults) {
   /* dstart, dend: the start and end time of the measurement */
   /* dtime: the time for a single measurement in seconds */
   double dstart[NUM_FUNC], dend[NUM_FUNC], dtime[NUM_FUNC];
   /* flops stores the calculated FLOPS */
   double dres = 0.0;
   /* pointer_array to the different functions (in this case the different
    * permutation of the loops) */
   /* mult..._ the "_" for the fortran calling */
   void (*ptr_to_perm[]) (DT * matrixS, DT * matrixA, DT * matrixB, int *mA,
                          int *nA, int *nB) = {multijk_, multikj_, multjik_,
                                               multjki_, multkij_, multkji_ };

   int mA, nA, mB, nB, _mA, _nA, _mB, _nB, _mS, _nS, temp, i, j, k;
   int cpu_x = 0, cpu_y = 0;
   float fac;
   DT *matrixA, *matrixB, *matrixS;
   DT **pointer;
   GridPosition gridpos;

   int temprank, resultsender;
   MPI_Status status;

   /* cast void* pointer */
   mydata_t *pmydata = (mydata_t *) mdpv;
   myinttype imyproblemsize = (myinttype) iproblemsize;

   MPI_Comm_rank(MPI_COMM_WORLD, &globalrank);
   MPI_Comm_size(MPI_COMM_WORLD, &globalsize);

   /* initialize the random generator for each processor */
   srand((unsigned int)globalrank * 111);

   IDL(3, printf("\nrank=%d entered bi_entry\n", globalrank));

   /* calculate real problemsize */
   imyproblemsize = (myinttype) bi_get_list_element(iproblemsize);
   mA = imyproblemsize;
   nA = imyproblemsize;
   mB = imyproblemsize;
   nB = imyproblemsize;

   /* there are max. mA*nB processors, and the number squared */
   createMyMPIComm(globalsize, mA, nB);

   /* check wether the pointer to store the results in is valid or not */
   if (globalrank == 0) {
      if (dresults == NULL) {
         fprintf(stderr, "\nrank=%d resultpointer not allocated - panic\n",
                 globalrank);
         fflush(stderr);
         return 1;
      }
   }

   /* x*y cpu, x per row, y per column */
   fac = (float)mA / (float)nB;
   IDL(INFO, printf("\nfactor: %e", fac));
   cpu_x = ceil(sqrt(size) * fac);
   cpu_y = ceil(sqrt(size) / fac);
   IDL(INFO, printf("\n1. cpu per row: %i", cpu_x));
   IDL(INFO, printf("\n1. cpu per column: %i", cpu_y));

   while (1) {
      if (cpu_y < cpu_x) {
         if (cpu_x * cpu_y <= size) {
            break;
         } else {
            cpu_x--;
         }
      } else {
         if (cpu_x * cpu_y <= size) {
            break;
         } else {
            cpu_y--;
         }
      }
   }

   IDL(INFO, printf("\n2. cpu per row: %i", cpu_x));
   IDL(INFO, printf("\n2. cpu per column: %i", cpu_y));

   temp = 0;
   for (i = 0; i < cpu_y; i++) {
      for (j = 0; j < cpu_x; j++) {
         if (rank == temp) {
            gridpos.row = j;
            gridpos.column = i;
         }
         temp++;
      }
   }

   _mA = ceil(mA / (float)cpu_x);
   if ((gridpos.row % cpu_x) == cpu_x - 1) {
      _mA = mA - (cpu_x - 1) * _mA;
   }

   _nA = ceil(nA / (float)cpu_y);
   if ((gridpos.column % cpu_y) == cpu_y - 1) {
      _nA = nA - (cpu_y - 1) * _nA;
   }

   _mB = ceil(mB / (float)cpu_x);
   if ((gridpos.row % cpu_x) == cpu_x - 1) {
      _mB = mB - (cpu_x - 1) * _mB;
   }

   _nB = ceil(nB / (float)cpu_y);
   if ((gridpos.column % cpu_y) == cpu_y - 1) {
      _nB = nB - (cpu_y - 1) * _nB;
   }

   IDL(INFO,
       printf("\nrank=%i  _mA=%i, _nA=%i  _mB=%i, _nB=%i  gridpos=(%i, %i)",
              rank, _mA, _nA, _mB, _nB, gridpos.row, gridpos.column));

   /* get the actual time do the measurement / your algorythm get the actual
    * time */
   if (rank != MPI_UNDEFINED) {
      matrixA = createMatrix(_mA, _nA);
      matrixB = createMatrix(_mB, _nB);

      IDL(INFO, MPI_Barrier(mycomm));
      initRandomMatrix(matrixA, _mA, _nA);
      IDL(INFO, MPI_Barrier(mycomm));
      IDL(INFO, printf("Random MatrixA:\n"));
      IDL(INFO, printMatrix(matrixA, _mA, _nA));

      IDL(INFO, MPI_Barrier(mycomm));
      initRandomMatrix(matrixB, _mB, _nB);
      IDL(INFO, MPI_Barrier(mycomm));
      IDL(INFO, printf("Random MatrixB:\n"));
      IDL(INFO, printMatrix(matrixB, _mB, _nB));

      pointer =
         initialShift(matrixA, &(_mA), &(_nA), matrixB, &(_mB), &(_nB), gridpos,
                      cpu_x, cpu_y);
      if (pointer[0] != NULL)
         matrixA = pointer[0];
      if (pointer[1] != NULL)
         matrixB = pointer[1];
      free(pointer);

      for (k = 0; k < NUM_FUNC; k++) {
         _mS = _mA;
         _nS = _nB;
         matrixS = createMatrix(_mS, _nS);
         initZERO(matrixS, _mS, _nS);

         MPI_Barrier(mycomm);
         dstart[k] = bi_gettime();
         pointer =
            MatxMat(matrixS, &(_mS), &(_nS), matrixA, &(_mA), &(_nA), matrixB,
                    &(_mB), &(_nB), gridpos, cpu_x, cpu_y, &(*ptr_to_perm[k]));
         MPI_Barrier(mycomm);
         dend[k] = bi_gettime();
         if (pointer[0] != NULL)
            matrixA = pointer[0];
         if (pointer[1] != NULL)
            matrixB = pointer[1];
         free(pointer);

         clearMatrix(matrixS);
      }
      pointer =
         undoShift(matrixA, &(_mA), &(_nA), matrixB, &(_mB), &(_nB), gridpos,
                   cpu_x, cpu_y);
      if (pointer[0] != NULL)
         matrixA = pointer[0];
      if (pointer[1] != NULL)
         matrixB = pointer[1];
      free(pointer);

      clearMatrix(matrixA);
      clearMatrix(matrixB);
   }

   /* sometimes globalrank 0 is not rank 0 and so the dstart/dend are invalid */
   if (globalrank == 0) {
      for (k = 1; k < globalsize; k++) {
         MPI_Recv(&temprank, 1, MPI_INT, k, tag, MPI_COMM_WORLD, &status);
         if (temprank == 0)
            resultsender = k;
      }
   } else {
      MPI_Send(&rank, 1, MPI_INT, 0, tag, MPI_COMM_WORLD);
   }

   if (globalrank == 0 && rank != 0) {
      MPI_Recv(dstart, NUM_FUNC, MPI_DOUBLE, resultsender, tag, MPI_COMM_WORLD,
               &status);
      MPI_Recv(dend, NUM_FUNC, MPI_DOUBLE, resultsender, tag, MPI_COMM_WORLD,
               &status);
   }

   if (rank == 0 && globalrank != 0) {
      MPI_Send(dstart, NUM_FUNC, MPI_DOUBLE, 0, tag, MPI_COMM_WORLD);
      MPI_Send(dend, NUM_FUNC, MPI_DOUBLE, 0, tag, MPI_COMM_WORLD);
   }

   if (globalrank == 0) {
      /* calculate the FLOPS */
      dres = 2 * (1.0 * mA) * (1.0 * mA) * (1.0 * mA);

      /* calculate the used time */
      for (k = 0; k < NUM_FUNC; k++) {
         dtime[k] = dend[k] - dstart[k];
         dtime[k] -= dTimerOverhead;

         /* If the operation was too fast to be measured by the timer function,
          * mark the result as invalid */
         if (dtime[k] < dTimerGranularity)
            dtime[k] = INVALID_MEASUREMENT;
      }

      /* store the results in results[1], results[2], ... * [1] for the first
       * function, [2] for the second function * and so on ... * the index 0
       * always keeps the value for the x axis */
      dresults[0] = (double)imyproblemsize;
      if (pmydata->output) {
         for (k = 0; k < NUM_FUNC; k++) {
            dresults[k + 1] = dtime[k];
         }
      } else {
         for (k = 0; k < NUM_FUNC; k++) {
            dresults[k + 1] =
               (dtime[k] != INVALID_MEASUREMENT) ? dres / dtime[k] :
               INVALID_MEASUREMENT;
         }
      }
   }

   freeMyMPIComm();

   return 0;
}

/** Clean up the memory
 */
void bi_cleanup(void *mdpv) {
   mydata_t *pmydata = (mydata_t *) mdpv;
   if (pmydata)
      free(pmydata);
   return;
}
