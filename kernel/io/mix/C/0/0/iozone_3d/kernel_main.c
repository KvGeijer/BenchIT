/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: kernel_main.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/io/mix/C/0/0/iozone_3d/kernel_main.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "interface.h"
#include "kernel_main.h"
#include <unistd.h>
#include "tools/error.h"

#define NR_FCT 14 //reclen + 13 io functions
#define MAX_LINE_LENGTH 255


int do_iozone();

/* from work.h */
mydata_t* mdp;
//list_t * listhead;

unsigned long inputlinecount = 0;

void assert_mdp(){
   if (mdp == NULL) mdp = (mydata_t*)malloc(sizeof(mydata_t));
   if (mdp == NULL){
      fprintf(stderr, "Allocation of structure mydata_t failed\n");
      fflush(stderr);
      exit(ENOMEM);
   }
}


/* Reads the environment variables used by this kernel. */
void evaluate_environment(){
    int inumentries = 0;
    int ii = 0;
    char * p;
    char unit;
    assert_mdp();

    mdp->filesize_max_unit = (char *)malloc(1);

    mdp->filename = bi_getenv("BENCHIT_KERNEL_FILENAME", 1);
    mdp->filesize_max = bi_getenv("BENCHIT_KERNEL_FILESIZE_MAX", 1);
    mdp->max = (unsigned int)strtol(mdp->filesize_max, &(mdp->filesize_max_unit), 10);
    mdp->cachelinesize = bi_getenv("BENCHIT_KERNEL_CACHELINE_SIZE", 1);
    mdp->cachesize = bi_getenv("BENCHIT_KERNEL_CACHE_SIZE", 1);
    mdp->options = bi_getenv("BENCHIT_KERNEL_OPTIONS", 1);

    unit=*(mdp->filesize_max_unit);
    switch (unit){
        case 'k':
             ii=1;
             break;
        case 'm':
             ii=1024;
             break;
        case 'g':
             ii=1048576;
             break;
        default:
             exit(BENVUNKNOWN);
             break;
    }
    mdp->max = mdp->max * ii;

//    printf("min=%lu max=%lu inc=%lu\n", mdp->min, mdp->max, mdp->inc);

//    mdp->testarray = (unsigned int *)malloc(sizeof(unsigned int) * NR_FCT);
}



void bi_getinfo(bi_info * infostruct)
{
   int i = 0, j = 0, iswitch=0;
   /* get environment variables for the kernel */
   printf("\nHello You there\n");
   evaluate_environment();
   infostruct->codesequence = bi_strdup("iozone");
   infostruct->xaxistext = bi_strdup("size of file");
//   infostruct->num_measurements = inputlinecount; //(mdp->max - mdp->min+1)/mdp->inc;
//   if((mdp->max - mdp->min+1) % mdp->inc != 0)
//     infostruct->num_measurements++;
   infostruct->num_processes = 1;
   infostruct->num_threads_per_process = 0;
//   infostruct->base_xaxis = 0;

   infostruct->kernel_execs_mpi1 = 0;
   infostruct->kernel_execs_mpi2 = 0;
   infostruct->kernel_execs_pvm = 0;
   infostruct->kernel_execs_omp = 0;
   infostruct->kernel_execs_pthreads = 0;
   infostruct->numfunctions = NR_FCT;

   /* allocating memory for y axis texts and properties */
   allocYAxis(infostruct);
   /* setting up y axis texts and properties */
    j=0;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("reclen");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("write");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("rewrite");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("read");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("reread");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("random read");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("random write");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("read backwarts");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("rewrite record");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("stride read");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("fwrite");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("frewrite");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("fread");
    j++;

    infostruct->yaxistexts[j] = bi_strdup("Bytes/s");
    infostruct->selected_result[j] = 0;
    infostruct->base_yaxis[j] = 0;
    infostruct->legendtexts[j] = bi_strdup("freread");
    j++;

   infostruct->numfunctions = j;

   if (DEBUGLEVEL > 3){
      for (i = 0; i < infostruct->numfunctions; i++){
         printf("yaxis[%2d]=%s\t\t\tlegend[%2d]=%s\n",
            i, infostruct->yaxistexts[i], i, infostruct->legendtexts[i]);
      }
   }
   //printf("\nstarting iozone to get to know number of values\n");
   do_iozone();
   infostruct->num_measurements = inputlinecount;
   printf("\niozone finished, exiting bi_getinfo\n");
   printf("infostruct->num_measurements: %lu\n", infostruct->num_measurements);
}



void* bi_init(int problemsizemax){
		char filenamestring[STRINGSIZE];

    assert_mdp();
    return (void*)mdp;

    /* clean up resultoutputfile */
    system("rm -f iozone.out");

    /* clean up outputfile */
    sprintf(filenamestring,"rm -f %s", mdp->filename);
    system(filenamestring);
}


int do_iozone(){
    char command[STRINGSIZE];
    char inputline[MAX_LINE_LENGTH+1];
    int ii=0, ret=0;
    FILE * ptr;
    char * input1;
    char * input2;
    unsigned long value;

    /* assemble iozone-call */
    snprintf(command, STRINGSIZE, "./bin/iozone -a -g %s -S %s -L %s %s -f %s | tee iozoneresults.txt",
    mdp->filesize_max,
    mdp->cachesize,
    mdp->cachelinesize,
    mdp->options,
    mdp->filename);
    printf("command: %s\n", command);

    if ((ptr = popen(command, "r")) != NULL){
       while (fgets(inputline, MAX_LINE_LENGTH, ptr) != NULL){
       printf(inputline);
       inputlinecount++;
//       printf("\ninputlinecount = %lu", inputlinecount);
       }
    }
    popen("sync", "r");
    (void) pclose(ptr);

    return ret;
}

int bi_entry(void* mdpv, int problemsize, double* results){
    int ii=0, ret=0, j=1;
    unsigned long filesize;
    char * p;
    FILE * ptr;
    char * input1;
    char * input2;
    char * inputline;
    unsigned long value;


    printf("\nbi_entry, problemsize=%i", problemsize);
    if (results == NULL) exit(ENOMEM);
    inputline = (char *) malloc((MAX_LINE_LENGTH + 1) * sizeof(char));
    memset(inputline, 0, MAX_LINE_LENGTH + 1);

    if ((ptr = fopen("iozoneresults.txt", "r")) != NULL){
        /* skip the header */
        while ((fgets(inputline, MAX_LINE_LENGTH, ptr) != NULL) && (strstr(inputline, "KB") == NULL)) {
//            printf(inputline);
        }
//        printf("\nI've skipped the header\n");

        /* skip forwarMPIF
        for(ii=0; ii<pMPIF
            if (fgets(MPIF
                ret=1;MPIF
                printf("\nskipping forward to the actual line [FAILED]");
                break;
            }
        }
        /* check wether we have a sane value */
        if (ret != 0){
            printf("\nskipping forward to the actual line [FAILED] - no sane value");
            return 0;
        }

        ii=0;
        input1 = inputline;
        value = (unsigned long)strtol(input1, &input2, 10);
        results[ii] = (double)(value*1024);
        ii++;
        while ((input2 != NULL) && (value != 0)){
            input1 = input2;
            value = (unsigned long)strtol(input1, &input2, 10);
            results[ii] = (double)(value*1024);
            ii++;
        }

        printf("\n problemsize %i, nr_elements %i, results:\n", problemsize, ii);
        for (j=0; j<ii; j++) printf("%f ",results[j]);
        printf("\n");

    }

    fclose(ptr);
    free(inputline);
    return 0;
}

/** Clean up the memory
 */
void bi_cleanup(void* mdpv)
{
   mydata_t* mdp = (mydata_t*)mdpv;
   if (mdp) free(mdp);
   return;
}
