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

// For the thread pinning
#include <sched.h>
#include <pthread.h>


#define ONE {ptr=(void **) *ptr;}
#define TEN ONE ONE ONE ONE ONE ONE ONE ONE ONE ONE
#define HUN TEN TEN TEN TEN TEN TEN TEN TEN TEN TEN
#define THO HUN HUN HUN HUN HUN HUN HUN HUN HUN HUN


extern long numjumps;
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


// Pin the unbound thread to a specific hardware thread
void pin_thread(int cpu_use)
{
  // WARNING: Requires _GNU_SOURCE to have been defined during compilation with flag -D_GNU_SOURCE
  cpu_set_t mask;
  CPU_ZERO(&mask);
  CPU_SET(cpu_use, &mask);
  pthread_t thread = pthread_self();
  if (pthread_setaffinity_np(thread, sizeof(cpu_set_t), &mask) != 0)
  {
          fprintf(stderr, "Error setting thread affinity\n");
  }
}

typedef struct {
  void* mcb;
  long njumps;
} targs_t;

void modify_linked_memory(void* vargs)
{
  targs_t* args = vargs;
  long njumps = args->njumps;
  void** start = args->mcb;
  void** current = start;

  pin_thread(11);

  for (int jump = 0; jump < njumps; jump++) {
    // Take modified ownership of current, should not be optimized away
    void** volatile at = current;
    *current = *at;
    
    // Follow the pointer to the next one
    current = (void **) *current;


    // Repeat until we have wrapped around the memory, or jumped as many times as the test will
    if (current == start) break;
  } 
}


// Spawn another thread to take the memory, then wait for it to finish
void transfer_linked_memory(void* mcb, long njumps)
{
  pthread_t tid;
  targs_t args = {.mcb = mcb, .njumps = njumps};
  pthread_create(&tid, NULL, modify_linked_memory, &args);
  pthread_join(tid, NULL);
}


int bi_entry(void *mcb,int problemSize,double *results) {

	static double timeroh=0, calloh=0;
	double start, stop;
	int i;

	long length;
	long long c[4];
	void *ptr;

	extern double dMemFactor;
	extern long minlength;

	length = (long)(((double)minlength)*pow(dMemFactor, (problemSize-1)));

	results[0]=(double) length;

  // Use thread 1 as default, as 0 is often used a bit by OS
  pin_thread(1);

	IDL(2, printf("Making structure\n"));
	make_linked_memory(mcb, length);
  IDL(2, printf("Enter measurement\n"));

  // Here we could have another thread call jump_around. Then that thread would read it into its cache and we could see core-to-core transfers.
  // To also specify the cache lines, we could have the other thread also write to the memory or similar? (How would this work? Can we just write the same value twice?).
  // We should probably replce the call below with the new thread!

  // Following the strategy from https://ieeexplore.ieee.org/document/5260544:
  //     1) thread 0: warm-up TLB
  //     2) if (N>0): sync of thread 0 and N
  //     3) thread N: access data (-> E/M/S)
  //     4) if (N>0): sync of thread 0 and N
  //     5) all threads: flush caches (optional)
  //     6) thread 0: measure latency
  //
  // So add steps 2 - 4 by spawning another thread to manipulate the data
  // according to the cache mode wanted (start with just modified or exclusive).


  
	// ptr = jump_around(mcb, numjumps);

  transfer_linked_memory(mcb, numjumps);
  
	start=bi_gettime();
	// if ((long)ptr == 0)
		// printf("#");


	jump_around(mcb, numjumps);

	stop=bi_gettime();

	IDL(2, printf("Done\n"));

	 results[1]=(double)(stop-start)/((double)numjumps);


  return (0);
}
