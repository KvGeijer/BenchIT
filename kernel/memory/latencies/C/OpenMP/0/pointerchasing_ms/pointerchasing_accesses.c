/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: pointerchasing_accesses.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/memory/latencies/C/0/0/pointerchasing/pointerchasing_accesses.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Kernel: Memory Access Time (C)
 *******************************************************************/
#include <stdatomic.h>

#define ONE_W { ptr=(volatile void **)atomic_fetch_or_explicit(ptr,ormask,memory_order_seq_cst);}

#define ONE {ptr=(void **) *ptr;}

void *jump_around(void *mem, long n) {
  void **ptr;
  long a;


  ptr=(void **) mem;

  /* numjump Sprnge im Kreis :-) */
  for(a=0; a<n; a++) {
    ONE
      }
  return (void *) ptr;
}
void *jump_around_w(volatile void **mem, long n) {
  volatile void **ptr;
  long a;
  unsigned long long ormask=0x0;

  ptr=(volatile void **) mem;

  /* numjump Sprnge im Kreis :-) */
  for(a=0; a<n; a++) {
    ONE_W
      }
  return (void *) ptr;
}
