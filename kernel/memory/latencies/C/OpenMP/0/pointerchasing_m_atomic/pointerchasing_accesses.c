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

#define ONE { ptr=(volatile void **)atomic_fetch_or_explicit(ptr,ormask,memory_order_seq_cst);}
#define TEN ONE ONE ONE ONE ONE ONE ONE ONE ONE ONE
#define HUN TEN TEN TEN TEN TEN TEN TEN TEN TEN TEN
#define THO HUN HUN HUN HUN HUN HUN HUN HUN HUN HUN

void *jump_around(volatile void **mem, long n) {
  volatile void **ptr;
  long a;
  unsigned long long ormask=0x0;


  ptr=(volatile void **)atomic_fetch_or_explicit(mem,ormask,memory_order_seq_cst);

  /* numjump Sprnge im Kreis :-) */
  for(a=0; a<n-2; a++) {
    ONE
      }
  ptr=(volatile void **)atomic_fetch_or_explicit(ptr,ormask,memory_order_seq_cst);
  return (void *) ptr;
}
