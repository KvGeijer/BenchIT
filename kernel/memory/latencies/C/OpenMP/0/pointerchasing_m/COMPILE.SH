#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: COMPILE.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/memory/latencies/C/0/0/pointerchasing/COMPILE.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Kernel: Memory Access Time (C)
#####################################################################

# If it's not set, the user
# executed this script directly so we need to call top script
if [ -z "${BENCHIT_COMPILE_SH_IS_CALLED}" ]; then
   # Go to COMPILE.SH directory
   cd `dirname ${0}` || exit 1

   # compile using global script
   ../../../../../../../COMPILE.SH `pwd`
   exit 0
fi


LOCAL_KERNEL_COMPILER="C"
LOCAL_KERNEL_COMPILERFLAGS="-DBENCHIT_KERNEL_USE_HUGE_PAGES=${BENCHIT_KERNEL_USE_HUGE_PAGES} ${BENCHIT_CC_C_FLAGS_OMP}"
LOCAL_KERNEL_FILES="pointerchasing_init.c pointerchasing_entry.c pointerchasing_accesses.c"

LOCAL_MODULE_FILES=""

LOCAL_BENCHIT_COMPILER="C"
LOCAL_BENCHIT_COMPILERFLAGS="-DERROR_CORRECTION=100"

LOCAL_LINKERFLAGS="${BENCHIT_CC_C_FLAGS_OMP}"

if [ -z "${BENCHIT_KERNEL_USE_NUMA_NODE}" ]; then
   echo "Compiling without NUMA support, you can still use numactl"
else
    LOCAL_KERNEL_COMPILERFLAGS="-DBENCHIT_KERNEL_USE_NUMA_NODE=${BENCHIT_KERNEL_USE_NUMA_NODE} ${LOCAL_KERNEL_COMPILERFLAGS}"
    LOCAL_LINKERFLAGS="${LOCAL_LINKERFLAGS} -lnuma"
fi
