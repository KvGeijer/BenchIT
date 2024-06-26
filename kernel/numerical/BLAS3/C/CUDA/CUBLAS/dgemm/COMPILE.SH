#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: COMPILE.SH 1 2011-01-27 fschmitt $
# $URL: svn+ssh://benchit@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/numerical/BLAS3/C/CUDA/CUBLAS/sgemm/COMPILE.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Kernel: Measurement of Nvidia CUBLAS sgemm performance
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

LOCAL_KERNEL_COMPILER="CXX"
LOCAL_KERNEL_COMPILERFLAGS=""
LOCAL_KERNEL_FILES="kernel_main.c"

LOCAL_MODULE_FILES="empty.c"


LOCAL_LINKERFLAGS="-lcublas -lcudart"
