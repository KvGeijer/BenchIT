#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: COMPILE.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/applications/MGV/F95/OpenMP/MathKeisan/recursive/COMPILE.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Kernel: multigrid methode for 2D Poisson equation
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

LOCAL_MathKeisan="-lparblas"
export LOCAL_MathKeisan

LOCAL_KERNEL_COMPILER="F95"
LOCAL_KERNEL_COMPILERFLAGS="${BENCHIT_F95_C_FLAGS_OMP}"
LOCAL_KERNEL_FILES="2dPoisson.f90"

LOCAL_MODULE_FILES="kernel_main.c"

LOCAL_BENCHIT_COMPILER="C"
LOCAL_BENCHIT_COMPILERFLAGS="${BENCHIT_CC_C_FLAGS_OMP}"

LOCAL_LINKERFLAGS="${BENCHIT_F95_C_FLAGS_OMP} ${LOCAL_MathKeisan}"

BENCHIT_COMMENT="multigrid methode for 2D Poisson equation"
export BENCHIT_COMMENT
