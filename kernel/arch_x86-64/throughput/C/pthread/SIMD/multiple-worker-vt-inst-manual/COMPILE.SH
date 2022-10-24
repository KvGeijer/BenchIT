#!/bin/sh
##################################################################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id$
# For license details see COPYING in the package base directory
##################################################################################################################

# If kernel name string is set, this COMPILE.SH is sourced
# from the global COMPILE.SH. If it is not set, the user
# executed this script directly so we need to call configure.
if [ -z "${BENCHIT_KERNELNAME}" ]; then
	# Go to COMPILE.SH directory
	cd `dirname ${0}` || exit 1

	# Set configure mode
	CONFIGURE_MODE="COMPILE"

	# Load the definitions
	. ../../../../../../../tools/configure
fi

# check whether compilers and libraries are available
if [ -z "${BENCHIT_CC}" ]; then
	echo "No C compiler specified - check \$BENCHIT_CC"
	exit 1
fi

BENCHIT_KERNEL_COMMENT="throughput of SIMD instructions"
export BENCHIT_KERNEL_COMMENT

# the compiler and its flags for the benchit.c
LOCAL_BENCHITC_COMPILER="${KERNEL_CC} ${BENCHIT_CC_C_FLAGS} ${BENCHIT_CC_C_FLAGS_STD} ${BENCHIT_DEFINES}"
# the compiler for the measurement kernel
LOCAL_KERNEL_COMPILER="C"
# the compilerflags for the measurement kernel
LOCAL_KERNEL_COMPILERFLAGS="${BENCHIT_CC_C_FLAGS} -DNOPCOUNT=${BENCHIT_KERNEL_NOPCOUNT} -DLINE_PREFETCH=${BENCHIT_KERNEL_LINE_PREFETCH} ${BENCHIT_CC_C_FLAGS_HIGH} ${BENCHIT_INCLUDES} -I${BENCHITROOT}/tools/hw_detect"
# the linkerflags
if [ "${BENCHIT_LIB_PTHREAD}" = "" ]; then
 BENCHIT_LIB_PTHREAD="-lpthread"
fi
LOCAL_LINKERFLAGS="${BENCHIT_CC_L_FLAGS} ${BENCHIT_LIB_PTHREAD} -lnuma"

if [ "$BENCHIT_KERNEL_ENABLE_PAPI" = "1" ]; then
 LOCAL_KERNEL_COMPILERFLAGS="${LOCAL_KERNEL_COMPILERFLAGS} -DUSE_PAPI -I${PAPI_INC}"
 LOCAL_LINKERFLAGS="${LOCAL_LINKERFLAGS} -L${PAPI_LIB} -lpapi"
fi

if [ "$BENCHIT_KERNEL_ENABLE_PAPI" = "2" ]; then
 LOCAL_KERNEL_COMPILERFLAGS="${LOCAL_KERNEL_COMPILERFLAGS} -DUSE_PAPI -DPAPI_UNCORE -I${PAPI_INC}"
 LOCAL_LINKERFLAGS="${LOCAL_LINKERFLAGS} -L${PAPI_LIB} -lpapi"
fi

if [ "$BENCHIT_KERNEL_SERIALIZATION" = "cpuid" ]; then
 LOCAL_KERNEL_COMPILERFLAGS="${LOCAL_KERNEL_COMPILERFLAGS} -DFORCE_CPUID"
fi

if  [ "$BENCHIT_KERNEL_SERIALIZATION" = "mfence" ]; then
 LOCAL_KERNEL_COMPILERFLAGS="${LOCAL_KERNEL_COMPILERFLAGS} -DFORCE_MFENCE"
fi

if [ "$BENCHIT_KERNEL_REGONLY" = "1" ]; then
 LOCAL_KERNEL_COMPILERFLAGS="${LOCAL_KERNEL_COMPILERFLAGS} -DREGONLY"
fi

# COMPILER-variables should appear in resultfile...
export LOCAL_BENCHITC_COMPILER LOCAL_KERNEL_COMPILER LOCAL_KERNEL_COMPILERFLAGS LOCAL_LINKERFLAGS

# ENVIRONMENT HASHING - creates bienvhash.c
cd ${BENCHITROOT}/tools/
set > tmp.env
./fileversion >> tmp.env
./envhashbuilder
cd ${KERNELDIR}

LOCAL_KERNEL_FILES="arch.c kernel_main.c work.c"

LOCAL_MODULE_FILES="${BENCHITROOT}/tools/hw_detect/x86.c ${BENCHITROOT}/tools/hw_detect/generic.c ${BENCHITROOT}/tools/hw_detect/properties.c"
