#!/bin/bash
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# For license details see COPYING in the package base directory
#####################################################################
# All kernels in kernel will be compiled and executed.
# You should have edited the c compiler part in your LOCALDEF
# in a proper way before this.
#####################################################################

set -euo pipefail

### variables and helpers

# change to BenchIT folder
cd "`dirname $0`/.."

BITPATH=`pwd`				# path to BenchIT root
KERNELPATH=${BITPATH}/kernel	# path to kernels
BINPATH=${BITPATH}/bin		    # path to kernel binaries
LOG=${BITPATH}/RUNALL.log
# number of errors
COMPILE_ERRORS=0
RUN_ERRORS=0

prepare()
{
  echo -e "\033[1;32mSTAGE 0: preparing...\033[0m"
  rm -rf ${BINPATH}/*		# necessary cleanup

  echo "### BenchIT Test Run ###" > ${LOG}
  echo "Date: `date`" >> ${LOG}
  echo "-----------------------------" >> ${LOG}
}

compile()
{
  echo -e "\033[1;32mSTAGE 1: compiling...\033[0m"
  echo "Compiler warnings/errors per kernel" >> ${LOG}

  for i in `find ${KERNELPATH} -name PARAMETERS`; do
    folder=`dirname $i`
	  echo ${folder} >> ${LOG}
	  echo "Compiling ${folder}"
    set +e
    # Stderr to Stdout (variable and tee), Stdout and Stderr (from tee) to LOG
	  errOutput="$(./COMPILE.SH ${folder} 2>&1 >>${LOG} | tee --append ${LOG})"
	  result=$?
	  set -e
	  if [ $result -ne 0 ]; then
		  echo -e "\033[1;31mError during compilation of $folder!\033[0m" >&2
	    echo "$errOutput"
		  COMPILE_ERRORS=$((COMPILE_ERRORS+1))
	  fi
  done
}

run()
{
  echo -e "\033[1;32mSTAGE 2: running...\033[0m"
  echo "Status information to kernel runs:" >> ${LOG}

  for i in `ls ${BINPATH}`; do
    tmp=${i//./}
    lenI=${#i}
    lenTmp=${#tmp}
    if [ $((lenTmp-lenI)) -lt 4 ]; then
      continue
    fi
	  echo "##### $i #####" >> ${LOG}
	  echo "Running $i"
	  set +e
    # Stderr to Stdout (variable and tee), Stdout and Stderr (from tee) to LOG
	  errOutput="$(./RUN.SH ${BINPATH}/$i 2>&1 >>${LOG} | tee --append ${LOG})"
	  result=$?
	  set -e
	  if [ $result -ne 0 ]; then
		  echo -e "\033[1;31mError during execution of $i!\033[0m" >&2
	    echo "$errOutput"
		  RUN_ERRORS=$((RUN_ERRORS+1))
	  fi
  done
}

finish()
{
  echo -e "\033[1;32mSTAGE 3: Finished...\033[0m"
  if [ ${COMPILE_ERRORS} -gt 0 ] || [ ${RUN_ERRORS} -gt 0 ]; then
    echo "There were ${COMPILE_ERRORS} compile errors and ${RUN_ERRORS} run errors!" >> ${LOG}
    echo -e "\033[1;31mThere were ${COMPILE_ERRORS} compile errors and ${RUN_ERRORS} run errors!\033[0m" >&2
    result=1
  else
    echo -e "\033[1;32mAll completed successfully\033[0m"
    result=0
  fi

  exit $result
}

prepare
compile
#run
finish

