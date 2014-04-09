#!/bin/sh
###############################################################################
#
#  B e n c h I T - Performance Measurement for Scientific Applications
#
#  Shell script, compiling the gui
#
#  Author: SWTP Nagel 1
#  Last change by: $Author: domke $
#  $Revision: 1.2 $
#  $Date: 2008/05/29 12:06:07 $
#
###############################################################################
echo "###### compiling  ######"

OLDDIR="${PWD}"
cd `dirname ${0}`/../src

jarFiles=
for file in `find ../lib -name "*.jar"`; do
  jarFiles="$jarFiles:$file"
done

javaFiles=
for file in `find . -name "*.java"`; do
  javaFiles="$javaFiles $file"
done

mkdir -p ../bin/class
rm -rf ../bin/class/*
javac -classpath ".:$jarFiles" -d ../bin/class $javaFiles
#*.java admin/*.java com/twmacinta/util/*.java com/twmacinta/io/*.java conn/*.java generated/org/benchit/bitconnect/service/types/*.java generated/org/benchit/bitconnect/service/*.java gui/*.java org/benchit/bitconnect/*.java org/benchit/bitconnect/gui/*.java org/syntax/jedit/*.java org/syntax/jedit/tokenmarker/*.java plot/data/*.java plot/gui/*.java reportgen/*.java system/*.java
../bin/install.sh

cd "${PWD}"
echo "###### done       ######"
###############################################################################
#  Log-History
#
###############################################################################
