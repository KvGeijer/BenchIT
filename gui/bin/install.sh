#!/bin/sh
###############################################################################
#
#  B e n c h I T - Performance Measurement for Scientific Applications
#
#  Shell script, installing the gui
#
#  Author: SWTP Nagel 1
#  Last change by: $Author: domke $
#  $Revision: 1.2 $
#  $Date: 2008/05/29 12:06:07 $
#
###############################################################################
echo "###### installing ######"

cd `dirname ${0}`
if [ ! -d ../build ]; then
  echo "build folder not found"
  exit
fi
cd ../build

rm -f BenchIT.jar
echo "Manifest-Version: 1.0" > MANIFEST.SF
echo "Main-Class: BIGMain" >> MANIFEST.SF
echo "Class-Path: ." >> MANIFEST.SF
echo "Built-By: $USER" >> MANIFEST.SF

for file in `find ../lib -name "*.jar"`; do
  jar xf $file
done
rm -f META-INF/*.SF

echo "###### packaging ######"
jar cfm ../bin/BenchIT.jar MANIFEST.SF *

cd ..
rm -rf ./build

echo "###### done       ######"
###############################################################################
#  Log-History
#
###############################################################################
