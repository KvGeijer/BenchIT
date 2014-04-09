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
for file in `find ../lib -name "*.jar"`; do
  jar xf $file
done
rm -f META-INF/*.SF
mkdir -p META-INF
echo "Manifest-Version: 1.0" > META-INF/MANIFEST.SF
echo "Main-Class: BIGMain" >> META-INF/MANIFEST.SF
echo "Class-Path: ." >> META-INF/MANIFEST.SF
echo "Built-By: $USER" >> META-INF/MANIFEST.SF


echo "###### packaging ######"
jar cf ../bin/BenchIT.jar *

cd ..
rm -rf ./build

echo "###### done       ######"
###############################################################################
#  Log-History
#
###############################################################################
