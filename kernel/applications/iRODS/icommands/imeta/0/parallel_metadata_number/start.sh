#! /bin/sh

# $1 = Increment of the number of files

BENCHIT_KERNEL_NUMBER_META=$1
FILE=$BENCHIT_RESULT_NAME
SPECIAL="meta_benchit"
SUBDIR="benchit_subdir"
IRODS_RESOURCE=""
PATH_TEMP=$BENCHIT_KERNEL_PATH_TEMP
PATH_SCRIPT=$KERNELDIR
BOOL=1

if [ "$BENCHIT_IRODS_RESC" != "" ]
then
	IRODS_RESOURCE="-R $BENCHIT_IRODS_RESC"
fi

# Creates new files if they not already exist and transfers them to iRODS
mkdir $PATH_TEMP/$SUBDIR
PATH_TEMP="$PATH_TEMP/$SUBDIR/"
imkdir $SUBDIR
dd if=/dev/urandom of="$PATH_TEMP/$SPECIAL" bs=100K count=1 2>/dev/null
if [ $? -ne 0 ]
then
	BOOL=0
fi     
iput $IRODS_RESOURCE -f "$PATH_TEMP/$SPECIAL" $SUBDIR 1>/dev/null
if [ $? -ne 0 ]
then
	BOOL=0
fi

# If no error happened, the measurement begins
if [ $BOOL -ne 1 ] 
then
	echo "Error: No files created\n" 1>&2
else
  echo "All files created."
  echo "Start to set metadata."   
 	#time: real_time;user_time;system_time
	$BENCHIT_TOOL_TIME -f "%e;%U;%S" -o "$BENCHIT_KERNEL_PATH_TEMP/$FILE" -a $PATH_SCRIPT/irods_parallel.sh "$SUBDIR/$SPECIAL" "$BENCHIT_KERNEL_NUMBER_META" "$BENCHIT_KERNEL_META_ATTRIBUTE"
	echo "$1" >> "$BENCHIT_KERNEL_PATH_TEMP/$FILE"
fi

# Clean up
echo "Remove temporary files."
rm -r "$PATH_TEMP" 
irm -fr $SUBDIR 2>/dev/null
if [ $? -ne 0 ]
then
	sleep 3
	irm -fr $SUBDIR
fi


wait
