#!/bin/zsh
ps -o comm= -p $$

CURRENT_DIR=`pwd`
DEMO_DIR="../demos/FreeRTOS-SMP-Demos/FreeRTOS/Demo/CORTEX_M0+_RP2040"
LOG_DIR="`pwd`/build_logs"
BUILD_LOG="$LOG_DIR/build_log--`date +'%y_%m_%d--%H_%M'`.txt"

export CC=/usr/bin/clang
export CQQ=/usr/bin/clang++

mkdir $LOG_DIR
cd $DEMO_DIR
rm -rf build
mkdir build
cd build
cmake .. &>$BUILD_LOG
echo "\ncmake finished\n"

make VERBOSE=1 &>>$BUILD_LOG

echo "\nmake finished\n"
