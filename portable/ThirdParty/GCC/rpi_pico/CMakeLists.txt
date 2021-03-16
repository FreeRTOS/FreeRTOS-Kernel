cmake_minimum_required(VERSION 3.12)
 
add_library(FreeRTOS_port port.c)

include_directories(AFTER ../../../include)
