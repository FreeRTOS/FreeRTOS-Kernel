cmake_minimum_required(VERSION 3.12)
 
add_library(FreeRTOS list.c queue.c tasks.c timers.c event_groups.c)

include_directories(AFTER include)
