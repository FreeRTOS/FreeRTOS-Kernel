# FreeRTOS ported version for stm32u545re microcontroller (Cortex-M33)

## This repository provides a minimal and working FreeRTOS port for the STM32U545RE microcontroller based on the ARM Cortex-M33 core.

## It is intended as a clean starting point for developers building low-power IoT and embedded applications on STM32U5 devices.

#### Example is simple switching between two tasks on serial monitor.

## porting procedure: 
#### 1. modified systick handler to generate time slice with respect to cortex m33 processor.
#### 2. modified pendSV handler to perform context switching between tasks with respect to cortex m33 processor.
#### 3. modified supervisor call handler to determine which os service is requested to cortex m33 processor.