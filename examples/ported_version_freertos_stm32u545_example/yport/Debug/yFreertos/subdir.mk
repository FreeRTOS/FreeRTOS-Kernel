################################################################################
# Automatically-generated file. Do not edit!
# Toolchain: GNU Tools for STM32 (12.3.rel1)
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
C_SRCS += \
../yFreertos/croutine.c \
../yFreertos/event_groups.c \
../yFreertos/list.c \
../yFreertos/queue.c \
../yFreertos/stream_buffer.c \
../yFreertos/tasks.c \
../yFreertos/timers.c \
../yFreertos/yash.c 

OBJS += \
./yFreertos/croutine.o \
./yFreertos/event_groups.o \
./yFreertos/list.o \
./yFreertos/queue.o \
./yFreertos/stream_buffer.o \
./yFreertos/tasks.o \
./yFreertos/timers.o \
./yFreertos/yash.o 

C_DEPS += \
./yFreertos/croutine.d \
./yFreertos/event_groups.d \
./yFreertos/list.d \
./yFreertos/queue.d \
./yFreertos/stream_buffer.d \
./yFreertos/tasks.d \
./yFreertos/timers.d \
./yFreertos/yash.d 


# Each subdirectory must supply rules for building sources it contributes
yFreertos/%.o yFreertos/%.su yFreertos/%.cyclo: ../yFreertos/%.c yFreertos/subdir.mk
	arm-none-eabi-gcc "$<" -mcpu=cortex-m33 -std=gnu11 -g -DDEBUG -DUSE_HAL_DRIVER -DSTM32U545xx -c -I../Core/Inc -I"C:/Users/DELL/Downloads/yport/yport/yFreertos" -I"C:/Users/DELL/Downloads/yport/yport/yFreertos/include" -I"C:/Users/DELL/Downloads/yport/yport/yFreertos/portable/GCC/ARM_CM33_NTZ/non_secure" -I"C:/Users/DELL/Downloads/yport/yport/yFreertos/portable/MemMang" -I../Drivers/STM32U5xx_HAL_Driver/Inc -I../Drivers/STM32U5xx_HAL_Driver/Inc/Legacy -I../Drivers/CMSIS/Device/ST/STM32U5xx/Include -I../Drivers/CMSIS/Include -O0 -ffunction-sections -fdata-sections -Wall -fstack-usage -fcyclomatic-complexity -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" --specs=nano.specs -mfpu=fpv5-sp-d16 -mfloat-abi=hard -mthumb -o "$@"

clean: clean-yFreertos

clean-yFreertos:
	-$(RM) ./yFreertos/croutine.cyclo ./yFreertos/croutine.d ./yFreertos/croutine.o ./yFreertos/croutine.su ./yFreertos/event_groups.cyclo ./yFreertos/event_groups.d ./yFreertos/event_groups.o ./yFreertos/event_groups.su ./yFreertos/list.cyclo ./yFreertos/list.d ./yFreertos/list.o ./yFreertos/list.su ./yFreertos/queue.cyclo ./yFreertos/queue.d ./yFreertos/queue.o ./yFreertos/queue.su ./yFreertos/stream_buffer.cyclo ./yFreertos/stream_buffer.d ./yFreertos/stream_buffer.o ./yFreertos/stream_buffer.su ./yFreertos/tasks.cyclo ./yFreertos/tasks.d ./yFreertos/tasks.o ./yFreertos/tasks.su ./yFreertos/timers.cyclo ./yFreertos/timers.d ./yFreertos/timers.o ./yFreertos/timers.su ./yFreertos/yash.cyclo ./yFreertos/yash.d ./yFreertos/yash.o ./yFreertos/yash.su

.PHONY: clean-yFreertos

