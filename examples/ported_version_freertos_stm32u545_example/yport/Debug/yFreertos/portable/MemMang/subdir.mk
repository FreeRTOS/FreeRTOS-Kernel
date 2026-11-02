################################################################################
# Automatically-generated file. Do not edit!
# Toolchain: GNU Tools for STM32 (12.3.rel1)
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
C_SRCS += \
../yFreertos/portable/MemMang/heap_4.c 

OBJS += \
./yFreertos/portable/MemMang/heap_4.o 

C_DEPS += \
./yFreertos/portable/MemMang/heap_4.d 


# Each subdirectory must supply rules for building sources it contributes
yFreertos/portable/MemMang/%.o yFreertos/portable/MemMang/%.su yFreertos/portable/MemMang/%.cyclo: ../yFreertos/portable/MemMang/%.c yFreertos/portable/MemMang/subdir.mk
	arm-none-eabi-gcc "$<" -mcpu=cortex-m33 -std=gnu11 -g -DDEBUG -DUSE_HAL_DRIVER -DSTM32U545xx -c -I../Core/Inc -I"C:/Users/DELL/Downloads/yport/yport/yFreertos" -I"C:/Users/DELL/Downloads/yport/yport/yFreertos/include" -I"C:/Users/DELL/Downloads/yport/yport/yFreertos/portable/GCC/ARM_CM33_NTZ/non_secure" -I"C:/Users/DELL/Downloads/yport/yport/yFreertos/portable/MemMang" -I../Drivers/STM32U5xx_HAL_Driver/Inc -I../Drivers/STM32U5xx_HAL_Driver/Inc/Legacy -I../Drivers/CMSIS/Device/ST/STM32U5xx/Include -I../Drivers/CMSIS/Include -O0 -ffunction-sections -fdata-sections -Wall -fstack-usage -fcyclomatic-complexity -MMD -MP -MF"$(@:%.o=%.d)" -MT"$@" --specs=nano.specs -mfpu=fpv5-sp-d16 -mfloat-abi=hard -mthumb -o "$@"

clean: clean-yFreertos-2f-portable-2f-MemMang

clean-yFreertos-2f-portable-2f-MemMang:
	-$(RM) ./yFreertos/portable/MemMang/heap_4.cyclo ./yFreertos/portable/MemMang/heap_4.d ./yFreertos/portable/MemMang/heap_4.o ./yFreertos/portable/MemMang/heap_4.su

.PHONY: clean-yFreertos-2f-portable-2f-MemMang

