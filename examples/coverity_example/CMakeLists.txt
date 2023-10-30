cmake_minimum_required(VERSION 3.15)

project(example)

set(FREERTOS_KERNEL_PATH "../../")
FILE( GLOB FREERTOS_KERNEL_SOURCE ${FREERTOS_KERNEL_PATH}*.c )

# pdTRUE and pdFALSE will be regarded as boolean type by naming convention
# which Coverity uses to determine the intent. However, boolean type is not used 
# in FreeRTOS to support compiler of older standard. Replace pdTRUE with pdPASS
# and pdFALSE with pdFAIL in this example to suppress this false positive warning.
add_custom_target( fix_source ALL 
    COMMAND sed -i -b -e 's/pdFALSE/pdFAIL/g' -e 's/pdTRUE/pdPASS/g' ${FREERTOS_KERNEL_SOURCE}
    DEPENDS ${FREERTOS_KERNEL_SOURCE})

# Add the freertos_config for FreeRTOS-Kernel
add_library(freertos_config INTERFACE)

target_include_directories(freertos_config
    INTERFACE
    ./configuration
)

# Select the heap port.  values between 1-4 will pick a heap.
set(FREERTOS_HEAP "4" CACHE STRING "" FORCE)

# Select the native compile PORT
set(FREERTOS_PORT "TEMPLATE" CACHE STRING "" FORCE)

# Adding the FreeRTOS-Kernel subdirectory
add_subdirectory(${FREERTOS_KERNEL_PATH} FreeRTOS-Kernel)

add_executable(${PROJECT_NAME}
    ../cmake_example/main.c
)
add_dependencies(${PROJECT_NAME} fix_source)

target_link_libraries(${PROJECT_NAME} freertos_kernel freertos_config)
