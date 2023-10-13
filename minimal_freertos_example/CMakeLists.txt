cmake_minimum_required(VERSION 3.15)

set(PROJECT_NAME example)

project(${PROJECT_NAME})

set(FREERTOS_KERNEL_PATH "../")

# Add the freertos_config for FreeRTOS-Kernel
add_library(freertos_config INTERFACE)

target_include_directories(freertos_config
    INTERFACE
    ./
    ../sample_configuration
)

# Select the heap port.  values between 1-4 will pick a heap.
# set(FREERTOS_HEAP "40" CACHE STRING "" FORCE)

# Select the native compile PORT
set(FREERTOS_PORT "TEMPLATE" CACHE STRING "" FORCE)

# bring in the kernel
#add_subdirectory(${FREERTOS_KERNEL_PATH})

# Adding the FreeRTOS-Kernel subdirectory
add_subdirectory(${FREERTOS_KERNEL_PATH} ${CMAKE_CURRENT_BINARY_DIR}/FreeRTOS-Kernel)

add_executable(${PROJECT_NAME}
    main.c
)

target_include_directories(${PROJECT_NAME}
    PRIVATE
    ${CMAKE_CURRENT_LIST_DIR}
)

target_link_libraries(${PROJECT_NAME} freertos_kernel freertos_config)