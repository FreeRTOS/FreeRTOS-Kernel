cmake_minimum_required(VERSION 3.15)

project(example)

set(FREERTOS_KERNEL_PATH "../../")

# Add the freertos_config for FreeRTOS-Kernel
add_library(freertos_config INTERFACE)

target_include_directories(freertos_config
    INTERFACE
    ../sample_configuration
)

# Select the heap port.  values between 1-4 will pick a heap.
set(FREERTOS_HEAP "4" CACHE STRING "" FORCE)

# Select the native compile PORT
set(FREERTOS_PORT "TEMPLATE" CACHE STRING "" FORCE)

# Use default options by adding "-DFREERTOS_KERNEL_TOOLCHAIN=GCC" in cmake command OR
# provide your compile options by setting freertos_kernel_compile_option.
#
# An example to set freertos_kernel_compile_option in application cmake file.
# set( freertos_kernel_compile_option
#      ### Gnu/Clang C Options
#      $<$<COMPILE_LANG_AND_ID:C,GNU>:-fdiagnostics-color=always>
#      $<$<COMPILE_LANG_AND_ID:C,Clang>:-fcolor-diagnostics>

#      $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wall>
#      $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wextra>
#      $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wpedantic>
#      $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Werror>
#      $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wconversion>
#      $<$<COMPILE_LANG_AND_ID:C,Clang>:-Weverything>

#      # Suppressions required to build clean with clang.
#      $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
#      $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-padded>
#      $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-variable-declarations>
#      $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-covered-switch-default>
#      $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-align> )

# Adding the FreeRTOS-Kernel subdirectory
add_subdirectory(${FREERTOS_KERNEL_PATH} FreeRTOS-Kernel)

add_executable(${PROJECT_NAME}
    main.c
)

target_link_libraries(${PROJECT_NAME} freertos_kernel freertos_config)
