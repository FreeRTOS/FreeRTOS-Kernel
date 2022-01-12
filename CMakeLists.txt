cmake_minimum_required(VERSION 3.12)

set(CMAKE_TRY_COMPILE_TARGET_TYPE "STATIC_LIBRARY")

project(FreeRTOS-Kernel)

list(APPEND CMAKE_MESSAGE_CONTEXT "FreeRTOS-Kernel")

add_library(FreeRTOS-Kernel OBJECT)

# Optional parameters.
option(FREERTOS_KERNEL_USE_CUSTOM_PORT "Enable the use of a custom port implementation from a different project. When enabling this option set <FREERTOS_KERNEL_PORT> to the path that contains port files." OFF)
option(FREERTOS_KERNEL_USE_CUSTOM_HEAP "Enable the use of a custom heap implementation from a different project. When enabling this option set <FREERTOS_KERNEL_HEAP_FILE> to the file that implements the memory management." OFF)

## FreeRTOS Kernel Config ##
# Check that <FREERTOS_KERNEL_CONFIG> contains FreeRTOSConfig.h
if(NOT DEFINED FREERTOS_KERNEL_CONFIG)
    message(FATAL_ERROR "<FREERTOS_KERNEL_CONFIG> is undefined. Set <FREERTOS_KERNEL_CONFIG> to the path that contains FreeRTOSConfig.h.")
else()
    if(NOT EXISTS "${FREERTOS_KERNEL_CONFIG}/FreeRTOSConfig.h")
        message(FATAL_ERROR "FreeRTOSConfig.h not found in ${FREERTOS_KERNEL_CONFIG}. Set <FREERTOS_KERNEL_CONFIG> to the path that contains FreeRTOSConfig.h.")
    endif()
endif ()

## FreRTOS Kernel Port ##
if(FREERTOS_KERNEL_USE_CUSTOM_PORT)
    # If a custom port is being used then check that <FREERTOS_KERNEL_PORT> contains a valid directory.
    if(NOT DEFINED FREERTOS_KERNEL_PORT)
        message(FATAL_ERROR "<FREERTOS_KERNEL_PORT> is undefined. When using a custom port set <FREERTOS_KERNEL_PORT> to the path that contains the port source files.")
    else()
        if(NOT EXISTS "${FREERTOS_KERNEL_PORT}")
            message(FATAL_ERROR "Custom port folder: ${FREERTOS_KERNEL_PORT} does not exist.")
        endif()
    endif()
else()
    # If using a default port then check the compiler ID identified by CMake and set the port folder accordingly.
    if(${CMAKE_C_COMPILER_ID} STREQUAL "ARMClang")
        set(FREERTOS_COMPILER_PORT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/portable/ARMClang")
    elseif(${CMAKE_C_COMPILER_ID} STREQUAL "Bruce")
        set(FREERTOS_COMPILER_PORT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/portable/BCC/16BitDOS")
    elseif(${CMAKE_C_COMPILER_ID} STREQUAL "GNU")
        set(FREERTOS_COMPILER_PORT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/portable/GCC")
    elseif(${CMAKE_C_COMPILER_ID} STREQUAL "IAR")
        set(FREERTOS_COMPILER_PORT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/portable/IAR")
    elseif(${CMAKE_C_COMPILER_ID} STREQUAL "MSVC")
        set(FREERTOS_COMPILER_PORT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/portable/MSVC-MingW")
    elseif(${CMAKE_C_COMPILER_ID} STREQUAL "OpenWatcom")
        set(FREERTOS_COMPILER_PORT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/portable/oWatcom/16BitDOS")
    elseif(${CMAKE_C_COMPILER_ID} STREQUAL "SDCC")
        set(FREERTOS_COMPILER_PORT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/portable/SDCC")
    else()
        message(FATAL_ERROR "The C compiler identification is ${CMAKE_C_COMPILER_ID}. No port is available for this compiler. Check your toolchain configuration or set <FREERTOS_KERNEL_USE_CUSTOM_PORT> to use a custom FreeRTOS port.")
    endif()
    message(VERBOSE "The C compiler identification is: ${CMAKE_C_COMPILER_ID}. Compiler port folder is: ${FREERTOS_COMPILER_PORT_DIRECTORY}")

    # Search the port folder for available port configurations.
    file(GLOB PORTS RELATIVE "${FREERTOS_COMPILER_PORT_DIRECTORY}" CONFIGURE_DEPENDS "${FREERTOS_COMPILER_PORT_DIRECTORY}/*")
    message(VERBOSE "Available ports in ${FREERTOS_COMPILER_PORT_DIRECTORY} are: ${PORTS}")

    # Check that <FREERTOS_KERNEL_PORT> contains a valid port in the identified compiler port directory.
    if (NOT DEFINED FREERTOS_KERNEL_PORT)
        message(FATAL_ERROR "<FREERTOS_KERNEL_PORT> is undefined. Set <FREERTOS_KERNEL_PORT> to the desired port. Available ports are: ${PORTS}")
    else()
        if(NOT FREERTOS_KERNEL_PORT IN_LIST PORTS)
            message(FATAL_ERROR "${FREERTOS_KERNEL_PORT} is not an available port. Available ports are: ${PORTS}")
        else()
            set(FREERTOS_KERNEL_PORT ${FREERTOS_COMPILER_PORT_DIRECTORY}/${FREERTOS_KERNEL_PORT})
        endif()
    endif()
endif()
message(VERBOSE "Directory for port implementation is: ${FREERTOS_KERNEL_PORT}")

# Search the port directory for source files.
file(GLOB FREERTOS_KERNEL_PORT_SOURCES
    ${FREERTOS_KERNEL_PORT}/*.asm
    ${FREERTOS_KERNEL_PORT}/*.c
    ${FREERTOS_KERNEL_PORT}/*.s*
    ${FREERTOS_KERNEL_PORT}/*.S
)
message(VERBOSE "Source files identified for port implementation are: ${FREERTOS_KERNEL_PORT_SOURCES}")


## FreeRTOS Kernel Heap ##
if(FREERTOS_KERNEL_USE_CUSTOM_HEAP)
    # If a custom heap is being used then check that <FREERTOS_KERNEL_HEAP_FILE> contains a valid file.
    if(NOT DEFINED FREERTOS_KERNEL_HEAP_FILE)
        message(FATAL_ERROR "<FREERTOS_KERNEL_HEAP_FILE> is undefined. Set <FREERTOS_KERNEL_HEAP_FILE> to the file that contains the heap implementation.")
    else()
        if(NOT EXISTS "${FREERTOS_KERNEL_HEAP_FILE}")
            message(FATAL_ERROR "Custom heap implementation file: ${FREERTOS_KERNEL_HEAP_FILE} does not exist.")
        endif()
    endif()
else()
    # Search the memory management directory for available heap implementations.
    set(FREERTOS_MEMORY_MANAGEMENT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/portable/MemMang")
    file(GLOB HEAP_FILES RELATIVE "${FREERTOS_MEMORY_MANAGEMENT_DIRECTORY}" CONFIGURE_DEPENDS "${FREERTOS_MEMORY_MANAGEMENT_DIRECTORY}/*.c")
    message(VERBOSE "Available heap files in ${FREERTOS_MEMORY_MANAGEMENT_DIRECTORY} are: ${HEAP_FILES}")

    # Check that <FREERTOS_KERNEL_HEAP_FILE> contains a valid heap file in the memory management directory.
    if(NOT DEFINED FREERTOS_KERNEL_HEAP_FILE)
        message(FATAL_ERROR "<FREERTOS_KERNEL_HEAP_FILE> is undefined. Set <FREERTOS_KERNEL_HEAP_FILE> to the desired heap implementation. Available implementations are: ${HEAPS}")
    else ()
        if(${FREERTOS_KERNEL_HEAP_FILE} IN_LIST HEAP_FILES)
            set(FREERTOS_KERNEL_HEAP_FILE ${FREERTOS_MEMORY_MANAGEMENT_DIRECTORY}/${FREERTOS_KERNEL_HEAP_FILE})
        elseif(${FREERTOS_KERNEL_HEAP_FILE}.c IN_LIST HEAP_FILES)
            set(FREERTOS_KERNEL_HEAP_FILE ${FREERTOS_MEMORY_MANAGEMENT_DIRECTORY}/${FREERTOS_KERNEL_HEAP_FILE}.c)
        else()
            message(FATAL_ERROR "${FREERTOS_KERNEL_HEAP_FILE} is not an available heap. Available heap files are: ${HEAP_FILES}")
        endif()
    endif()
endif()
message(VERBOSE "Heap implementation file is: ${FREERTOS_KERNEL_HEAP_FILE}")


## FreeRTOS Kernel Headers ##
target_include_directories(FreeRTOS-Kernel PUBLIC
    "${CMAKE_CURRENT_SOURCE_DIR}/include"
    ${FREERTOS_KERNEL_CONFIG}
    ${FREERTOS_KERNEL_PORT}
)


## FreeRTOS Kernel Sources ##
# Add core kernel source files.
target_sources(FreeRTOS-Kernel PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/croutine.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/event_groups.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/list.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/queue.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/stream_buffer.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/tasks.c"
    "${CMAKE_CURRENT_SOURCE_DIR}/timers.c"
    )

# Add heap implemntation source file.
target_sources(FreeRTOS-Kernel PRIVATE ${FREERTOS_KERNEL_HEAP_FILE})

# Add kernel port source file(s).
target_sources(FreeRTOS-Kernel PRIVATE ${FREERTOS_KERNEL_PORT_SOURCES})


list(POP_BACK CMAKE_MESSAGE_CONTEXT)
