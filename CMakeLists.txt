cmake_minimum_required(VERSION 3.13)

####################################################################################################
# User configurable options
####################################################################################################

option(FREERTOS_CREATE_GCC_SECTIONS 
    "Generate sections for functions and data. Required to remove unused code" ON
)
if(FREERTOS_CREATE_GCC_SECTIONS)
    option(FREERTOS_REMOVE_UNUSED_CODE "Remove unused code." ON)
endif()

####################################################################################################
# Pre project configuration
####################################################################################################
if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    if(NOT FREERTOS_WARNING_FLAGS)
        set(FREERTOS_WARNING_FLAGS
            -Wall
            -Wextra
            -Wimplicit-fallthrough=1
            -Wno-unused-parameter
            -Wshadow=local
        )
    endif()
endif()

set(LIB_FREERTOS_NAME freertos)
add_library(${LIB_FREERTOS_NAME})

####################################################################################################
# Source file handling
####################################################################################################

if(NOT FREERTOS_ADDITIONAL_SOURCES)
	message(WARNING 
		"FREERTOS_ADDITIONAL_SOURCES list of FreeRTOS sources was not " 
		"supplied, build might fail!"
	)
endif()

# Convert supplied additional sources to absolute path version. The user should set
# a list of sources like the port source and the selected memory management source file.
foreach(FREERTOS_ADDITIONAL_SRC ${FREERTOS_ADDITIONAL_SOURCES})
	if(IS_ABSOLUTE ${FREERTOS_ADDITIONAL_SRC})
		set(CURRENT_ADDITIONAL_SRC ${FREERTOS_ADDITIONAL_SRC})
	else()
		get_filename_component(CURRENT_ADDITIONAL_SRC
			${FREERTOS_ADDITIONAL_SRC} REALPATH BASE_DIR ${CMAKE_SOURCE_DIR}
		)
	endif()
	
	if(CMAKE_VERBOSE)
        message(STATUS "FreeRTOS port source: ${FREERTOS_ADDITIONAL_SRC}")
    endif()
	list(APPEND FREERTOS_ADDITIONAL_SOURCES_ABS ${CURRENT_ADDITIONAL_SRC})
endforeach()

# Can be used if the sources are packaged inside a separate folder.
if(NOT FREERTOS_KERNEL_SOURCE_FOLDER)
    set(FREERTOS_KERNEL_SOURCE_FOLDER ${CMAKE_CURRENT_SOURCE_DIR})
endif()

target_sources(${LIB_FREERTOS_NAME}  PRIVATE
    ${FREERTOS_KERNEL_SOURCE_FOLDER}/croutine.c
    ${FREERTOS_KERNEL_SOURCE_FOLDER}/event_groups.c
    ${FREERTOS_KERNEL_SOURCE_FOLDER}/list.c
    ${FREERTOS_KERNEL_SOURCE_FOLDER}/queue.c
    ${FREERTOS_KERNEL_SOURCE_FOLDER}/stream_buffer.c
    ${FREERTOS_KERNEL_SOURCE_FOLDER}/tasks.c
    ${FREERTOS_KERNEL_SOURCE_FOLDER}/timers.c
    ${FREERTOS_ADDITIONAL_SOURCES_ABS}
)

####################################################################################################
# Include handling
####################################################################################################

if(NOT FREERTOS_ADDITIONAL_INCLUDE_PATHS)
	message(WARNING
		"FREERTOS_ADDITIONAL_INCLUDE_PATHS list of external FreeRTOS includes was not supplied, "
		" build might fail!"
	)
endif()

# Convert supplied FreeRTOS includes paths to absolute paths. The user should set
# the path containing files like FreeRTOSConfig.h
foreach(FREERTOS_ADDITIONAL_INC ${FREERTOS_ADDITIONAL_INCLUDE_PATHS})
	if(IS_ABSOLUTE ${FREERTOS_ADDITIONAL_INC})
		set(CURR_ADDITIONAL_INC_ABS "${FREERTOS_ADDITIONAL_INC}")
	else()
		get_filename_component(CURR_ADDITIONAL_INC_ABS
			${FREERTOS_ADDITIONAL_INC} REALPATH BASE_DIR ${CMAKE_SOURCE_DIR})
	endif()
	
	if(CMAKE_VERBOSE)
		message(STATUS "FreeRTOS configuration path: ${CURR_ABS_FREERTOS_PATH}")
	endif()
	
	list(APPEND FREERTOS_ADDITIONAL_INC_PATHS_ABS ${CURR_ADDITIONAL_INC_ABS})
endforeach()

# Also considers the case where the user packages the header files into a freertos folder again
target_include_directories(${LIB_FREERTOS_NAME} INTERFACE
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_CURRENT_SOURCE_DIR}/include/freertos
    ${FREERTOS_ADDITIONAL_INC_PATHS_ABS}
)

target_include_directories(${LIB_FREERTOS_NAME} PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/include
    ${CMAKE_CURRENT_SOURCE_DIR}/include/freertos
    ${FREERTOS_ADDITIONAL_INC_PATHS_ABS}
)

####################################################################################################
# Library handling
####################################################################################################

if(FREERTOS_ADDITIONAL_LIBS)
    target_link_libraries(${LIB_FREERTOS_NAME} PRIVATE
        ${FREERTOS_ADDITIONAL_LIBS}
    )
endif()

####################################################################################################
# Flags and defines
####################################################################################################

if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    if(FREERTOS_CREATE_GCC_SECTIONS)
        target_compile_options(${LIB_FREERTOS_NAME} PRIVATE
            ${FREERTOS_WARNING_FLAGS}
        )
        
        # Create sections for a GCC compiler
        target_compile_options(${LIB_FREERTOS_NAME} PRIVATE
            "-ffunction-sections"
            "-fdata-sections"
        )
        
        if(FREERTOS_REMOVE_UNUSED_CODE)
            target_link_options(${LIB_FREERTOS_NAME} PRIVATE
                "-Wl,--gc-sections"
            )
        endif()
    endif()
endif()

