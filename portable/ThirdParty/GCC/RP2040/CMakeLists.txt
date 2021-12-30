cmake_minimum_required(VERSION 3.13)

if (NOT TARGET _FreeRTOS_kernel_inclusion_marker)
    add_library(_FreeRTOS_kernel_inclusion_marker INTERFACE)

    # Pull in PICO SDK (must be before project)
    include(pico_sdk_import.cmake)
    if (PICO_SDK_VERSION_STRING VERSION_LESS "1.2.0")
        message(FATAL_ERROR "Require at least Raspberry Pi Pico SDK version 1.2.0")
    endif()

    if (NOT FREERTOS_KERNEL_PATH)
        get_filename_component(FREERTOS_KERNEL_PATH ${CMAKE_CURRENT_LIST_DIR}/../../../.. REALPATH)
    endif ()

    message(DEBUG "FREERTOS_KERNEL_PATH is ${FREERTOS_KERNEL_PATH}")
    project(FreeRTOS-Kernel C CXX)

    set(CMAKE_C_STANDARD 11)
    set(CMAKE_CXX_STANDARD 17)

    pico_is_top_level_project(FREERTOS_KERNEL_TOP_LEVEL_PROJECT)

    # The real work gets done in library.cmake which is called at the end of pico_sdk_init
    list(APPEND PICO_SDK_POST_LIST_FILES ${CMAKE_CURRENT_LIST_DIR}/library.cmake)

    # We need to inject the following header file into ALL SDK files (which we do via the config header)
    list(APPEND PICO_CONFIG_HEADER_FILES ${CMAKE_CURRENT_LIST_DIR}/include/freertos_sdk_config.h)

    if (FREERTOS_KERNEL_TOP_LEVEL_PROJECT)
        message("FreeRTOS: initialize SDK since we're the top-level")
        # Initialize the SDK
        pico_sdk_init()
    else()
        set(PICO_SDK_POST_LIST_FILES ${PICO_SDK_POST_LIST_FILES} PARENT_SCOPE)
        set(PICO_CONFIG_HEADER_FILES ${PICO_CONFIG_HEADER_FILES} PARENT_SCOPE)
        set(FREERTOS_KERNEL_PATH ${FREERTOS_KERNEL_PATH} PARENT_SCOPE)
    endif()
endif()

