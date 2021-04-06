if (NOT DEFINED FREERTOS_MEMMANG)
    message(WARNING "FREERTOS_MEMMANG not defined, user should linking some heap management file manually")
endif()

if (NOT DEFINED FREERTOS_PORT)
    message(FATAL_ERROR "FREERTOS_PORT not defined")
endif()

set(
    FREERTOS_INC
    ${CMAKE_CURRENT_SOURCE_DIR}/include
)

set(
    FREERTOS_SRC
    ${CMAKE_CURRENT_SOURCE_DIR}/tasks.c
    ${CMAKE_CURRENT_SOURCE_DIR}/timers.c
    ${CMAKE_CURRENT_SOURCE_DIR}/stream_buffer.c
    ${CMAKE_CURRENT_SOURCE_DIR}/queue.c
    ${CMAKE_CURRENT_SOURCE_DIR}/list.c
    ${CMAKE_CURRENT_SOURCE_DIR}/event_groups.c
    ${CMAKE_CURRENT_SOURCE_DIR}/croutine.c
)

if (DEFINED FREERTOS_MEMMANG)
    set(
        FREERTOS_SRC
        ${FREERTOS_SRC}
        ${CMAKE_CURRENT_SOURCE_DIR}/portable/MemMang/${FREERTOS_MEMMANG}.c
    )
endif()

add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/portable/${FREERTOS_PORT})

set(FREERTOS_SRC ${FREERTOS_SRC} PARENT_SCOPE)
set(FREERTOS_INC ${FREERTOS_INC} PARENT_SCOPE)
