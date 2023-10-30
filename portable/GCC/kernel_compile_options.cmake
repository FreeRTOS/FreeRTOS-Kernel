########################################################################
# Overall Compile Options
# Note the compile option strategy is to error on everything and then
# Per library opt-out of things that are warnings/errors.
# This ensures that no matter what strategy for compilation you take, the
# builds will still occur.
#
# Only tested with GNU and Clang.
# Other options are https://cmake.org/cmake/help/latest/variable/CMAKE_LANG_COMPILER_ID.html#variable:CMAKE_%3CLANG%3E_COMPILER_ID
# Naming of compilers translation map:
#
#   FreeRTOS    | CMake
#   -------------------
#   CCS         | ?TBD?
#   GCC         | GNU, Clang, *Clang Others?
#   IAR         | IAR
#   Keil        | ARMCC
#   MSVC        | MSVC # Note only for MinGW?
#   Renesas     | ?TBD?
set( freertos_kernel_compile_option
     ### Gnu/Clang C Options
     $<$<COMPILE_LANG_AND_ID:C,GNU>:-fdiagnostics-color=always>
     $<$<COMPILE_LANG_AND_ID:C,Clang>:-fcolor-diagnostics>

     $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wall>
     $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wextra>
     $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wpedantic>
     $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Werror>
     $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wconversion>
     $<$<COMPILE_LANG_AND_ID:C,Clang>:-Weverything>

     # Suppressions required to build clean with clang.
     $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
     $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-padded>
     $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-variable-declarations>
     $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-covered-switch-default>
     $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-align> )
