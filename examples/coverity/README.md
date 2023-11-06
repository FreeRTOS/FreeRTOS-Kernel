# Static code analysis for FreeRTOS-Kernel
This directory is made for the purpose of statically testing the MISRA C:2012 compliance of FreeRTOS-Kernel using
[Synopsys Coverity](https://www.synopsys.com/software-integrity/security-testing/static-analysis-sast.html) static analysis tool.
To that end, this directory provides a [CMake](CMakeLists.txt)
file and [FreeRTOSConfig.h](configuration/FreeRTOSConfig.h)
required to build an application for the tool to analyze.

> **Note**
FreeRTOS does not use boolean type included in C language C99 standard. For generating
the report as outlined below, `pdTRUE` is replaced with `pdPASS` and `pdFALSE` is replaced
with `pdFAIL` in the source code files to prevent false positive deviations with Coverity
version 2022.6.1.

For details regarding the suppressed violations in the report (which can be generated using the instructions described below),
please see the [MISRA.md](../../MISRA.md) file.

## Getting Started
### Prerequisites
You can run this on a platform supported by Coverity. The list and other details can be found [here](https://sig-docs.synopsys.com/polaris/topics/c_coverity-compatible-platforms.html).
To compile and run the Coverity target successfully, you must have the following:

1. CMake version > 3.13.0 (You can check whether you have this by typing `cmake --version`)
2. GCC compiler
    - You can see the downloading and installation instructions [here](https://gcc.gnu.org/install/).
3. Download the repo and include the submodules using the following commands.
    - `git clone https://github.com/FreeRTOS/FreeRTOS-Kernel.git ./FreeRTOS-Kernel`

### To build and run Coverity:
Go to the root directory of the FreeRTOS-Plus-TCP repo and run the following commands in terminal:
1. Update the compiler configuration in Coverity
  ~~~
  cov-configure --force --compiler cc --comptype gcc
  ~~~
2. Create the build files using CMake in a `build` directory
  ~~~
  cmake -B build -S examples/coverity
  ~~~
3. Build the (pseudo) application
  ~~~
  cd build/
  cov-build --emit-complementary-info --dir cov-out make
  ~~~
4. Go to the Coverity output directory (`cov-out`) and begin Coverity static analysis
  ~~~
  cd cov-out/
  cov-analyze --dir ./cov-out \
    --coding-standard-config ../examples/coverity/coverity_misra.config \
    --tu-pattern "file('.*/FreeRTOS/Source/[A-Za-z_]*\.c')
  ~~~
5. Format the errors in HTML format so that it is more readable while removing the FreeRTOS-Kernel directory from the report
  ~~~
  cov-format-errors --dir ./cov-out --html-output html-output
  ~~~

You should now have the HTML formatted violations list in a directory named `html-output`.
