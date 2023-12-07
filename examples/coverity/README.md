# MISRA Compliance for FreeRTOS-Kernel
FreeRTOS-Kernel is MISRA C:2012 compliant. This directory contains a project to
run [Synopsys Coverity](https://www.synopsys.com/software-integrity/security-testing/static-analysis-sast.html)
for checking MISRA compliance.

> **Note**
Coverity version 2022.6.1 incorrectly infers the type of `pdTRUE` and `pdFALSE`
as boolean because of their names, resulting in multiple false positive warnings
about type mismatch. We replace `pdTRUE` with `pdPASS` and `pdFALSE` with
`pdFAIL` to avoid these false positive warnings. This workaround will not be
needed after Coverity fixes the issue of incorrectly inferring the type of
`pdTRUE` and `pdFALSE` as boolean.

Deviations from the MISRA C:2012 guidelines are documented in
[MISRA.md](../../MISRA.md) and [coverity_misra.config](coverity_misra.config)
files.

## Getting Started
### Prerequisites
Coverity can be run on any platform mentioned [here](https://sig-docs.synopsys.com/polaris/topics/c_coverity-compatible-platforms.html).
The following are the prerequisites to generate coverity report:

1. CMake version > 3.13.0 (You can check whether you have this by typing `cmake --version`).
2. GCC compiler.
    - See download and installation instructions [here](https://gcc.gnu.org/install/).
3. Clone the repo using the following command:
    - `git clone https://github.com/FreeRTOS/FreeRTOS-Kernel.git ./FreeRTOS-Kernel`

### Generating Report
Go to the root directory of the FreeRTOS-Kernel repo and run the following
commands in a terminal:
1. Update the compiler configuration in Coverity:
  ~~~
  cov-configure --force --compiler cc --comptype gcc
  ~~~
2. Create the build files using CMake in a `build` directory:
  ~~~
  cmake -B build -S examples/coverity
  ~~~
3. Build the (pseudo) application:
  ~~~
  cd build/
  cov-build --emit-complementary-info --dir cov-out make
  ~~~
4. Go to the Coverity output directory (`cov-out`) and begin Coverity static
   analysis:
  ~~~
  cd cov-out/
  cov-analyze --dir ./cov-out \
    --coding-standard-config ../examples/coverity/coverity_misra.config \
    --tu-pattern "file('.*/FreeRTOS/Source/[A-Za-z_]*\.c')
  ~~~
5. Generate the HTML report:
  ~~~
  cov-format-errors --dir ./cov-out --html-output html-output
  ~~~

HTML report should now be generated in a directory named `html-output`.
