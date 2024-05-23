# MISRA Compliance for FreeRTOS-Kernel
FreeRTOS-Kernel is MISRA C:2012 compliant. This directory contains a project to
run [CodeSecure CodeSonar](https://codesecure.com/our-products/codesonar/)
for checking MISRA compliance.


Deviations from the MISRA C:2012 guidelines are documented in
[MISRA.md](../../MISRA.md) and [codesonar.con](codesonar.conf)
files.

## Getting Started
### Prerequisites
CodeSonar can be run on a large number of platforms, see the CodeSonar documentation for more information. To run CodeSonar, one would require the following step:

1. CMake version > 3.13.0 (You can check whether you have this by typing `cmake --version`).
2. GCC compiler.
    - See download and installation instructions [here](https://gcc.gnu.org/install/).
3. Clone the repo using the following command:
    - `git clone https://github.com/FreeRTOS/FreeRTOS-Kernel.git ./FreeRTOS-Kernel`

### Generating Report
Perform an analysis with CodeSonar through the following steps:
Singe core FreeRTOS:
  ~~~
  cmake -B build -S examples/codesonar
  ~~~

SMP FreeRTOS:
  ~~~
  cmake -B build -S examples/codesonar -DFREERTOS_SMP_EXAMPLE=1
  ~~~

Build and analyze the (pseudo) application:
  ~~~
  cd build/
  codesonar analyze freertos -preset misra2012 -conf-file ../examples/codesonar/codesonar.conf <hub-url> make
  ~~~
Generate the HTML report by going to the CodeSonar web interface for the analysis and Generate Report for MISRA 2012

