## Getting started
This repository contains FreeRTOS kernel source/header files and kernel ports only. This repository is referenced as a submodule in [FreeRTOS/FreeRTOS](https://github.com/FreeRTOS/FreeRTOS) repository, which contains pre-configured demo application projects under ```FreeRTOS/Demo``` directory.

The easiest way to use FreeRTOS is to start with one of the pre-configured demo application projects.  That way you will have the correct FreeRTOS source files included, and the correct include paths configured.  Once a demo application is building and executing you can remove the demo application files, and start to add in your own application source files.  See the [FreeRTOS Kernel Quick Start Guide](https://www.FreeRTOS.org/FreeRTOS-quick-start-guide.html) for detailed instructions and other useful links.

Additionally, for FreeRTOS kernel feature information refer to the [Developer Documentation](https://www.FreeRTOS.org/features.html), and [API Reference](https://www.FreeRTOS.org/a00106.html).

### Getting help
If you have any questions or need assistance troubleshooting your FreeRTOS project, we have an active community that can help on the [FreeRTOS Community Support Forum](https://forums.freertos.org).

## To consume FreeRTOS-Kernel

### Consume with CMake
If using CMake, it is recommended to use this repository using FetchContent.
Add the following into your project's main or a subdirectory's `CMakeLists.txt`:

- Define the source and version/tag you want to use:

```cmake
FetchContent_Declare( freertos_kernel
  GIT_REPOSITORY https://github.com/FreeRTOS/FreeRTOS-Kernel.git
  GIT_TAG        master #Note: Best practice to use specific git-hash or tagged version
)
```

- Add a freertos_config library (typically an INTERFACE library) The following assumes the directory structure:
  - `include/FreeRTOSConfig.h`
```cmake
add_library(freertos_config INTERFACE)

target_include_directories(freertos_config SYSTEM
INTERFACE
    include
)

target_compile_definitions(freertos_config
  INTERFACE
    projCOVERAGE_TEST=0
)
```

- Configure the FreeRTOS-Kernel and make it available
  - this particular example supports a native and cross-compiled build option.

```cmake
set( FREERTOS_HEAP "4" CACHE STRING "" FORCE)
# Select the native compile PORT
set( FREERTOS_PORT "GCC_POSIX" CACHE STRING "" FORCE)
# Select the cross-compile PORT
if (CMAKE_CROSSCOMPILING)
  set(FREERTOS_PORT "GCC_ARM_CA9" CACHE STRING "" FORCE)
endif()

FetchContent_MakeAvailable(freertos_kernel)
```

### Consuming stand-alone - Cloning this repository

To clone using HTTPS:
```
git clone https://github.com/FreeRTOS/FreeRTOS-Kernel.git
```
Using SSH:
```
git clone git@github.com:FreeRTOS/FreeRTOS-Kernel.git
```

## Repository structure
- The root of this repository contains the three files that are common to
every port - list.c, queue.c and tasks.c.  The kernel is contained within these
three files.

- The ```./portable``` directory contains the files that are specific to a particular microcontroller and/or compiler.
See the readme file in the ```./portable``` directory for more information.

- The ```./include``` directory contains the real time kernel header files.

### Code Formatting
FreeRTOS files are formatted using the "uncrustify" tool. The configuration file used by uncrustify can be found in the [.github/uncrustify.cfg](.github/uncrustify.cfg) file.

### Line Endings
File checked into the FreeRTOS-Kernel repository use unix-style LF line endings for the best compatbility with git.

For optmial compatibility with Microsoft Windows tools, it is best to enable the git autocrlf feature. You can eanble this setting for the current repository using the following command:
```
git config core.autocrlf true
```

### Git History Optimizations
Some commits in this repository perform large refactors which touch many lines and lead to unwanted behavior when using the `git blame` command. You can configure git to ignore the list of large refactor commits in this repository with the followig command:
```
git config blame.ignoreRevsFile .git-blame-ignore-revs
```

### Spelling
*lexicon.txt* contains words that are not traditionally found in an English dictionary. It is used by the spellchecker to verify the various jargon, variable names, and other odd words used in the FreeRTOS code base. If your pull request fails to pass the spelling and you believe this is a mistake, then add the word to *lexicon.txt*.
Note that only the FreeRTOS Kernel source files are checked for proper spelling, the portable section is ignored.
