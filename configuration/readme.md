# Configuration support for FreeRTOS

## Overview

Every FreeRTOS project requires FreeRTOSConfig.h located in their include path.

## Reference configuration
  A complete FreeRTOSConfig.h file is located in this folder.  Please use this file as a starting point.  Every config option is documented in this file along with defaults that will build the demo projects but will almost certainly not be suitable for all ports or applications.

## Configuration Generator
Alternatively, you can use the configuration generator to ask questions about your project and generate the FreeRTOSConfig.h automatically.

### Install kconfiglib
The automatic generation requires kconfiglib which can be installed with python pip.  This assumes you have python installed on your development machine.
```
pip3 install kconfiglib
```

### Generating a configuration
