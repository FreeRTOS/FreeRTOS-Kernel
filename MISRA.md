# MISRA Compliance

FreeRTOS-Kernel conforms to [MISRA C:2012](https://www.misra.org.uk/misra-c)
guidelines, with the deviations listed below. Compliance is checked with
Coverity static analysis. Since the FreeRTOS kernel is designed for
small-embedded devices, it needs to have a very small memory footprint and
has to be efficient. To achieve that and to increase the performance, it
deviates from some MISRA rules. The specific deviations, suppressed inline,
are listed below.

Additionally, [MISRA configuration file](examples/coverity/coverity_misra.config)
contains project wide deviations.

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming rule 8.4 violation; with justification in point 1 ):
```
grep 'MISRA Ref 8.4.1' . -rI
```

#### Rule 8.4

_Ref 8.4.1_

- MISRA C:2012 Rule 8.4: A compatible declaration shall be visible when an
        object or function with external linkage is defined.
        This rule requires that a compatible declaration is made available
        in a header file when an object with external linkage is defined.
        pxCurrentTCB(s) is defined with external linkage but it is only
        referenced from the assembly code in the port files. Therefore, adding
        a declaration in header file is not useful as the assembly code will
        still need to declare it separately.
