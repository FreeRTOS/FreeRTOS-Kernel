This directory contains files copied from:
`/Library/Developer/CommandLineTools/SDKs/MacOSX12.3.sdk/System/Library/Frameworks/Kernel.framework/Versions/A/Headers`
We cannot put this directory on VeriFast's include path because it contains
the file `stdbool.h` which VeriFast cannot parse.

More specifically, VeriFast cannot parse the defines `#define false 0` and
`#define true 1` contained in the header `stdbool.h`.
Therefore, by default, it skips all includes of `stdbool.h` and
uses its builtin definitions of `true` and `false`. However, if we manually
specify an include path (via VeriFast's `-I` option) that contains `stdbool.h`,
this behaviour changes. It stops skipping these includes which leads to parse
errors.
