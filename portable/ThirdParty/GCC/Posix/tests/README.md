# POSIX thread-marker regression tests

Run on Linux with GCC, CMake, and a GNU-compatible linker:

```sh
cmake -S portable/ThirdParty/GCC/Posix/tests -B build/posix-tests
cmake --build build/posix-tests
ctest --test-dir build/posix-tests --output-on-failure
```

The failure-injection executable includes the actual port implementation to
reach its private helpers. Linker wrappers inject key-creation, allocation, and
TLS-storage failures. Each failure must terminate via the fatal handler; failed
TLS storage must first free the allocated marker. Tests run with assertions
both enabled and disabled. The success case checks thread identity, isolation
from the calling thread, and automatic destructor cleanup after pthread exit.
The separate smoke test links the full kernel and runs a real scheduled task
through a tick delay and scheduler shutdown.

For sanitizer validation, configure another build directory with
`-DCMAKE_C_FLAGS="-fsanitize=address,undefined -fno-omit-frame-pointer"`.
These tests are specific to the POSIX simulator; they do not validate hardware
ports. The kernel's main CMock suite lives in the parent FreeRTOS repository.
