# FreeROTS VeriFast Proofs
This directory contains an unbounded proof memory safety and thread safety proof
for the core of the task scheduler: `vTaskSwitchContext`
The proof ensures that no call to `vTaskSwitchContext` that complies with the
specified precondition results in unsafe memory accesses. It also ensures that
concurrent instances of `vTaskSwitchContext` running on diffierent cores are
mutually thread safe.


# Proof Directory Structure

```
FreeRTOS-Kernel
│
│
│
├── tasks.c files
│   The base directory contains the source files, in particular `tasks.c`.
│   `tasks.c` has been annotated with the VeriFast proof steps necessary to
│   prove memory safety and thread safety of `vTaskSwitchContext`.
│   The proof uses many specifications and lemmas residing in 
│   `verification/verifast/proof_setup` and `verifcation/verifast/proofs`.
│
│
├── include
│   Contains the header files. Some of the header files have been annotated with
│   VeriFast contracts and proofs.
│
│
├── portable
│   └── Thirdparty
│       └── GCC
│           └── RP2040
│               Contains the Raspberry Pi Pico setup.
│
│
└── verification
    └── verifast
        ├── preprocessing_scripts
        │   Contains scripts to preprocess and rewrite the source code.
        │
        ├── demos
        │   Contains the FreeRTOS SMP demo. Our proofs use some of its 
        │   configuartion files.
        │
        ├── proof
        │   Contains the VeriFast proof files.
        │   │
        │   ├── *.h files
        │   │   Headers containing VeriFast formalizations and proofs.
        │   │
        │   ├── README.md
        │   │   Contains more details about the proof.
        │   │
        │   ├── single_core_proofs
        │   │   Contains the old list formalization and proofs written by
        │   │   Aalok Thakkar and Nathan Chong in 2020 for the single-core 
        │   │   setup.
        │   │
        │   └── single_core_proofs_extended
        │       Contains new proofs extending the single-core list
        │       formalization.
        │
        ├── proof_setup
        │   Contains config files for the proof. The proof assumes a setup for
        │   RP2040.
        │
        └── sdks
            Contains SDKs referenced by the proof setup.
            Some files are annotated with VeriFast contracts.
```



# Proof Setup
The VeriFast proofs assume a setup for the Raspberry Pi Pico, i.e., RP2040.