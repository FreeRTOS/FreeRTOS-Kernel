# FreeROTS VeriFast Proofs
This directory contains an unbounded memory safety and thread safety proof
for the core of the task scheduler: `vTaskSwitchContext`
The proof ensures that no call to `vTaskSwitchContext` that complies with the
specified precondition results in unsafe memory accesses. It also ensures that
concurrent instances of `vTaskSwitchContext` running on different cores are
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
└── Test/VeriFast/tasks/vTaskSwitchContext
    │
    ├── run-verifast.sh
    │   Shell script to run check the proof with VeriFast.
    │
    ├── run-vfide.sh
    │   Shell script to load the proof into the VeriFast IDE.
    │
    ├── diff.sh
    │   Shell script to compute flag changes in the production code that
    │   potentially break the validity of the VeriFast proof. An empty diff
    │   means that the proof and the production code remain in sync.
    │
    ├── preprocessing_scripts
    │   Contains scripts to preprocess and rewrite the source code.
    │
    ├── demos
    │   Contains the FreeRTOS SMP demo. Our proofs use some of its
    │   configuartion files.
    │
    ├── include
    │   Contains annotated copies of header files residing in
    │   'FreeRTOS-Kernel/include'. These files are annotated with VeriFast
    |   predicates, lemmas and proof steps.
    │
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
    │
    ├── proof_setup
    │   Contains config files for the proof. The proof assumes a setup for
    │   RP2040.
    │
    ├── sdks
    │   Contains SDKs referenced by the proof setup.
    │   Some files are annotated with VeriFast contracts.
    │
    ├── src
    │   Contains annotated copies of source files residing in the repository's
    │   base directory 'FreeRTOS-Kernel'. The files are annotated with VeriFast
    │   predicates, lemmas and proof steps.
    │
    └── stats
        Contains some statistics about the VeriFast proof.
```



# Checking the Proof
The proof can be checked by running one of the scripts 'run-verifast.sh' and
'run-vfide.sh' residing in this directory (see repo structure above).
Both scripts preprocess the annotated code with Clang and rewrite syntax
VeriFast does not understand into something equivalent.
The result is written to a temporary file ('preprocessed_files/tasks_vf_pp.c')
before it is processed by VeriFast.
This file contains a copy of all the code and annotations required to check the
proof.
Both scripts expect the command line arguments explained below.
In the following we use the following variables

- #### run-verifast.sh:
  Preprocesses the code and proof files and uses the
  command-line version of VeriFast to check the resulting proof file.
  A call must have the form:
  #### run-verifast.sh \<REPO_BASE_DIR\> \<VERIFAST_DIR\>
  where
  - \<REPO_BASE_DIR\> is the absolute path to this repository's base directory,
    i.e., 'FreeRTOS-Kernel' in the repo structure depicted above.
  - \<VERIFAST_DIR\> is the absolute path to the VeriFast installation
    directory.

- #### run-vfide.sh:
  Preprocesses the code and proof files and loads the resulting proof file into
  the VeriFast IDE.
  A call must have the form:
  #### run-vfide.sh \<REPO_BASE_DIR\> \<VERIFAST_DIR\> \[\<FONT_SIZE\>\]
  where
  - \<REPO_BASE_DIR\> \<VERIFAST_DIR\> are as explained above
  - \<FONT_SIZE\> is an optional argument specifying the IDE's font size.

# Disclaimer
All scripts and proofs have been tested under OS X 12.6.1 and with the VeriFast nightly build from Dec 12th 2022.

# Proof Setup
The VeriFast proofs assume a setup for the Raspberry Pi Pico, i.e., RP2040.
