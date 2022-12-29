# FreeRTOS VeriFast Proofs
This directory contains an unbounded memory safety and thread safety proof
for the core of the task scheduler: `vTaskSwitchContext`

Informally, the proof guarantees the following:
```
Proof Assumptions:
 - Data structure specification
 - Locking discipline
 - Contracts abstracting assembly
 - FreeRTOS config
 - Function contract of `vTaskSwitchContext`

==>

Unbounded memory & thread safety guarantees:
  ∀ #tasks. ∀ task interleavings. ∀ interrupt schedules. ∀ data sizes.∀ cores C1, …, Cn.
	vTaskSwitchContext(C1)  ||  …  ||  vTaskSwitchContext(Cn)  
  =>  (no memory error ∧ no race condition)
```

We have to model certain aspects of the system and our proof assumes that these models are correct (cf. `Proof Assumptions` below for a detailed explanation).
In particular, this modeling step includes writing a precondition for `vTaskSwitchContext` that specifies the context in which the function may be called.

Our proof considers any number of running tasks, any possible task interleavings and any interrupts that might occur during execution.
In particular, it considers any possible size for the involved data structures, since it is an unbounded proof.

The proof ensures that every concurrent execution of `vTaskSwitchContext` on any cores is memory safe and mutually thread safe.
That is, when we execute multiple instances of the function on different cores, we won't get any memory errors or data races, no matter how these instances interleave or when interrupts occur.


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

# Proof Assumptions
We have to model certain aspects of the system in order to reason about the task scheduler.
The proof treats these models as assumptions.
Therefore, the proof's correctness relies on the correctness of our models.

- ### FreeRTOS Configuration
  The VeriFast proofs assume a setup for the Raspberry Pi Pico, i.e., RP2040, cf. directory `proof_setup`.
  We use the config files from the official FreeRTOS SMP demo for the RP2040 and from official RP2040 port.
  The most important properties of this configuration are:
  - It supports running multiple priorities in parallel on different cores.
  - Core affinity is deactivated, i.e., all tasks may be scheduled on any core.

  The Raspberry Pi Pico only has two cores and we want to ensure that our proof does not accidentally rely on the properties that come with this binary setup.
  Hence, we changed the number of cores to an arbitrary large number.

- ### Contracts Abstracting Assembly
  The port layer of FreeRTOS contains assembly code that is essential for our proof.
  In particular, code to mask interrupts and code to acquire and release locks.
  VeriFast is a program verifier for C and not designed to handle any kind of assembly.
  The port-specific assembly is called via macros with a port-specific definition.
  We redefined these macros to call dummy function prototypes instead.
  We equipped these prototypes with VeriFast contracts that capture the semantics of the original assembly code, cf. `proof/port_contracts.h`.
  This way, VeriFast refers to the contracts to reason about the macro calls and does not have to deal with the assembly code.

- ### Data structure specification
  VeriFast expects us to specify the memory layout of the data structures accessed by the task scheduler.
  In a proof, these specifications tell us what a well-formed instance of a data structure looks like and how me may manipulate it to preserve well-formedness.

  Most notably, the scheduler searches the so called "ready lists", a global array of cyclic doubly linked lists storing tasks of specific priorities that are ready to be scheduled.
  Reasoning about this data structure is challenging because it requires heavy reasoning about its complex internals.

  Previously, Aalok Thakkar and Nathan Chong used VeriFast to prove functional correctness of the stand-alone list data structure for a single-core setup, c.f. [FreeRTOS Pull Request 836: Update VeriFast proofs](https://github.com/FreeRTOS/FreeRTOS/pull/836).
  We reused their formalization and proofs as much as possible.
  However, we had to heavily adapt both to tailor them to the needs of the scheduler proof, cf. `Reusing List Proofs` below.

  The reused specification resides in `proofs/single_core_proofs/`.
  The full ready list array is specified in `proofs/ready_list_predicates.h`.


- ### Function Contract of `vTaskSwitchContext`
  VeriFast expects every function that it verifies to have a so called "function contract".
  These contracts consist of a precondition, also called the "requires clause" and a postcondition, also called the "ensures clause".
  The precondition characterizes the context in which the function may be called.
  This determines the state in which our proof starts.
  The postcondition characterizes the state we want to be in when the function terminates.

  Starting from the precondition, VeriFast symbolically executes the function's code and our annotated proof steps.
  The proof succeeds if every step succeeds and if the proof ends in a state that complies with the specified postcondition.

  Hence, the function contract determines *WHAT* we prove.
  `vTaskSwitchContext` is called by an interrupt defined in the port layer on some core `C`.
  This interrupt masks interrupts on this core and acquires the locks protecting the ready lists.
  Therefore, the precondition of `vTaskSwitchContext` states that:
  - the function is executed on an arbitrary core `C`
  - interrupts on core `C` are deactivated
  - the locks protecting the ready lists have been acquired
  - that all the relevant global data structures are well-formed

  The postcondition states that all these properties are preserved, which is what the interrupt calling into the scheduler expects.



- ### Locking discipline



# Reusing List Proofs
