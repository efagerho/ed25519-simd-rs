# Machine model file layout

To audit a block, follow its mnemonics in `IntelSyntax.v`, its branch displacements in `Assembly.v`, its encoded bytes in `ProgramLayout.v`, and its effect on machine state in `Blocks.v`. For an individual SIMD instruction, `Instructions.v` dispatches to the instruction family that defines its lane operation and encoding.

## Instructions

| File | Contents |
| --- | --- |
| [X86.v](isa/X86.v) | Shared 64-bit truncation, EVEX prefixes, ModR/M fields, register encodings, and little-endian 32-bit fields. |
| [Move.v](isa/Move.v) | Lane copy and encodings for register moves, loads, and stores, including SIB bytes and compressed displacements. |
| [Arithmetic.v](isa/Arithmetic.v) | Wrapping qword addition, subtraction and multiplication for `vpaddq`, `vpsubq` and `vpmullq`, with their encoders. |
| [Logic.v](isa/Logic.v) | Lane operations and encodings for `vpxorq` and `vpandq`. |
| [Shift.v](isa/Shift.v) | Immediate left and logical right qword shifts and their encodings. |
| [IFMA.v](isa/IFMA.v) | Low and high 52-bit multiply-add operations, accumulator wraparound, and register/memory encodings. |
| [Instructions.v](isa/Instructions.v) | Typed vector operands and opcodes, operand validation, per-lane execution (`bits`, `run`), byte encoding (`encode`), and Intel text rendering (`asm_of`). |

## Programs and execution

| File | Contents |
| --- | --- |
| [ProgramLayout.v](isa/ProgramLayout.v) | Block bodies, terminators, shared vector fragments, and padding. `image` emits bytes. `valid_program` checks encodability, contiguous layout, and static control-flow targets. |
| [LayoutProofs.v](execution/LayoutProofs.v) | Proves that successful layout validation locates block bytes in the image, gives unique fetches and non-overlapping blocks, resolves vector fragments, and establishes static targets. |
| [Assembly.v](isa/Assembly.v) | Assembles addressed source blocks into a program. Collects vector fragments and computes call and jump displacements relative to the end of the instruction. |
| [IntelSyntax.v](isa/IntelSyntax.v) | Coq notation for register names, memory operands, scalar and vector instructions, and named branch targets. Exposes `assemble` to listings that import the notation. |
| [MachineState.v](execution/MachineState.v) | Region-relative pointers, vector-cell and return-slot permissions, PC, GPRs, ZF, ZMM registers, and memory. Defines the control and data components of `state` and their accessors. |
| [Blocks.v](execution/Blocks.v) | Executes block bodies and terminators, produces stack events with each transfer, applies vector and memory effects, and defines `step`, `reaches`, and `returns`. Proves that a successful `path` witnesses a return and that the returned state is unique. Also exposes the layout and state definitions through `Machine.execution.Blocks`. |

## Execution proofs

| File | Contents |
| --- | --- |
| [Dependencies.v](execution/Dependencies.v) | Tracks which registers and loads can influence a vector result. Proves agreement on selected outputs and preservation of untouched registers. |
| [VectorSequence.v](execution/VectorSequence.v) | Defines a single SIMD step with direct memory reads. Proves that stepping a fragment instruction by instruction agrees with its batched evaluation, including failed access checks. |
| [BlockSequence.v](execution/BlockSequence.v) | Defines instruction-by-instruction execution with PC advancement. Proves equivalence to a fetched block step and the empty, singleton, and split-block laws. |
| [ExecutionProperties.v](execution/ExecutionProperties.v) | Proves memory preservation outside permitted writes and independence of the control trace and step failure from initial vector data. |
| [MemoryTrace.v](memory/MemoryTrace.v) | Uses the common execution traversal to record vector effects and transfer events. Relates the trace to block execution and checks the order and addresses of live returns. |
| [FlatMemory.v](memory/FlatMemory.v) | Replays vector stores and saved PCs in one little-endian byte memory. Proves agreement with tracked logical cells and preservation of every byte outside the write footprint. |
| [WordBounds.v](execution/WordBounds.v) | Unsigned qword invariants for scalar integer values, vector registers and memory. Proves preservation by instructions, blocks, executions and recorded vector-effect prefixes. |
| [ByteMemory.v](memory/ByteMemory.v) | Little-endian byte decoding, exact word/vector read-write round trips, and construction of bounded logical data from bytes. Turns serialization agreement into exact reads and proves replay preserves byte bounds. |
| [Lane.v](execution/Lane.v) | Exact lane projection of vector effects and preservation of qword bounds, parameterized by the program. |
| [MemoryGeometry.v](memory/MemoryGeometry.v) | Region-relative vector alignment, disjointness, and reflected region-membership checks. |
| [MemoryCoverage.v](memory/MemoryCoverage.v) | Checked vector-write coverage implies initialization of every byte in the output region. |
| [ByteExecution.v](memory/ByteExecution.v) | Shared trace-frame and concrete-memory lifting proofs, including prefix reads, caller-byte preservation, and every stack pop. |
| [ScalarRefinement.v](execution/ScalarRefinement.v) | Concrete qword scalar effects and stack transfers, their representation relation, operation/body/block refinement with explicit placement and byte-read premises, and preservation of concrete word bounds. |
| [Alignment.v](memory/Alignment.v) | Relates clearing six low address bits to relative pointer alignment at a 64-byte-aligned region origin. |
| [proofs/README.md](proofs/README.md) | States the open obligation to decode the model's bytes with an independent x86 ISA specification and prove agreement on register and memory effects. |

## Conformance tests

| File | Contents |
| --- | --- |
| [tests/run.py](tests/run.py) | Command-line runner for Coq, Intel XED, and native comparisons. Selects cases and block probes, retains complete inputs in reports, and replays successful reports or failure records. |
| [tests/case_data.py](tests/case_data.py) | Case schema, mnemonic operand forms, register initialization, and seeded random case generation. |
| [tests/overflow.py](tests/overflow.py) | Generates arithmetic and IFMA boundary cases and all 256 immediate shift counts, with expected values computed in Python. |
| [tests/Operands.v](tests/Operands.v) | Coq regression examples for load encodings, signed displacement rendering, and operand order. |
| [tests/Representation.v](tests/Representation.v) | Regressions for noncanonical word rejection, high-bit little-endian decoding, unaligned vector writes and adjacent-byte preservation. |
| [tests/Control.v](tests/Control.v) | Mnemonic call/return and conditional-branch probe, predicted scalar observations, and invalid control-flow and stack-access examples. |
| [tests/Mixed.v](tests/Mixed.v) | Mnemonic loop combining vector arithmetic, load/store, and a scalar branch. Defines the initial state, memory permissions, and final observations. |
| [tests/Prologue.v](tests/Prologue.v) | Stack and buffer probe for scalar moves, broadcasts, address calculations, vector loads and stores, and upper-lane clearing. |
| [tests/Aligned.v](tests/Aligned.v) | Aligned-frame probe for saved RBP, register copies, restricted sign-extended imm32 moves, all four SysV stack padding cases and two nested calls. |
| [tests/CallerForms.v](tests/CallerForms.v) | Compares a program's scalar and control-flow forms with those exercised by the native probes. |
| [tests/model/Oracle.v](tests/model/Oracle.v) | Computes one instruction's encoded bytes and destination lanes. Proves preservation of other registers and formats numeric results for the runner. |
| [tests/model/backend.py](tests/model/backend.py) | Builds the Coq modules, evaluates batches of instruction cases and whole-program probes, and reads back their predictions. |
| [tests/xed/build-kit.sh](tests/xed/build-kit.sh) | Builds a static Intel XED kit from pinned XED and mbuild revisions. |
| [tests/xed/decode.c](tests/xed/decode.c) | Decodes supplied bytes with Intel XED and reports instruction length, operands, addressing, and EVEX attributes. |
| [tests/xed/backend.py](tests/xed/backend.py) | Builds and invokes the XED driver and constructs the expected decoded fields for each typed instruction. |
| [tests/native/backend.py](tests/native/backend.py) | Builds instruction wrappers and block probes, checks their machine bytes, and collects observations from a child process pinned to one CPU. |
| [tests/native/probe_main.c](tests/native/probe_main.c) | Shared block-probe executable entry point. Prints the linked probe bytes or runs the observations for supplied inputs. |
| [tests/native/control.S](tests/native/control.S) | Assembly counterpart of the Coq control probe and wrapper that captures RAX, RCX, and ZF and checks stack restoration. |
| [tests/native/control.c](tests/native/control.c) | Supplies each initial RCX to the control wrapper and prints its observations. |
| [tests/native/mixed.S](tests/native/mixed.S) | Assembly counterpart of the Coq mixed loop and wrapper that loads and captures the ZMM registers, records RCX and ZF, and checks the stack. |
| [tests/native/mixed.c](tests/native/mixed.c) | Seeds registers and an unaligned memory buffer, invokes the mixed wrapper, and prints the registers and three memory cells. |
| [tests/native/prologue.S](tests/native/prologue.S) | Assembly counterpart of the stack and buffer probe. Switches to a private stack and snapshots registers before returning to C. |
| [tests/native/prologue.c](tests/native/prologue.c) | Initializes the private stack, registers and three guarded buffers, and reports the observed qwords. |
| [tests/native/aligned.S](tests/native/aligned.S) | Assembly counterpart of the aligned-frame probe and wrapper that captures registers and stack words. |
| [tests/native/aligned.c](tests/native/aligned.c) | Initializes private stack alignments, checks guards and prints the aligned probe's observations. |

### Fixed input files

| File | Cases |
| --- | --- |
| [tests/cases/arithmetic.jsonl](tests/cases/arithmetic.jsonl) | Qword addition overflow, subtraction underflow and aliasing, and multiplication truncation and wraparound. |
| [tests/cases/ifma.jsonl](tests/cases/ifma.jsonl) | Accumulator wraparound, discarded upper operand bits, and an aliased accumulator. |
| [tests/cases/logic.jsonl](tests/cases/logic.jsonl) | Self-XOR, XOR of distinct sources, and AND with an aliased destination. |
| [tests/cases/move.jsonl](tests/cases/move.jsonl) | Register copies and loads across base registers and displacement boundaries. |
| [tests/cases/shift.jsonl](tests/cases/shift.jsonl) | Left and right shifts by 0, 1, 63, 64, and 255. |

## Build and documentation

| File | Contents |
| --- | --- |
| [_CoqProject](_CoqProject) | Maps this directory to the Coq namespace `Machine` and lists the model, proof, and test modules to build. |
| [README.md](README.md) | Model scope, theorem summaries, conformance coverage, and commands for building, testing, and replaying a case. |
| [CODE_LAYOUT.md](CODE_LAYOUT.md) | This file index. |

[LinkedCalls.v](execution/LinkedCalls.v) executes straight-line linked callers on concrete registers and byte memory. It decodes relative call displacements and connects return states to the block interpreter and its recorded writes. [KnownRegisters.v](execution/KnownRegisters.v) proves that successful block execution preserves representability of the entry registers.

[SysV.v](abi/SysV.v) defines the callee-saved GPRs and stack restoration. [CallFrame.v](abi/CallFrame.v) projects these guarantees to concrete registers and proves which caller bytes survive a call, including the write made by pushing its return address.
