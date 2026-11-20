# x86-64 instruction model

This folder contains a formal Coq machine model for a subset of x86-64
instructions. It defines the machine encoding and per-lane behavior of
unmasked AVX-512 instructions operating on eight 64-bit lanes. It also
executes programs organized into basic blocks with scalar register operations,
stack memory, direct calls, conditional jumps and returns. [File-by-file guide](CODE_LAYOUT.md)

## How the model is checked

The vector corpus combines fixed cases for each vector instruction family with a
deterministic boundary sweep. Each backend uses the same inputs. [Fixed cases](tests/cases) · [Boundary sweep](tests/overflow.py)

| Backend | What it checks |
| --- | --- |
| `model` | Coq evaluates `encodable`, `encode` and `run`. The runner checks all eight destination lanes against any supplied `expected` vector and the encoding against any supplied `bytes`. The boundary sweep computes its expected vectors independently with Python integers. [Coq oracle](tests/model/Oracle.v) |
| `xed` | Adds an independent decode of Coq's bytes with Intel XED in 64-bit mode. Checks include instruction length, mnemonic, operand order and access, registers, immediate, vector width, EVEX modifiers and load addressing. [XED decoder](tests/xed/decode.c) |
| `native` | Adds execution on x86-64 Linux with AVX-512F, DQ and IFMA. The runner verifies that the assembled instruction matches Coq's bytes, executes it in a child pinned to the reported CPU, and compares all 32 ZMM registers. The Coq lemma `preserved` establishes that each register other than the destination keeps its input value. [Native runner](tests/native/backend.py) |
| `all` | Runs all three checks. |

- **Arithmetic.** Addition, subtraction and multiplication cover operands around powers
  2²⁶, 2³², 2⁵¹, 2⁵² and 2⁶³, and the largest qwords. Exact results of
  2⁶⁴−1, 2⁶⁴ and 2⁶⁴+1 must produce 2⁶⁴−1, 0 and 1. [Multiplication boundary vector](tests/cases/arithmetic.jsonl)
- **IFMA.** Both forms ignore operand bits above bit 51 and select the low or
  high 52 bits of the product. Tests choose the accumulator so the sum lands
  just below, at or just above 2⁵² and 2⁶⁴. A sum of 2⁵² survives and a sum
  of 2⁶⁴ wraps to zero. Register and full-vector memory sources share the
  same arithmetic. Memory cases cover unaligned data, aliased accumulator/LHS,
  high registers, SIB bases, and zero, compressed and full displacements.
  [Register vectors](tests/cases/ifma.jsonl) · [Memory vectors](tests/cases/ifma-memory.jsonl)
- **Shifts.** Left and logical right shifts cover all 256 immediate counts,
  including inputs with bit 63 set. Counts from 64 through 255 produce zero
  in every lane.
- **Registers and loads.** Cases cover aliased source and destination registers,
  loads from unaligned private storage, compressed 8-bit displacement limits
  and both signed 32-bit displacement extremes. [Move and load vectors](tests/cases/move.jsonl)

The default native run also compares four programs written in Coq's Intel
notation with independently assembled `.S` files. It checks the entire
linked byte sequence before executing each program on the pinned CPU.

| Probe | Observations |
| --- | --- |
| `control` | A callee decrements ECX and the caller branches on its ZF. Eight inputs exercise both branch outcomes and 32-bit wraparound. The harness checks RAX, RCX, ZF and stack restoration. [Coq](tests/Control.v) · [Assembly](tests/native/control.S) |
| `mixed` | Seven seeds drive one to three loop iterations across scalar and vector blocks. An unaligned load, wrapping addition, aliased IFMA and store feed the next iteration. A SIMD instruction separates `dec` from `jne`. The harness checks RCX, ZF, stack restoration, all 32 ZMM registers and the stored vector plus both adjacent cells. [Coq](tests/Mixed.v) · [Assembly](tests/native/mixed.S) |
| `prologue` | Checks 32- and 64-bit immediates, broadcasts from RAX, stack adjustment in both directions, both `lea r8` encodings, vector loads and stores, and `vzeroupper`. Seven seeds exercise a private stack and three distinct unaligned buffers. The comparison covers RAX, RCX, R8 relative to the frame, restored RSP, all 32 ZMM registers, both inputs, output, stack scratch and guard cells. [Coq](tests/Prologue.v) · [Assembly](tests/native/prologue.S) |
| `aligned` | Eight seeds cover all four SysV stack padding cases and saved RBP values through `2^64−1`. Checks `push`/`pop rbp`, register copies, `and rsp,-64`, scratch-relative `lea` with zero and nonzero displacements, copies from RDX to RCX and RSP to R9, two nested calls, all ZMM registers, saved stack qwords, vector memory and guards. [Coq](tests/Aligned.v) · [Assembly](tests/native/aligned.S) |

The aligned probe also covers `MOV rax, imm32` (`48 c7 c0`) with zero,
one, the scalar reducer's constant, and `2^31-1`, observing each value through
a broadcast to a separate ZMM register. `MovRaxImm32` accepts only
`0 <= imm < 2^31`, where sign extension is the identity; Coq domain tests
reject negative immediates and `2^31`.

Consumers can check that the probes exercise every scalar and control-flow
form in their program by proving `uncovered_caller_forms program = []`.
Forms distinguish the operation, instruction length, scalar destination or
address base where applicable, and displacement direction. Coverage counts
instructions in blocks reached by the default probe inputs. [Coverage check](tests/CallerForms.v)

The comparisons cover observable effects of successful executions. A theorem
that an independent ISA model decodes every encodable instruction in full and
agrees with its effects for every valid input remains open. Faults and caller
behavior have separate proof obligations. [Proof status](proofs/README.md)

## Model files

Each instruction family defines its lane operations and encoders, with links to
the corresponding Intel Intrinsics Guide entries. The families share the EVEX
encoding helpers in `X86.v`. [Moves](Move.v) · [Arithmetic](Arithmetic.v) · [Bitwise operations](Logic.v) · [Shifts](Shift.v) · [IFMA](IFMA.v) · [Encoding helpers](X86.v)

`Machine.Instructions` exposes `encodable` to check operands, `encode` to
produce bytes, and `asm_of` to render Intel syntax. `run load code registers`
returns the final lane value of each register. The caller supplies unsigned
64-bit register values and a read-only memory view. For lane `j`,
`load base disp` supplies the unsigned little-endian qword at
`GPR[base] + disp + 8*j`. [Instruction interface](Instructions.v)

`agreement_sound` proves when two executions of a vector instruction list
agree on selected output registers. It tracks which input registers and loads
agree, including the case where self-XOR clears an arbitrary old value.
[Register dependency lemmas](Dependencies.v)

## Basic blocks and machine state

A program contains addressed blocks, straight-line vector fragments and
explicit padding. A block has a body and a terminator (`Next`, `CallRel32`,
`JneRel8` or `Ret`). `image` encodes them in layout order. `valid_program`
checks operand ranges, contiguous block addresses, and that every static
target and fallthrough starts a block. [Program and encoder](ProgramLayout.v)

`IntelSyntax.v` lets a Coq program use Intel mnemonics and named registers.
`ops[ ... ]` denotes a scalar block body, `vecs[ ... ]` a vector instruction
list, and `ends[ ... ]` a terminator. A local label denotes a byte address.
`assemble` resolves each call or conditional jump relative to the end of that
instruction. The native control-flow probe uses this notation. [Intel notation](IntelSyntax.v) · [Assembler](Assembly.v) · [Control-flow probe](tests/Control.v)

`step` executes one block on the program counter, GPRs, zero flag, ZMM
registers and memory. A call pushes a return PC to stack memory and a return
pops it. `returns` means a finite sequence of these steps reaches the external
caller. `path_returns` lets a proof compute the control path and effective
addresses once for arbitrary vector values. [Execution semantics](Blocks.v)

`step_sequential` proves that executing a fetched block gives the same
optional machine state as stepping its instructions in order and then its
terminator. Both executions return the same PC, flags, registers and memory
on success, or both return `None`. The instruction sequence expands every
vector fragment, checks each load when it executes and advances the PC by
each instruction's encoded length. [Block theorems](BlockSequence.v) · [Vector instruction refinement](VectorSequence.v)

`block_singleton` covers one body instruction followed by fallthrough.
`block_empty` covers a lone terminator. `block_cut` allows a cut at any
instruction boundary, including inside a vector fragment. `step_split`
applies this law to program execution when the two blocks can be fetched
at their respective addresses. The first falls through and the second
retains the original terminator. `block_laws_suffice` proves by induction
that the empty-body, singleton and split laws determine the result for
every instruction list. [Statements and proofs](BlockSequence.v)

`execution_memory_frame` proves that every finite execution preserves each
vector cell without write permission and each return-address slot outside
the layout's permitted slots. `control_trace_independent` proves that changing
the initial ZMM values or vector memory preserves the entire sequence of
control states when the program, layout and initial scalar control agree.
`step_failure_independent` covers a rejected step under the same conditions.
These properties concern the architectural model. [Execution properties](ExecutionProperties.v)

`record_path_sound` relates an ordered trace of vector effects, calls and
returns to the executed path. `replay_agrees` proves that the vector and
return-slot views agree with one little-endian byte memory when they agree
at entry and each writable cell is disjoint from every other tracked cell.
`replay_frame` proves that every byte outside the trace's write footprint
keeps its entry value. [Memory events](MemoryTrace.v) · [Byte memory](FlatMemory.v)

`state_words` requires unsigned 64-bit integer GPR values, all eight lanes of
the vector registers, and the vector memory values. `step_preserves_words`
and `execution_preserves_words` prove preservation; `recorded_prefix_words`
covers the intermediate vector effects within blocks. Symbolic pointers and
PCs retain their separate region/placement interpretation. [Word bounds](WordBounds.v)

`read_word` reconstructs a qword from eight little-endian bytes.
`read_word_encoded` returns the encoded integer modulo `2^64`, while
`read_word_exact` proves equality for a bounded word. `agrees_read_vector`
therefore turns byte agreement into exact logical loads. The converse
round trip constructs a matching logical data view directly from any valid
byte array. Word/vector stores and saved return words have corresponding
read-back lemmas, and replay preserves byte bounds. [Byte decoding proofs](ByteMemory.v)
Both certificates use these results to construct concrete entries and
state their arithmetic results on output bytes. [Pow2 concrete ABI proof](../crate/pow2/coq/Pow2Bytes.v) · [Double4 concrete ABI proof](../crate/double4/coq/Double4Bytes.v)

`aligned_region_and` proves that clearing the low six bits of a concrete
address equals alignment of its relative offset when the region origin is
64-byte aligned. Consumers of `AlignRsp64` must establish that placement
condition. Double4 proves it for its stack frame, including all four SysV
padding cases. `SavedWord` stack entries hold saved RBP qwords in the same
memory as return addresses; they are never executable PCs. [Alignment](Alignment.v)

The model tracks relocatable byte offsets. The supplied memory layout
distinguishes read-only vectors, writable vectors and individual return
qwords. Vector accesses must start at a 64-byte cell boundary relative to
the region origin. Its physical base can be unaligned except for a region
used by `AlignRsp64`. The scalar subset
models the zero flag written by `DEC`. Stack-pointer arithmetic and alignment make ZF
unknown, and executing `JNE` requires a known ZF. [State and permissions](MachineState.v) · [Intel instruction reference, Vol. 2](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)

## Run the conformance suite

Run these commands from this directory with Python 3, `coqdep` and `coqc` on
`PATH`. The native backend also needs a C compiler with an AVX-512-capable
assembler. Select one case with `--case` and its stable ID.

```sh
python3 -B tests/run.py --backend model
python3 -B tests/run.py --backend native --case arithmetic/mul-wrap-boundary
python3 -B tests/run.py --backend native --probe mixed
python3 -B tests/run.py --backend native --probe prologue
python3 -B tests/run.py --backend native --probe aligned
```

For `xed` or `all`, set `XED_KIT` to a static Intel XED kit. To build one in a
new directory, use the script below with Git, Python 3 and a C toolchain.
It fetches pinned revisions of XED and mbuild.

```sh
export XED_KIT="$PWD/../xed-kit"
tests/xed/build-kit.sh "$XED_KIT"
python3 -B tests/run.py --backend all --report fixed-report.json
python3 -B tests/run.py --backend all --random 1000 --seed 42 --report campaign-report.json
```

`--random N` adds N seeded cases, cycling through the modeled mnemonics.
`--cases FILE` replaces the default corpus with a JSONL file and can be
repeated. Successful reports retain every case's ID, operands, instruction
bytes, all 32 initial ZMM registers, memory input and optional expected result.
Defaults are expanded into explicit inputs, so the report can be replayed
without the original corpus or generator. Reports also retain the inputs
and bytes of any block probes that ran.

Reports distinguish `campaign_seeds` from `export_seeds`, using the provenance
recorded in each case. `--seed` affects only newly generated `--random` cases;
it does not describe imported inputs. Unrecorded seeds are left unknown.
Metadata includes case counts by mnemonic, the backend, CPU and microcode,
Coq, Python and C compiler versions, and SHA-256 digests of the complete
retained corpus, Coq sources and test harness, plus the XED library when used.

## Case format and replay

Each JSONL row has an `id` and an `instruction` array in Intel operand order.
Register operands use architectural register numbers. A load takes a ZMM
destination, GPR base and signed byte displacement.

| Case field | Meaning |
| --- | --- |
| `registers` | Optional map from ZMM number to eight unsigned 64-bit integers in low-to-high lane order. Register `r` defaults to lanes `8*r` through `8*r+7`. |
| `memory` | Required for a load. Supplies eight unsigned qwords at the effective address. |
| `expected` | Optional destination vector. Each checked-in case has one verified on an AMD EPYC 9555P. |
| `bytes` | Optional complete instruction encoding in hexadecimal. |
| `campaign_seed` | Optional seed used by the conformance runner to generate this case. |
| `export_seed` | Optional seed used by the release proof exporter to generate this case. |

Case readers must preserve all 64 bits of each JSON integer. A mismatch exits
nonzero and writes `machine-failure.json`, or the path supplied to `--failure`.
The vector failure record includes the initial ZMM registers, memory input, available bytes,
Coq result, expected and observed values, and run metadata. A block-probe failure records the program,
its bytes, the counts or seeds, and both observations. A `mixed` observation row contains the
seed, RCX, ZF, 256 register qwords in register and lane order, and the 24 memory qwords.
A `prologue` row contains the seed, RAX, RCX, the R8 frame offset, the 256
register qwords, 248 stack qwords and 32 qwords for each of the output and two inputs.
Replay accepts both failure records and complete successful reports
(`schema_version: 2`). It checks the retained corpus digest before running
a successful report, and reruns any recorded native block probes. Older
successful reports lack the inputs needed for replay and are rejected;
legacy failure records remain supported. Replay uses the recorded backend
by default. A repeated mismatch writes a sibling
`.replay.json` file unless `--failure` specifies another path.

```sh
python3 -B tests/run.py --replay machine-failure.json --failure replay-failure.json
python3 -B tests/run.py --replay campaign-report.json --report replay-report.json
```

## Build independently

From this directory, with Coq and GNU Make installed, run

```sh
coq_makefile -f _CoqProject -o Makefile
make
coqchk -Q . Machine Machine.BlockSequence Machine.ExecutionProperties Machine.Dependencies \
  Machine.WordBounds Machine.ByteMemory
```

A consumer maps the compiled directory with `-Q /path/to/model Machine` and
imports the interfaces with `From Machine Require Import Instructions Blocks.`
