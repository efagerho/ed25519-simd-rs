# Formal verification

This directory contains the Coq proofs for the crate’s x86-64 assembly routines.

| Folder | Contents |
| --- | --- |
| [machine/](machine/README.md) | The x86-64 instruction model, memory and calling conventions, and tests against native hardware and Intel XED. |
| [arithmetic/](arithmetic/README.md) | General proofs about integer expressions, polynomial identities, bounds, and radix representations. |
| [curve25519/](curve25519/README.md) | Field and scalar arithmetic, Edwards point formulas, and their relationship to the group law. |
| [crate/](crate/README.md) | Shared SIMD representations, the public theorem for each assembly routine, and instructions for auditing a linked executable. |

## Shared audit surface

Coq checks a statement about a program in this repository’s machine model.
For a native release, the auditor checks that the CPU executes the certified
bytes, that the model describes their effects, and that the theorem supplies
the guarantees the Rust caller needs.

**Instructions and control flow.** The encoder and interpreter are handwritten.
Check that the bytes select the same opcode, registers, operand order, widths,
and effective addresses that the interpreter uses. For example, IFMA consumes
the low 52 bits of both operands and adds the selected half of the product to
the old destination modulo `2^64`. For scalar instructions, check the flags
consumed by branches, signed displacements, stack adjustments, and the return
address pushed by a call. Instruction fetch uses an immutable code image.
The block model tracks the zero flag consumed by conditional jumps.
`returns` requires a finite execution that reaches the caller, so a rejected
access cannot count as success. [Vector semantics and encoding](machine/isa/Instructions.v) · [Scalar encoding and layout](machine/isa/ProgramLayout.v) · [Block execution](machine/execution/Blocks.v) · [Linked calls](machine/execution/LinkedCalls.v)

**Memory and the ABI.** Field kernels and scalar reduction model pointers as a
region plus a byte offset. A placement maps them into one flat array of bytes valued 0 through
255. The model uses region permissions for reads, writes, and stack slots.
Check address calculations, 64-byte vector accesses, eight-byte saved words,
little-endian qwords, lane order, and the SysV saved-register set. These definitions give “preserved” and
“returned” their meaning. Coq then proves that, under the routine’s placement
conditions, vector data and stack slots agree with **one byte memory** as
execution proceeds, including the word consumed by a return. Real callers
must supply accessible memory with the specified extents, alignment, and
aliasing, on a CPU and OS that enable the required instructions. Page faults,
concurrent interference, and timing or side-channel behavior lie outside
this execution model. [Pointers and permissions](machine/execution/MachineState.v) · [Address placement and writes](machine/memory/FlatMemory.v) · [Byte execution](machine/memory/ByteExecution.v) · [SysV contract](machine/abi/SysV.v)

**Packed byte operations.** Digest conversion and table staging use a straight-line interpreter
for one RDI-relative buffer. Check byte order within qwords, 128-bit unpack
boundaries, shuffle immediates, and the EVEX element width. A row read uses
the latest 64-byte store to the same row or the incoming flat memory.
Coq proves that each in-bounds store writes precisely its 64 bytes in flat
memory. The linked call and return use the shared stack semantics. [Packed interpreter](machine/execution/Packed.v) · [Row store proof](machine/memory/PackedMemory.v) · [Hardware probe](machine/tests/PackedRows.v)

**Indexed loads.** Staging executes each register-and-load block against its
incoming flat memory. Check 32-bit zero extension, 64-bit effective addresses,
SIB and scaled displacements, vector upper halves and the width recorded for
each memory operand. The contract checks those read extents and the alignment
of the destination for the packed stores. The model relies on the caller to
map the stated buffers and code. [Indexed encoder](machine/isa/IndexedLoad.v) · [Block semantics](machine/execution/IndexedLoads.v) · [Hardware probe](machine/tests/Indexed.v)

**Mask-dependent execution.** The torsion and small-order routines branch on values
computed by all eight lanes. The functional model reconstructs EAX comparisons
and the zero flag from a mask self-test. RIP-relative qwords and instruction
fetches use the immutable symbol images at their linked addresses. A native
load must preserve their relative placement. Check lane-to-bit order, mask
width, both branch targets and the mapping of each input to its read-only qword view. Nested
return addresses, saved RBP and vector spills share an aligned, tagged
stack. Interpreting that stack as private caller memory disjoint from the
inputs and code is an additional trust boundary. A flat-byte execution
refinement for this model remains open. Coq proves that its lifted vector
operations agree with the shared lane semantics. Native probes compare
the mask-dependent instructions with the CPU. [Mask execution](machine/execution/MaskTrace.v) · [Lane refinement](machine/execution/CircuitFacts.v) · [EAX probe](machine/tests/Mask.v) · [Filter probe](machine/tests/Filter.v)

The deferred ZIP-215 decoder uses tagged addresses for its outer caller and
field slots for its local load, store and mask instruction groups. The shared
pow2 callee has a flat-memory certificate. For the rest of the decoder,
matching the grouped operations to native reads and writes remains part of
the audit. [Decoder memory boundary](crate/decompress_r/README.md#what-to-audit)

**Mathematical meaning.** Check the field prime, scalar order, radix and limb
weights, Edwards curve and group law, and the predicates saying which point
an XYZ, extended, or cached representation denotes. An incorrect modulus or
coordinate convention changes the meaning of every theorem that uses it.
The soundness of the polynomial and interval checkers, the primality proof,
and the connection from coordinate formulas to the group law are themselves
kernel-checked results. [Arithmetic library](arithmetic/README.md) · [Curve definitions and representation theorems](curve25519/README.md)

**Proof and release evidence.** Trust rests on Coq’s kernel and a working proof
checking toolchain. A closed theorem establishes its stated contract in the
model. The listing generator must produce a program whose encoding equals the
supplied bytes. Identifying those bytes in the intended executable is an
external check. The scalar refinement theorem relates two internal views of
execution under explicit address and stack premises. Intel XED checks decoding
and native comparisons check execution on concrete cases. Refinement to an independent x86 ISA
specification remains open. [Hardware conformance](machine/README.md#how-the-model-is-checked) · [ISA refinement obligation](machine/proofs/README.md) · [Release audit procedure](crate/README.md#what-to-audit)
