# ISA refinement proofs

The intended theorem quantifies over every encodable instruction and every
architectural state satisfying its preconditions. Decoding the bytes in an
independent ISA specification must consume the full encoding, and one step
in that specification must agree with the modeled register and memory effects.

An independent ISA refinement theorem is still open. The [conformance
suite](../README.md#how-the-model-is-checked) supplies executable comparisons for individual cases.

For control transfers, the refinement should cover the exact fallthrough PC,
the target of both conditional paths, and the eight-byte return address
pushed by a call and consumed by a return. The model already relates its own
vector cells and return slots to a shared little-endian byte memory at
concrete addresses, including unaligned vector bases. A proof against an
independent ISA would also establish that its loads, stores, calls and returns
access those same addresses with the same widths and values.
[Control transfers](../execution/Blocks.v) · [Trace correspondence](../memory/MemoryTrace.v) · [Byte memory proof](../memory/FlatMemory.v)

[ScalarRefinement.v](../execution/ScalarRefinement.v) now relates the symbolic GPRs and
PCs to concrete qword values and an actual ZF. It proves scalar-operation and
stack-transfer correspondence, including sign extension, modulo-64-bit pointer
arithmetic, alignment, branch targets, and byte writes. Bodies and blocks compose
these local results. The shared theorem `scalar_model_refinement_checked`
applies to each program under its stated operation-placement and stack-access
premises. Both sides use this repository’s semantics. The [shared audit
surface](../../README.md#shared-audit-surface) describes the remaining hardware
correspondence. Vector effects remain covered by the existing lane and byte proofs.

The concrete scalar definitions follow the instruction descriptions in Intel's
[Software Developer's Manual](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
They are still handwritten semantics, not an independent ISA specification.
