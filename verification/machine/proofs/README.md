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
[Control transfers](../Blocks.v) · [Trace correspondence](../MemoryTrace.v) · [Byte memory proof](../FlatMemory.v)
