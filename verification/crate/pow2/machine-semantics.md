# Machine instruction semantics for `ed25519_simd_pow2_ifma`

Coq proves `pow2_spec` for a handwritten model of this routine. To apply the
theorem to native execution, check that each encoding selects the intended
instruction and operands, and that its modeled effect agrees with the
architecture. Intel specifies both in the opcode table and the **Operation**
pseudocode for each instruction. [Intel Software Developer’s Manual, Vol. 2](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)

## Vector arithmetic

The square and multiply bodies in `pow2_program` use Intel notation that
elaborates directly to typed Coq instructions. For each instruction, `encode`
computes its bytes and `bits` defines its effect on one 64-bit lane. The
certificate binds the encoding of the entire program to the linked symbol's
bytes and states the result of executing that same program.
[Generate and inspect Program.v](README.md#check-the-release-executable) · [Intel notation](../../machine/isa/IntelSyntax.v) · [Interpreter and encoder](../../machine/isa/Instructions.v) · [Audit contract](coq/Audit.v)

Each family defines its lane effects and encodings together. The shared model takes explicit register operands and a memory view. The
pow2 prologue broadcasts the constants into ZMM28 and ZMM29, and each
multiply reads its right operand through the address in R8. [Moves and loads/stores](../../machine/isa/Move.v) · [Addition and multiplication](../../machine/isa/Arithmetic.v) · [Bitwise operations](../../machine/isa/Logic.v) · [Shifts](../../machine/isa/Shift.v) · [IFMA](../../machine/isa/IFMA.v) · [EVEX encoding](../../machine/isa/X86.v)

At symbol offset `+0x062d`, the bytes `62 82 d5 40 b4 f4` encode
`vpmadd52luq zmm22, zmm21, zmm28`. Coq reads this as `(22, Madd false 21 28)`.
For each lane, `bits` multiplies the low 52 bits of ZMM21 and ZMM28, takes
the low 52 bits of that product (`false`), and adds them to the old ZMM22
modulo `2^64`. The `true` case selects product bits 103 through 52 for
`vpmadd52huq`. [Assembly source](../../../src/wide/avx512ifma/pow2.S) · [IFMA semantics and encoding](../../machine/isa/IFMA.v)

## Caller, memory, and control flow

The executable caller is a list of basic blocks at symbol-relative byte
offsets. Each block runs its body, then executes its terminator. A near
`call` pushes the fallthrough PC at RSP−8. A `ret` reads the saved PC and
advances RSP by eight. `dec ecx` writes the 32-bit result and sets ZF.
`jne` consumes that flag and the signed byte displacement. The first loop's
`jne` reaches `+0x0113` with ZF clear and `+0x011c` with ZF set.
[Instruction and block semantics](../../machine/execution/Blocks.v)

`block_layout_checked` checks the layout and every static edge,
including the fallthrough after a call. `control_path_checked` follows the
real counters and return slots to the external caller. It proves that the
resulting loads, stores, and kernel invocations occur in the order used by the
arithmetic proof. The finite search supplies a witness for the unbounded
`returns` relation. Kernel dependency proofs justify reusing the arithmetic
lemmas with arbitrary incoming scratch registers. [Control and data proofs](coq/Execution.v) · [Register dependencies](../../machine/execution/Dependencies.v)

The public contract separately guarantees `output_initialized`: every byte
at offsets 0 through 639 from the entry output pointer occurs in the write
footprint of that returning execution. The proof derives the ten output
stores from the checked control path and proves that their 64-byte spans
cover the whole output. This guarantee requires no arithmetic limb bound
and holds for arbitrary initial output contents. [Contract](coq/Pow2Memory.v) ·
[Trace coverage](coq/FrameProof.v) · [Regression examples](coq/ByteEntryTests.v)

The byte proof assigns concrete bases to the buffers, stack and code, and a
concrete address to `Caller`. It records stores, calls and returns along the
executed path. A vector store writes 64 little-endian bytes and a call
writes the eight bytes of its relocated fallthrough PC to the same memory.
Starting from matching bytes, both logical memory views agree with this
memory after every trace prefix. Every return reads the bytes of the most
recent live return address. The caller must supply accessible memory with
the placement and entry contents in the contract.
[Byte semantics](../../machine/memory/FlatMemory.v) · [Placement and contract](coq/Pow2Memory.v) · [Proof](coq/FrameProof.v)

The certificate also accepts a concrete entry consisting of a byte array and
unsigned register words. It constructs the input, scratch and output views by
decoding that array and proves initial agreement, including when the inputs
overlap. The word-bound invariant is preserved through execution and every
recorded vector-effect prefix. Under this invariant, byte agreement implies
exact qword reads; serialized values that differ by `2^64` cannot represent
different logical operands. The final field result is stated directly on the
decoded output bytes. Pointer relocation still uses `placement`, and this
byte correspondence remains a theorem about the specified machine model.
[Concrete entry and result](coq/Pow2Bytes.v) · [Word invariant](../../machine/execution/WordBounds.v) · [Byte decoding](../../machine/memory/ByteMemory.v)
