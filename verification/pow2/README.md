# Paired field exponentiation

**Audit one statement.** `pow2_contract symbol_bytes` is the complete public
claim for `ed25519_simd_pow2_ifma`. Its only parameter is the byte sequence
of the linked symbol. [Read the statement in Audit.v](coq/Audit.v)

1. **Field result.** `pow2_spec a b out` applies when every input limb is
   below `2^52`. For each of eight lanes, the two halves of `out` represent
   the corresponding inputs raised to `2^252 − 3` modulo `2^255 − 19`.
   Each input and each output half occupies 320 bytes. Limb `i` of lane `j`
   is the little-endian qword at byte offset `64*i + 8*j` and has weight
   `2^(51*i)`. Output limbs 0, 2, 3 and 4 are below `2^51`. Limb 1 is at
   most `2^51 + 511`. [Field specification](coq/FieldSpec.v)
2. **Code.** Encoding `pow2_program` produces exactly those bytes, including
   padding. The return and field guarantees apply to this same program.
   Its operands, block layout, and static control-flow targets pass
   the machine model's validity check.
   [Assembly source](../../src/wide/avx512ifma/pow2.S) · [Encoding and validity](../machine/ProgramLayout.v)
3. **Registers and return.** From every valid ABI entry, execution returns
   with RBX, RBP and R12–R15 equal to their entry values and RSP advanced
   by eight bytes. The result is read at the output pointer supplied in RDI.
   [Entry, layout, and output definitions](coq/Pow2ABI.v) · [Execution and return](../machine/Blocks.v)
4. **Output initialization.** Every one of the 640 bytes at the entry RDI
   pointer is written before return, regardless of the input limb bounds or
   previous output contents. This definite-write guarantee justifies the
   Rust caller's `assume_init()` independently of the conditional field result.
   [Initialization contract](coq/Pow2Memory.v) · [Trace coverage proof](coq/FrameProof.v)
5. **Writes and saved addresses.** Let `S` be entry RSP. Every vector store
   fits entirely in the 640-byte output or the stack scratch area
   `[S−1928, S−8)`. An internal call writes its eight-byte return address
   at `S−1936` and can reuse that slot only after the matching return.
   Every return reads its expected address from the same byte memory as the
   vector stores. The caller's eight bytes at `S` stay intact throughout.
   These guarantees hold independently of the arithmetic limb bound.
   [Memory and register contract](coq/Pow2Memory.v) · [Proof](coq/FrameProof.v)
6. **Concrete bytes and word bounds.** A `concrete_entry` supplies one byte
   array, unsigned register values, the ABI pointers and the caller's saved
   return address. `entry_from_bytes` constructs the logical memory views;
   their initial agreement is proved. Every integer register value and vector
   qword remains in `[0, 2^64)` during modeled execution. At every memory-event
   prefix, reading eight little-endian bytes reconstructs the exact logical
   vector qword. The final output, read directly from bytes, satisfies
   `pow2_spec`. Identical and partially overlapping read-only inputs use the
   same underlying bytes. [Concrete entry and result](coq/Pow2Bytes.v) ·
   [Word bounds](../machine/WordBounds.v) · [Byte round trips](../machine/ByteMemory.v)

The byte proof covers every non-wrapping placement satisfying `valid_placement`.
The output and stack must be disjoint from each other, the inputs and the
symbol. The read-only inputs may overlap if their bytes agree. Native use
requires accessible buffers, a SysV-aligned stack with 1,936 bytes available
below RSP, a valid caller return address, and AVX-512F/DQ/IFMA instruction
behavior matching the model. The Rust caller supplies the limb bound. The
certificate covers the optional `asm-pow2` backend.
[Instruction semantics and model assumptions](machine-semantics.md) · [Rust call boundary](../../src/wide/avx512ifma/field.rs)

## Check the release executable

From the repository root, supply the unstripped x86-64 Linux ELF and a new
output directory. Requires Python 3, LLVM MC, GNU binutils, and Coq (`coqdep`, `coqc`, and `coqchk`).

```bash
elf=/path/to/unstripped-release-elf
python3 -B verification/pow2/coq_proof.py "$elf" --output ./pow2-audit
```

**The implementation lives in `pow2.S`.** The `asm-pow2` feature assembles it
directly with Rust's built-in assembler. The optional `verify-asm-pow2`
build and the release checker use LLVM MC to assemble the same file and
generate `Program.v` from its expanded Intel mnemonics, grouped into basic
blocks. Coq uses this program for both encoding and execution. It derives the
sequence of squares, multiplies and saves by following the caller's branches.
[Assembly source](../../src/wide/avx512ifma/pow2.S) · [Listing generator](generate_listing.py) · [Arithmetic trace](coq/Linked.v)

The `verify-asm-pow2` build embeds the bytes that Coq checked. For a release
audit, the checker extracts the linked symbol into `pow2-audit/ObjectBytes.v`.
Coq proves that encoding the generated program produces those exact bytes,
including alignment padding. The checker rejects axioms, runs `coqchk`, and
prints the verified symbol's SHA-256. [Rust build](review.py) · [ELF byte extraction](coq_proof.py) · [Certificate](coq/Object.v)

The output directory retains every generated and handwritten Coq source,
the assembly and checker sources, the raw symbol bytes (`symbol.bin`),
the assumption-check output (`assumptions.txt`) and `coqchk.log`.
`manifest.json` identifies the public theorem, ELF and symbol hashes,
tool versions and successful proof checks, and hashes each retained source
and evidence file. If `--cases` is supplied, the directory also retains
an exact copy as `conformance.jsonl`, with its export seed and case count
recorded in the manifest. [Evidence writer](evidence.py)

The retained `_CoqProject` lists all sources needed to rebuild the proof
without the repository or assembler. In `pow2-audit`, run:

```bash
set -e
for proof_source in $(coqdep -sort -f _CoqProject); do
  coqc -Q machine Machine -Q arithmetic ProofArithmetic "$proof_source"
done
coqchk -Q machine Machine -Q arithmetic ProofArithmetic -silent Object
```

Compiling `Object.v` must print `Closed under the global context` for
`assembled_symbol_correct`. The saved manifest and logs record the original
check; rebuilding allows the auditor to repeat it.

To inspect the instructions, open `pow2-audit/Program.v` next to
`pow2-audit/pow2.expanded.S`. Both listings use symbol-relative offsets.
The assembly listing includes the instruction bytes, and each mnemonic in
`Program.v` is Coq notation for a typed instruction. To compare with the
linked bytes, disassemble the same ELF.
[Intel notation](../machine/IntelSyntax.v)

```bash
objdump -d -M intel --disassemble=ed25519_simd_pow2_ifma "$elf"
```

To inspect the theorem binding, start `coqtop -quiet -Q machine Machine` in
`pow2-audit` and enter

```coq
Require Object Audit ObjectBytes.
Check Object.assembled_symbol_correct : Audit.pow2_contract ObjectBytes.symbol_bytes.
```

To generate the two readable listings without a release ELF, run

```bash
python3 -B verification/pow2/generate_listing.py ./pow2-listing
```

CI also runs an independent Z3 check of the linked disassembly.
[Z3 checker](check.py) · [CI workflow](../../.github/workflows/ci.yml)

## Check native instruction coverage

Add `--cases` to the release proof command to export one test per square and
multiply instruction, including its symbol-relative offset, actual linked
bytes, symbol SHA-256, export seed and complete initial state. Run the exported
corpus with the shared vector conformance runner. The export also checks that every
scalar and control-flow instruction form in the linked program occurs in
the machine probes. The first runner invocation below executes those probes
and the fixed corpus. The second executes each exact linked kernel row.
Both require an AVX-512F/DQ/IFMA host and an XED kit. [Coverage check](coq/ExportCases.v) · [Backend setup](../machine/README.md#run-the-conformance-suite) · [Case format and replay](../machine/README.md#case-format-and-replay)

```bash
python3 -B verification/pow2/coq_proof.py "$elf" --output pow2-coverage-audit --cases pow2-rows.jsonl --seed 42
python3 -B verification/machine/tests/run.py --backend all --report fixed-report.json
python3 -B verification/machine/tests/run.py --cases pow2-rows.jsonl --backend all --report pow2-report.json
python3 -B verification/machine/tests/run.py --replay pow2-report.json --report replay-report.json
```

CI retains both conformance reports, the exported corpus and the release
audit directory as one artifact. The reports embed their complete test inputs;
the release manifest binds the exported corpus to the exact proof sources and
linked symbol used by the check.
