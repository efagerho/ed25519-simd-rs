# Paired field exponentiation

In each of eight lanes, `ed25519_simd_pow2_ifma` raises each of two field
elements to `2^252 − 3` modulo `2^255 − 19`. The field result requires
input limbs below `2^52`. Every valid ABI call returns and initializes both
outputs, including calls with limbs outside that bound.

Public theorem in `Ed25519Simd.Pow2`. [Statement](coq/Audit.v) · [Proof](coq/Object.v)

```coq
Object.assembled_symbol_correct : Audit.pow2_contract ObjectBytes.symbol_bytes
```

## What to audit

1. **Exponent and output order.** Read `pow2_spec`. It decodes five little-endian
   qwords per lane from each input, with limb weights `2^(51*i)`. The first 320 output bytes must
   correspond to input A and the next 320 to B. Output limb 1 may reach
   `2^51 + 511`. The other four must be below `2^51`.
   [Field specification](coq/Pow2Spec.v)
2. **Pointers and initialization.** Compare `concrete_entry` and
   `concrete_pow2_contract` with the Rust call. RDI supplies a distinct
   640-byte output, RSI and RDX supply 320-byte inputs that may coincide or
   partially overlap. Both inputs are decoded from the same bytes. Check that
   `output_initialized` covers the whole Rust `[WideFe; 2]` before
   `assume_init()`, independently of the limb premise.
   [Byte contract](coq/Pow2Bytes.v) · [Rust caller](../../../src/wide/avx512ifma/field.rs) · [Aliasing and coverage witnesses](coq/ByteEntryTests.v)
3. **Stack and return.** For entry RSP `S`, check the writable vector scratch
   range `[S−1928, S−8)`, the internal call slot at `S−1936`, and the caller’s
   return word at `S`. The stack and output need the separations in
   `valid_placement`. The return advances RSP by eight and preserves the SysV
   saved registers. [Permissions and write footprint](coq/Pow2Memory.v) · [Entry layout](coq/Pow2ABI.v)

Apply the [crate audit procedure](../README.md#what-to-audit) to this symbol.
The [instruction notes](machine-semantics.md) illustrate the shared model on
this implementation.

## Check the release executable

From the repository root, supply the unstripped x86-64 Linux ELF and a new
output directory. Requires Python 3, LLVM MC, GNU binutils, and Coq (`coqdep`, `coqc`, and `coqchk`).

```bash
elf=/path/to/unstripped-release-elf
python3 -B verification/crate/pow2/coq_proof.py "$elf" --output ./pow2-audit
```

**The implementation lives in `pow2.S`.** The `asm` feature assembles it
alongside the other backends with Rust's built-in assembler. The optional
`verify-asm-pow2` build and the release checker use LLVM MC to assemble the same file and
generate `Program.v` from its expanded Intel mnemonics, grouped into basic
blocks. Coq uses this program for both encoding and execution. It derives the
sequence of squares, multiplies and saves by following the caller's branches.
[Assembly source](../../../src/wide/avx512ifma/pow2.S) · [Listing generator](generate_listing.py) · [Arithmetic trace](coq/Linked.v)

The `verify-asm-pow2` build embeds the pow2 bytes that Coq checked. For a release
audit, the checker extracts the linked symbol into `pow2-audit/Pow2/ObjectBytes.v`.
Coq proves that encoding the generated program produces those exact bytes,
including alignment padding. The checker rejects axioms, runs `coqchk`, and
prints the verified symbol's SHA-256. [Rust build](review.py) · [ELF byte extraction](../../elf.py) · [Certificate](coq/Object.v)

The output directory retains every generated and handwritten Coq source,
the assembly and checker sources, the raw symbol bytes (`symbol.bin`),
the assumption-check output (`assumptions.txt`) and `coqchk.log`.
`manifest.json` identifies the public theorem, ELF and symbol hashes,
tool versions and successful proof checks, and hashes each retained source
and evidence file. If `--cases` is supplied, the directory also retains
an exact copy as `conformance.jsonl`, with its export seed and case count
recorded in the manifest. [Evidence writer](../../evidence.py)

The retained `_CoqProject` lists all sources needed to rebuild the proof
without the repository or assembler. In `pow2-audit`, run:

```bash
set -e
coq_makefile -f _CoqProject -o Makefile
make -B
make validate
```

Compiling `Object.v` must print `Closed under the global context` for
`assembled_symbol_correct`. The saved manifest and logs record the original
check; rebuilding allows the auditor to repeat it.

To inspect the instructions, open `pow2-audit/Pow2/Program.v` next to
`pow2-audit/pow2.expanded.S`. Both listings use symbol-relative offsets.
The assembly listing includes the instruction bytes, and each mnemonic in
`Program.v` is Coq notation for a typed instruction. To compare with the
linked bytes, disassemble the same ELF.
[Intel notation](../../machine/isa/IntelSyntax.v)

```bash
objdump -d -M intel --disassemble=ed25519_simd_pow2_ifma "$elf"
```

To inspect the theorem binding, start `coqtop -quiet $(sed -n '/^-Q /p' _CoqProject)` in
`pow2-audit` and enter

```coq
From Ed25519Simd.Pow2 Require Object Audit ObjectBytes.
Check Object.assembled_symbol_correct : Audit.pow2_contract ObjectBytes.symbol_bytes.
```

To generate the two readable listings without a release ELF, run

```bash
python3 -B verification/crate/pow2/generate_listing.py ./pow2-listing
```

CI also runs an independent Z3 check of the linked disassembly.
[Z3 checker](check.py) · [CI workflow](../../../.github/workflows/ci.yml)

## Check native instruction coverage

Add `--cases` to the release proof command to export one test per square and
multiply instruction, including its symbol-relative offset, actual linked
bytes, symbol SHA-256, export seed and complete initial state. Run the exported
corpus with the shared vector conformance runner. The export also checks that every
scalar and control-flow instruction form in the linked program occurs in
the machine probes. The first runner invocation below executes those probes
and the fixed corpus. The second executes each exact linked kernel row.
Both require an AVX-512F/DQ/IFMA host and an XED kit. [Coverage check](coq/ExportCases.v) · [Backend setup](../../machine/README.md#run-the-conformance-suite) · [Case format and replay](../../machine/README.md#case-format-and-replay)

```bash
python3 -B verification/crate/pow2/coq_proof.py "$elf" --output pow2-coverage-audit --cases pow2-rows.jsonl --seed 42
python3 -B verification/machine/tests/run.py --backend all --report fixed-report.json
python3 -B verification/machine/tests/run.py --cases pow2-rows.jsonl --backend all --report pow2-report.json
python3 -B verification/machine/tests/run.py --replay pow2-report.json --report replay-report.json
```

CI retains both conformance reports, the exported corpus and the release
audit directory as one artifact. The reports embed their complete test inputs;
the release manifest binds the exported corpus to the exact proof sources and
linked symbol used by the check.
