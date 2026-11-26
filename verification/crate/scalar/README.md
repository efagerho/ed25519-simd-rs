# Scalar reduction certificate

For each of eight unsigned 512-bit inputs H, `ed25519_simd_scalar_reduce_ifma`
writes the canonical integer **`H mod L`** in five base-`2^52` limbs, where
`L = 2^252 + 27742317777372353535851937790883648493`. All 512 input bits
are covered.

Public theorem in `Ed25519Simd.Scalar`. [Statement](coq/Audit.v) · [Proof](coq/Object.v)

```coq
Object.assembled_scalar_correct : Audit.scalar_contract ObjectBytes.symbol_bytes
```

## What to audit

1. Compare `lane_input` and `lane_output` with Rust’s word-major buffers.
   Index `8*i+j` selects word or limb `i` of lane `j`. Check the input
   weight `2^(64*i)`, output weight `2^(52*i)`, scalar order, and exact
   equality to `H mod L`. This equality rules out a Montgomery-scaled result
   or a noncanonical representative. [Scalar specification](coq/ScalarSpec.v) · [Scalar order](../../curve25519/Scalar.v)
2. Compare `concrete_entry` with the call in `ed25519_simd_digest_to_radix16`.
   RDI designates the first 320 bytes of the digit output and RSI designates
   a disjoint 512-byte digest input. Check that `output_initialized` covers
   all five limb rows the caller reads. The eight-byte return slot is the
   only stack storage the reducer needs. [Assembly caller](../../../src/scalar/radix16.S) · [Concrete contract](coq/ScalarBytes.v) · [Memory permissions](coq/ScalarMemory.v)
3. Check that the allowed placements include unaligned buffers and that
   the input premise admits the maximal 512-bit integer. The entry tests
   exercise all 64 buffer alignments and derive the maximal-input result
   from the public contract. [Entry witnesses](coq/EntryTests.v)

Apply the [crate audit procedure](../README.md#what-to-audit) to this symbol.
The digest wrapper consumes this result to prove signed-digit recoding and
final lane placement for the linked caller. [Wrapper certificate](../radix16/README.md)

## Contract

RDI points to a writable 320-byte output and RSI to a read-only 512-byte
input. They are disjoint from each other, the caller's eight-byte return
slot, and the code. Input and output need no vector alignment. The stack
pointer follows SysV alignment. Input row `i` contains word `i` of eight
little-endian 512-bit integers; output row `i` contains radix-2^52 limb `i`
of their canonical residues. Every output limb is below `2^52`.

The theorem has no input-limb restrictions beyond being unsigned qwords.
It proves termination, normal return, RSP restoration, preservation of SysV
callee-saved registers, and initialization of every output byte. Writes
stay inside the output; input, code, return bytes, and all other bytes are
preserved. The routine uses no stack scratch or calls.

Concrete pointers and byte memory induce the logical entry state. Every
mapped vector read agrees with byte decoding at every trace prefix; RET
reads the caller's actual return word. `EntryTests.v` supplies concrete
entries for all 64 buffer alignments, rejects a wrong return word, and
checks that the maximal 512-bit input is covered.

## Replay against a release executable

With Coq 8.20, Python, LLVM MC, and GNU binutils on PATH:

```sh
python3 -B verification/crate/scalar/audit.py /path/to/unstripped-release-elf \
  --output ./scalar-audit --cases ./scalar-cases.jsonl --seed 42
```

The audit requires `Closed under the global context` and runs `coqchk` on
the complete theorem. It retains the proof sources, expanded assembly with
instruction offsets and bytes, generated Coq listing, raw symbol bytes,
tool versions, hashes, and conformance cases. The manifest identifies the
exact executable and symbol being certified.

Replay the retained certificate without the repository or assembler:

```sh
cd scalar-audit
set -e
coq_makefile -f _CoqProject -o Makefile
make -B
make validate
```

To embed certified bytes for scalar reduction during the build:

```sh
export RUSTFLAGS='-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma'
cargo build --release --features verify-asm-scalar
```

The default build assembles the reducer directly. `verify-asm-scalar`
certifies scalar reduction at build time.
Release auditing checks the final linked artifact from either build.

## Proof structure

| Files | Checked responsibility |
| --- | --- |
| `Unpack.v`, `Product.v` | Exact 64-to-52-bit unpacking and both constant products; actual IFMA operand and accumulator bounds. |
| [Scalar specialization](../../curve25519/ScalarReduction.v), [general cancellation](../../arithmetic/Montgomery.v), `Reduction.v`, `Montgomery.v` | Cancellation of each low column, the optimized ceiling carry including zero low limbs, all five Montgomery steps, normalization, and the bound that makes one subtraction sufficient. |
| `Borrow.v`, `Finish.v` | Borrow propagation through five limbs, wrapped subtraction, and bitwise selection of the canonical result. |
| [Shared arithmetic](../../arithmetic/README.md), `Symbolic.v`, `Calculate.v` | Sound interval/exact-polynomial checking, scalar instruction conditions, and composition into `H mod L`. |
| `Control.v`, `Lane.v`, `Routing.v`, `Logical.v` | Actual control path, broadcasts, register and memory routing, stores, and all eight lanes. |
| `ScalarMemory.v`, `FrameProof.v`, `ScalarBytes.v` | ABI, complete writes, concrete byte memory, read consistency, and preservation outside output. |
| `Audit.v`, `Object.v`, `EntryTests.v` | Complete public certificate, byte binding, and concrete non-vacuity witnesses. |

The arithmetic checker reuses the existing polynomial normalizer and
interval interpreter, but proves exact integer identities independently of
the field modulus used by the point routines. All range facts used to
justify IFMA and carry operations are proved from arbitrary input qwords.
The large constants and the Bezout witness for Montgomery cancellation
are checked by Coq as integer identities.

## Instruction coverage

No new vector instruction semantics are needed. The scalar encoding addition
is `48 c7 c0 imm32` (`MOV rax, imm32`), restricted to nonnegative 31-bit
immediates, for which sign extension is the identity. Negative immediates and
values at or above `2^31` are rejected by `valid_program`. Native probes cover
zero, one, the reducer's constant, and `2^31-1`; domain tests check rejection
at both unsupported boundaries. All vector instruction occurrences are
exported, and export also checks native coverage of every scalar form.

```sh
python3 -B verification/machine/tests/run.py --backend all \
  --xed-kit /path/to/xed-kit --cases ./scalar-cases.jsonl \
  --report ./scalar-report.json
```

The [shared audit surface](../../README.md#shared-audit-surface) explains how
to interpret the XED and hardware comparisons.

## Fault injection

```sh
python3 -B verification/crate/scalar/mutations.py \
  --output ./scalar-mutations --native
```

Each mutation uses a private source tree. The campaign removes carry rounding
and a modulus product, corrupts the Montgomery inverse and unpack shift,
omits a canonical subtraction, and omits stores. Each must fail a semantic
prerequisite of the public theorem while still passing independent byte
binding and program-layout checks. Reordering independent register clears
must pass the entire certificate and `coqchk`. Native checks compare exact
canonical results with Python integer arithmetic and retain counterexamples.
A rejected prerequisite prevents issuance of the public certificate; it does
not imply that Coq reached the final theorem before rejecting the proof.
