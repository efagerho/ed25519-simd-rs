# Scalar reduction certificate

The public theorem is
[`Object.assembled_scalar_correct`](coq/Object.v), with the complete statement
in [`Audit.scalar_contract`](coq/Audit.v). It binds every modeled instruction
to the linked bytes of `ed25519_simd_scalar_reduce_ifma` and proves canonical
reduction of all eight independent 512-bit inputs modulo
`L = 2^252 + 27742317777372353535851937790883648493`.

Start an audit with [`ScalarSpec.v`](coq/ScalarSpec.v), then the public contract,
[`ScalarABI.v`](coq/ScalarABI.v), and the concrete entry and byte-result
conditions in [`ScalarBytes.v`](coq/ScalarBytes.v). The specification is
independent of the assembly listing and the proof checker. Its result is
`H mod L`, not merely a congruent or Montgomery-scaled value.

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
python3 -B verification/scalar/audit.py /path/to/unstripped-release-elf \
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
for proof_source in $(coqdep -sort -f _CoqProject); do
  coqc -Q machine Machine "$proof_source"
done
coqchk -Q machine Machine -silent Object
```

To embed only certified bytes during the build:

```sh
export RUSTFLAGS='-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma'
cargo build --release --features asm-pow2,verify-asm-scalar
```

`asm-scalar` selects the same assembly without running Coq during the build.
Release auditing checks the final linked artifact from either build.

## Proof structure

| Files | Checked responsibility |
| --- | --- |
| `Unpack.v`, `Product.v` | Exact 64-to-52-bit unpacking and both constant products; actual IFMA operand and accumulator bounds. |
| `ScalarMath.v`, `Reduction.v`, `Montgomery.v` | Cancellation of each low column, the optimized ceiling carry including zero low limbs, all five Montgomery steps, normalization, and the bound that makes one subtraction sufficient. |
| `Borrow.v`, `Finish.v` | Borrow propagation through five limbs, wrapped subtraction, and bitwise selection of the canonical result. |
| `Symbolic.v`, `Calculate.v` | Sound interval/exact-polynomial checking and composition into `H mod L`. |
| `Control.v`, `Lane.v`, `Routing.v`, `Logical.v` | Actual control path, broadcasts, register and memory routing, stores, and all eight lanes. |
| `ScalarMemory.v`, `FrameProof.v`, `ScalarBytes.v` | ABI, complete writes, concrete byte memory, read consistency, and preservation outside output. |
| `Audit.v`, `Object.v`, `EntryTests.v` | Complete public certificate, byte binding, and concrete non-vacuity witnesses. |

The arithmetic checker reuses the existing polynomial normalizer and
interval interpreter, but proves exact integer identities independently of
the field modulus used by the point routines. All range facts used to
justify IFMA and carry operations are proved from arbitrary input qwords.
The large constants and the Bezout witness for Montgomery cancellation
are checked by Coq as integer identities.

## Machine model and trust boundary

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

These tests compare Coq encodings and execution with Intel XED and hardware.
An independent ISA refinement theorem remains open. Coq's kernel, the stated
machine semantics, and identification/extraction of the linked bytes remain
the trust boundary. Python generation and the executable proof checkers do
not add axioms: their results are checked by the kernel.

The certificate covers this assembly routine in the model. It does not prove
Rust dispatch or recoding, SHA-512, physical constant-time behavior, or the
complete Ed25519 verifier. [Machine model](../machine/README.md) ·
[ISA refinement obligation](../machine/proofs/README.md)

## Fault injection

```sh
python3 -B verification/scalar/mutations.py \
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
