# Cached point addition

Start with the complete public theorem:

```coq
Object.assembled_cached_add_correct : Audit.cached_add_contract ObjectBytes.symbol_bytes
```

[`Audit.v`](coq/Audit.v) states the claim for `ed25519_simd_add_cached_ifma`.
[`Object.v`](coq/Object.v) proves it without axioms and binds the modeled
instructions to independently extracted linked symbol bytes. The arithmetic
specification in [`CachedAddSpec.v`](coq/CachedAddSpec.v) is independent of the
instruction listing and proof checker.

## Contract

RDI points to an initialized, exclusive 1,280-byte point containing X, Y, Z, T
at offsets 0, 320, 640, 960. RSI points to read-only staged fields
`Y2-X2`, `Y2+X2`, `2*d*T2`, and optionally `2*Z2`. Both buffers are aligned to
64 bytes and disjoint from each other, code, and the private stack area.
Each field contains five vectors of eight unsigned qwords, weighted by
`2^(51*i)` within each lane. Every input limb must be below `2^52` for the
arithmetic guarantee. Curve membership and consistency of cached coordinates
are not assumed.

RDX (`compute_t`) and RCX (`affine`) must each be exactly zero or one. All four
combinations are proved. Projective mode reads 1,280 cached bytes; affine mode
reads only 960 bytes and substitutes `D=2*Z1`.

In each of the eight lanes, modulo `p=2^255-19`:

```text
A = (Y1-X1)*(Y2-X2)    B = (Y1+X1)*(Y2+X2)
C = T1*(2*d*T2)        D = Z1*(2*Z2), or 2*Z1 in affine mode
E = B-A   F = D-C   G = D+C   H = B+A
X' = E*F  Y' = G*H  Z' = F*G  T' = E*H, or literal zero if compute_t=0
```

Every output coordinate has limbs 0, 2, 3, 4 below `2^51` and limb 1 below
`2^52`. Omitting T writes five exactly zero vectors, even for inputs outside
the arithmetic bounds.

The same theorem proves finite execution, normal return, restored RSP and
SysV saved registers, initialization of every output byte, and preservation
of the cache. Writes stay inside the point and private stack. The aligned
scratch area, saved RBP, padding, and two nested return addresses use at most
1,352 bytes below entry RSP.

One concrete byte memory covers vectors and saved stack qwords. Every read
agrees with byte decoding at every trace prefix. Pops read the expected
qwords; caller return bytes and all bytes outside writable regions are
preserved. The proof constructs the logical entry from actual pointers,
flag qwords and bytes, and proves that its alignment equals `AND RSP,-64`.
Memory/ABI guarantees do not depend on the field arithmetic bounds.
[`ABI`](coq/CachedAddABI.v) · [`Memory`](coq/CachedAddMemory.v) · [`Concrete bytes`](coq/CachedAddBytes.v)

## Check the release executable

With Python 3.8+, LLVM MC, GNU binutils and Coq (`coqdep`, `coqc`, `coqchk`)
on PATH, run from the repository root:

```sh
python3 -B verification/cached_add/audit.py /path/to/unstripped-release-elf \
  --output ./cached-add-audit --cases ./cached-add-cases.jsonl --seed 42
```

The audit checks the complete theorem, requires `Closed under the global
context`, and runs `coqchk`. It retains proof sources, the expanded assembly,
the Coq instruction listing, raw symbol bytes, tool versions and hashes.
Both listings contain instruction offsets; `add_cached.expanded.S` also
shows bytes. The manifest identifies the ELF and symbol being certified.

Rebuild the retained certificate without the repository or assembler:

```sh
cd cached-add-audit
set -e
for proof_source in $(coqdep -sort -f _CoqProject); do
  coqc -Q machine Machine -Q arithmetic ProofArithmetic "$proof_source"
done
coqchk -Q machine Machine -Q arithmetic ProofArithmetic -silent Object
```

For a build that embeds only certified bytes:

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --release --features verify-asm-pow2,verify-asm-double4,verify-asm-cached-add
```

`asm-cached-add` selects the same assembly without running Coq during the
build. Release auditing checks the final linked artifact from either build.

## Proof structure and trust boundary

| Files | Responsibility |
| --- | --- |
| `Kernels.v`, `KernelInterface.v` | Prove the six arithmetic blocks against their actual instructions, including different cached RHS operands, loose multiplication outputs, and biased subtraction/reduction. |
| `Bounds.v`, `KernelCalls.v`, `Calls.v` | Prove interval propagation through the complete path and check each call's preconditions. The interval bounds used to justify IFMA operands are proved, never assumed. |
| `Control.v`, `Routing.v`, `Arithmetic.v`, `Logical.v` | Compute and prove all four public control paths, check actual register/memory routing, compose the formulas, and lift them to all eight lanes. |
| `FrameProof.v`, `CachedAddBytes.v`, `ReadFootprint.v` | Prove the shared byte-memory contract, stack and register restoration, complete output writes, cache preservation and affine read extent. |
| `EntryTests.v` | Concrete witnesses with valid arithmetic inputs for every flag/alignment combination, rejection of wrong return bytes, and output initialization outside the arithmetic bounds. |
| `Audit.v`, `Object.v` | State and prove the single complete byte-bound certificate. |

The polynomial checker and signed symbolic interpreter are shared with pow2
and double4. Cached addition adds IFMA memory operands to the machine model;
they reuse the existing IFMA arithmetic and common EVEX memory encoder.
Read tracking, instruction/block equivalence, dependency tracking, word
bounds and byte-memory proofs include those operands.

The case export covers every vector instruction occurrence and checks that
native probes cover each scalar/control form. Fixed memory-IFMA cases test
all eight lanes, operand aliasing, 52-bit masking, accumulator wraparound,
high registers and displacement/SIB encoding. The aligned stack probe also
observes the new register copies and zero-displacement LEA.

```sh
python3 -B verification/machine/tests/run.py --backend all \
  --xed-kit /path/to/xed-kit --cases ./cached-add-cases.jsonl \
  --report ./cached-add-report.json
```

Tests compare Coq's encodings and execution with Intel XED and native hardware.
An independent ISA refinement theorem remains open. Coq's kernel, the stated
machine semantics and the auditor's identification/extraction of the linked
bytes remain the trust boundary. Listing generation, interval checking and
polynomial normalization produce claims rechecked by the kernel.
[`Machine model`](../machine/README.md) · [`ISA obligation`](../machine/proofs/README.md)

This certificate proves coordinate arithmetic in the model. It does not
prove the group law, the Rust staging/dispatch code, physical constant-time
behavior, or the complete Ed25519 verifier.

## Mutation checks

```sh
python3 -B verification/cached_add/mutations.py \
  --output ./cached-add-mutations --native
```

The script copies sources into isolated directories, removes a reduction,
uses the wrong cached operand, removes the top carry fold, ignores the T
flag, and omits output stores. Each must fail a semantic proof prerequisite
of the public theorem while still passing separate Coq checks of byte binding
and program layout. A harmless reordering of constant loads must pass the full
theorem and `coqchk`. `--native` additionally checks independent integer
fixtures, retaining a counterexample for every faulty variant. Omit it on
hosts without AVX-512F/DQ/IFMA.

A rejected prerequisite prevents issuance of the public certificate; it is
not a report that Coq reached and rejected the final line of `Object.v`.
