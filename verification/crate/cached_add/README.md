# Cached point addition

Given bounded input limbs in all eight lanes, `ed25519_simd_add_cached_ifma`
writes the cached-addition formulas in place for each lane. If the input represents P with a
valid T and the staged cache represents Q, `add_represents` gives the group
result **P + Q**. Both output modes give XYZ. Full mode also gives T, and
omitted-T mode writes five zero vectors. [Arithmetic contract](coq/CachedAddSpec.v) · [Group interpretation](../../curve25519/group/Representation.v)

Public theorem in `Ed25519Simd.CachedAdd`. [Statement](coq/Audit.v) · [Proof](coq/Object.v)

```coq
Object.assembled_cached_add_correct : Audit.cached_add_contract ObjectBytes.symbol_bytes
```

## What to audit

1. Compare the staged operand layout with `cache_values` and `concrete_entry`.
   RDI points to the in-place accumulator, RSI to a separate read-only cache,
   RDX selects T, and RCX selects affine mode. Both flags must be zero or one.
   Check the field order `Y−X, Y+X, 2dT`, with `2Z` present only in the
   projective cache. The assembly ladder selects and transposes the table entries
   before the verified call. [Staging theorem](../stage_round/README.md) · [Full ladder caller](../../../src/wide/avx512ifma/mul_s_base_minus_k_public.S) · [Ladder step](../../../src/wide/avx512ifma/ladder_step.S) · [Cache decoding](../Wide51.v) · [Byte contract](coq/CachedAddBytes.v)
2. Read `cached_add_spec` for all four flag combinations. The field result
   requires bounded point and cache limbs. The literal-zero T guarantee sits
   outside that implication. For the group interpretation, check that
   `represents_cache` uses a common nonzero scale and fixes it to one for
   affine input. [Field specification](coq/CachedAddSpec.v) · [Representation predicates](../../curve25519/group/Representation.v)
3. Check that `cache_contract` preserves the cache and limits each cache
   read to the selected extent, 960 or 1,280 bytes. Writes must fit in the
   point or private stack, including the two nested return slots. Check
   the concrete entries for both flags and each permitted stack alignment.
   [Memory contract](coq/CachedAddMemory.v) · [Shared point frame](../PointFrame.v) · [Entry witnesses](coq/EntryTests.v)

Apply the [crate audit procedure](../README.md#what-to-audit) to this symbol.

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

The independent products A and B, and projective C and D, return folded
columns below `300·2^52`. The proof checks the biased differences and sums
at that bound, then checks that carrying E, F, G and H makes them valid
52-bit multiplication inputs. [Kernel bounds](coq/Kernels.v) · [Call preconditions](coq/KernelCalls.v)

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
python3 -B verification/crate/cached_add/audit.py /path/to/unstripped-release-elf \
  --output ./cached-add-audit --cases ./cached-add-cases.jsonl --seed 42
```

The audit checks the complete theorem, requires `Closed under the global
context`, and runs `coqchk`. It retains proof sources, the expanded assembly,
the Coq instruction listing, raw symbol bytes, tool versions and hashes.
Both listings expand the field multiplication macro shared with double4 and
give instruction offsets. `add_cached.expanded.S` also shows the bytes. The
manifest identifies the ELF and symbol being certified. [Shared multiplication kernel](../../../src/wide/avx512ifma/fe51_product.inc)

Rebuild the retained certificate without the repository or assembler:

```sh
cd cached-add-audit
set -e
coq_makefile -f _CoqProject -o Makefile
make -B
make validate
```

To embed certified bytes for pow2, double4, and cached addition:

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --release --features verify-asm-pow2,verify-asm-double4,verify-asm-cached-add
```

The default build assembles the routine directly. The proof features certify
the named routines at build time. Release auditing checks the final linked
artifact from either build.

## Proof structure

| Files | Responsibility |
| --- | --- |
| `Kernels.v`, `KernelInterface.v` | Prove the six arithmetic blocks against their actual instructions, including different cached RHS operands, loose multiplication outputs, and biased subtraction/reduction. |
| `Bounds.v`, `KernelCalls.v`, `Calls.v` | Prove interval propagation through the complete path and check each call's preconditions. The interval bounds used to justify IFMA operands are proved, never assumed. |
| `Control.v`, `Routing.v`, `Arithmetic.v`, `Logical.v` | Compute and prove all four public control paths, check actual register/memory routing, compose the formulas, and lift them to all eight lanes. |
| `FrameProof.v`, `CachedAddBytes.v`, `ReadFootprint.v` | Prove the shared byte-memory contract, stack and register restoration, complete output writes, cache preservation and affine read extent. |
| `EntryTests.v` | Concrete witnesses with valid arithmetic inputs for every flag/alignment combination, rejection of wrong return bytes, and output initialization outside the arithmetic bounds. |
| `Audit.v`, `Object.v` | State and prove the single complete byte-bound certificate. |

Cached addition and double4 share the signed symbolic interpreter and
field-kernel checker. Cached addition adds IFMA memory operands to the machine model;
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

The [shared audit surface](../../README.md#shared-audit-surface) explains how
to interpret the XED and hardware comparisons.

## Mutation checks

```sh
python3 -B verification/crate/cached_add/mutations.py \
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
