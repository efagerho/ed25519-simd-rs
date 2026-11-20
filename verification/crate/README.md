# Assembly proofs

Each routine has one public theorem binding its result to the bytes of its
linked symbol. Start with the routine’s
README for its contract and release audit.

| Routine | What the theorem covers |
| --- | --- |
| [pow2/](pow2/README.md) | Paired field exponentiation. |
| [double4/](double4/README.md) | Four in-place point doublings. |
| [cached_add/](cached_add/README.md) | Cached point addition with affine or projective inputs and optional T output. |
| [scalar/](scalar/README.md) | Canonical reduction of eight 512-bit inputs modulo the scalar order. |
| [radix16/](radix16/README.md) | The linked reducer and digest wrapper produce 64 signed digits representing each input modulo the scalar order. |
| [stage_round/](stage_round/README.md) | Signed key lookup, base-digit folding and exact limb placement in the 55-row ladder input. |
| [ladder_step/](ladder_step/README.md) | A radix-256 ladder step composed from the verified doubling and cached-addition routines. |
| [torsion/](torsion/README.md) | The returned lane mask equals the full ZIP-215 cofactor check, including the all-lanes early return. |
| [small_order/](small_order/README.md) | The returned mask selects precisely the valid projective points killed by the cofactor, including the all-lanes rejection path. |

## What to audit

Use the [shared audit surface](../README.md#shared-audit-surface) for the
machine, memory, and mathematical assumptions. For each release, follow the
routine’s inputs from the Rust call site to the public theorem and its outputs
back to the caller. The certificates begin at the assembly ABI. Rust dispatch,
caller-side input preparation, and end-to-end Ed25519 acceptance require
separate review.

1. **Identify the code.** Use the exact release ELF. Independently compare its
   digest, symbol name, address, size, and bytes with the audit manifest and
   retained symbol file. The extractor cross-checks the file offset from
   `.text` against the executable load segment. For the ladder, check the
   wrapper and both callees in the same ELF and the relative call targets.
   For radix16, check the wrapper and its scalar reducer together.
   [ELF extraction](../elf.py) · [Manifest contents](../evidence.py)
2. **Read the public statement.** Start in the routine’s `coq/Audit.v`. For a
   standalone routine with an output buffer follow `run_concrete` to its byte-level contract. Check
   the byte binding, layout check, input predicates, and the access, byte-memory,
   and arithmetic predicates supplied to `SysV.call_result`. They describe
   the same returning execution. For the ladder, read `run_ladder` and the
   fields of `ladder_result`, including `edwards_sum`. For torsion, read
   `run_correct` and `lane_result` for the mask, point premises and group
   equation. For small order, check the two byte bindings and the group result
   for valid XYZ points. Both mask routines use a tagged private stack.
   For staging, check the signed entry index, source extents and every output row in `stage_contract`.
   [Common call result](../machine/abi/SysV.v) · [Ladder contract](ladder_step/coq/Audit.v)
3. **Match the caller.** Compare register arguments, Rust layout, buffer
   lengths, aliasing, stack space, and numeric or point-representation premises
   with the actual call site. Read the entry witnesses to see concrete states
   admitted by the contract. Check that each property Rust consumes holds
   under the premises it supplies. For example, `MaybeUninit::assume_init`
   requires every output byte to be written even when the arithmetic result
   is conditional on input bounds. Each routine guide links its caller and
   the relevant predicates.
4. **Recheck the certificate.** Run the routine’s linked audit, or rebuild
   its retained sources for replay. Inspect the generated `Checked.v` for the
   fully qualified theorem and expected type, including the extracted byte
   constant for a standalone symbol. Require `Closed under the global context`
   from `Print Assumptions checked` and a successful `coqchk` on the
   `Checked` module. This checks the proof and its dependencies. A human
   can rely on that replay for the intermediate proofs and check whether the
   public type and its definitions express the desired claim. [Theorem selection and checks](../proof_build.py)

### Shared crate definitions

| Module | What to check |
| --- | --- |
| [Wide51.v](Wide51.v) | `cell` selects qword `8*i + lane`. Trace `field_at`, `point_values`, and `cache_values` to the Rust field order. Check which coordinates each bound covers. |
| [PointFrame.v](PointFrame.v) | For double4 and cached addition, check the 1,280-byte scratch area, alignment padding, saved RBP, caller and nested return slots, and the writable byte interval. An overly broad interval weakens caller-memory preservation. |
| [FieldSymbolic.v](FieldSymbolic.v), [FieldKernel.v](FieldKernel.v) | The shared checker for double4 and cached addition takes the decoded instructions, input intervals, output bounds, and target field expressions. Its soundness theorem requires the mask register, loads, initial values, and refinement hints to satisfy their specifications. Coq checks those obligations at each use. |
| [field51/](field51/README.md) | The shared radix-51 circuit checker proves field congruence, limb bounds and positive representatives at the supplied cuts. Both mask routines use its [zero and mask lemmas](field51/RootMasks.v). |

## Build and audit

On x86-64 Linux, the `asm` feature enables all assembly backends. Each
`verify-asm-*` feature also checks the named standalone routine during the
build and embeds the bytes that passed. Staging, radix16, ladder, torsion and
small-order audits check the linked symbols in the release ELF.

Run the build commands from the repository root.

```sh
export RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512dq,+avx512ifma"
cargo build --release --features asm
cargo build --release --features verify-asm-pow2,verify-asm-double4,verify-asm-cached-add,verify-asm-scalar
```

The proof and audit tools require Python 3.8 or later, LLVM MC (`llvm-mc`
or `LLVM_MC`), GNU binutils (`nm`, `objcopy`, `objdump`), and Coq with its
standard library (`coqdep`, `coqc`, `coqchk`). The ladder and torsion group proofs and
the full shared-library build additionally require Coqprime
(`libcoq-coqprime` on Ubuntu).

Each audit checks the public theorem against its expected contract in
`Checked.v`, checks that its assumptions are closed, and runs `coqchk`.
The retained audit includes the sources and `_CoqProject` for replay. Its
manifest records the checked declaration and each linked symbol’s address,
size, and digest.

## Reuse a shared Coq build

CI builds the shared libraries once per job with `coq_makefile` and GNU Make.
To reuse them locally across build-time proofs, audits, mutation tests, and
machine conformance runs, choose a fresh output directory.

```sh
python3 -B verification/proof_build.py "$PWD/target/shared-coq" --jobs 4
export ED25519_SIMD_COQ_LIBRARIES="$PWD/target/shared-coq"
```

Each consumer checks the Coq version and the digests of project files, sources,
and compiled objects. With the variable unset, it builds its shared dependencies
from source.

Run `python3 -B verification/test_evidence.py` to check report replay, seed
provenance, and audit manifest integrity. With Coq on PATH, it also checks
that a weakened public theorem fails the expected-type check.
