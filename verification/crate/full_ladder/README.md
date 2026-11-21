# Full public double-scalar ladder

`Object.assembled_full_ladder_correct : Audit.full_ladder_contract` binds
`ed25519_simd_mul_s_base_minus_k_public` and its four reachable assembly
symbols in one ELF. In each lane the output represents **[s]B + [−k]A**
on Edwards25519. The theorem reads s and k as 64 little-endian signed
radix-16 digits from their actual ABI buffers. All four output coordinates
satisfy the reduced limb bounds. The extended mode supplies a valid T.
In XYZ mode all five T limbs are zero. The theorem proves existence of a
return in the model and covers every permitted return.

## What to audit

1. In `full_product`, check the eight lanes, the sign on k, the digit
   order, both T modes and the output bounds. `valid_tables` requires the
   signed key and affine tables to represent the specified multiples of
   each lane's A and of B. It constrains the contents of the Rust tables.
   The proof obtains their selected indices and words from the staging
   theorem. The caller supplies bounded digits, valid tables, readable
   inputs and disjoint writable memory. Read the placement conditions
   alongside the Rust call and the shared memory assumptions.
   [Public theorem](coq/Audit.v) · [Table and digit ABI](coq/Operands.v) ·
   [Rust caller](../../../src/wide/avx512ifma/ladder_step_asm.rs) ·
   [Central audit surface](../../README.md#shared-audit-surface)
2. Check the projection at call boundaries. `Program.walk` follows the
   linked relative targets and both conditional branches. It models the
   stack relative to entry RSP for each SysV alignment, checks the
   continuation, saved registers and return slot, and invalidates
   caller-saved values and private slots across calls. The stage and
   point buffers have separate identities. `Seed.step` executes qword
   instructions using RSP-relative staged rows and RBX-relative output
   rows. `Seed.valid` checks the addressing forms and bounds that permit
   that projection. [Caller model](coq/Program.v) · [Seed model](coq/Seed.v)
3. The execution model projects the wrapper onto its live buffers.
   Staging executes on the original read-only inputs. Each arithmetic
   call executes the linked callee with the accumulator and staged words
   from the preceding boundary, arbitrary well-formed temporaries, and the
   checked return address. The caller stack is tracked symbolically.
   There is no single flat-byte trace of the wrapper and all callees or
   guarantee about the final contents of private stack bytes.
   Check the concrete-to-buffer views, frame separation and the four
   imported callee bindings. [Native calls](coq/Native.v) ·
   [Buffer projection](coq/Composition.v) · [Staging](../stage_round/README.md) ·
   [Ladder step and its callees](../ladder_step/README.md)
4. The initial odd cache yields (2X, 2Y, 2Z). Check the carry into
   limb zero and the bound consumed by the first doubling. Each later
   pair updates the two signed scalar coefficients in radix 256.
   [Seed arithmetic](coq/Seed.v) · [Signed scalar action](coq/ScalarAction.v) ·
   [Round induction](coq/Execution.v)

## Replay

Build a release ELF with the `asm` feature and the AVX-512 target flags
in the [crate guide](../README.md#build-and-audit). From the repository
root, run the following command with that ELF.

```sh
python3 -B verification/crate/full_ladder/audit.py "$elf" --output ./full-ladder-audit
```

Compare the five linked symbol addresses and byte digests in
`manifest.json` with the release. The job checks the theorem's expected
type, closed assumptions and transitive dependencies with `coqchk`.
Negative controls change the pair index, T flag stack slot, frame size
and seed carry fold.
