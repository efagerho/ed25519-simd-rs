# ZIP-215 torsion check

The public theorem `assembled_torsion_correct` binds the complete linked
`ed25519_simd_check_8_torsion_ifma` symbol to an eight-bit return value.
For every bounded input, bit `j` is set exactly when the **full** four-root
test accepts lane `j`. For valid extended points with affine `R`, the same
bit is set exactly when **`[8](P[j] − R[j]) = identity`**. This includes the
early return and batches in which only some lanes pass. [Public contract and lane result](coq/Audit.v) · [Theorem](coq/Object.v)

## What to audit

1. Match the two read-only `WidePoint` arguments to SysV RDI and RSI.
   Each holds X, Y, Z, T in order, with five radix-51 limb vectors per
   coordinate. Qword `8*i+j` holds limb row `i` in lane `j`. Every P limb
   and every R limb in X, Y and T must be unsigned and below `2^52`.
   The arithmetic result permits arbitrary stored R.Z. The group result
   requires R.Z congruent to one and both T coordinates consistent with
   their points. The arguments can refer to the same point. Check that
   the ZIP-215 caller reads EAX bit zero as lane zero. [Assembly caller](../../../src/wide/avx512ifma/zip215.S) · [Representation](../Wide51.v) · [Edwards representation](../../curve25519/group/Representation.v)
2. Read `torsion_check` and `torsion_check_correct`. With mixed-subtraction
   numerators X and Y, the full check tests zero modulo the field prime for
   `iY`, `X`, `iY+X`, and `iY−X`, where `i² = −1`. The shortcut compares
   `X_P Y_R − Y_P X_R` to zero in every lane. If all eight comparisons pass,
   the full test's X numerator vanishes in every lane. Any other comparison
   mask runs the full check for all eight lanes. [Equations](../../curve25519/Torsion.v) · [Group proof](../../curve25519/group/Cofactor.v)
3. Follow `run_correct` into the mask-dependent machine. It starts at byte
   zero of the linked symbol, permits 20 readable vector rows per argument,
   and checks all four incoming SysV alignments with 1,032 bytes of private
   stack. Both paths return through the incoming caller slot after restoring
   RBP. Reads of RIP-relative constants come from the certified image.
   The functional theorem uses read-only input qwords and a tagged stack.
   The native return theorem reads both operands from the caller’s byte memory.
   It derives the return PC, EAX, and final memory from the selected path and
   proves that every store prefix preserves both inputs and the linked symbol.
   [Native return](coq/Native.v) The model and its
   remaining refinement obligations are documented centrally. [Shared trust boundary](../../README.md#shared-audit-surface) · [Machine](../../machine/execution/MaskTrace.v)
4. Check the ELF identity, symbol extent and retained bytes. Coq checks
   every instruction encoding and every literal byte, including alignment
   padding. As a separate source check, the audit reassembles the source
   and allows LLVM's NOP choices only at its explicit alignment directives.
   [Audit driver](audit.py) · [Symbol listing](listing.py)

## Replay

With the shared verification tools and Coqprime installed, run from the
repository root against a release ELF built with all assembly enabled.

```sh
python3 -B verification/crate/torsion/audit.py "$RELEASE_ELF" --output ./torsion-audit
python3 -B verification/crate/torsion/mutations.py "$RELEASE_ELF" --audit ./torsion-audit
```

The audit checks the independently stated type, requires `Closed under the
global context`, runs `coqchk`, and retains the sources and symbol digest.
The mutations change the all-lanes guard, determinant subtraction, last mask
union, and stack allocation. Each mutated listing must match its own ELF
bytes and then fail a specified prerequisite of the public theorem. [Release evidence](../README.md#what-to-audit)

## Proof structure

| Files | What Coq checks |
| --- | --- |
| [Schedule.v](coq/Schedule.v) | Both paths through the instructions and nested calls, plus twelve field values and their limb bounds. |
| [Arithmetic.v](../field51/Arithmetic.v), [Check.v](../field51/Check.v) | The field identities at each checkpoint follow from the word operations, including wrapping subtraction, unsigned carries, and IFMA's 52-bit operands. |
| [Radix51Zero.v](../../curve25519/Radix51Zero.v), [Masks.v](coq/Masks.v) | For the positive loose representatives produced here, the limbwise bit test detects exactly zero modulo the field prime. The actual comparisons and mask unions use those results. |
| [Lane.v](coq/Lane.v), [Object.v](coq/Object.v) | The determinant and full-check paths give the specified decision in each lane, including when a different lane controls the branch. |
