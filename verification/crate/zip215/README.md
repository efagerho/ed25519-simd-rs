# Post-hash ZIP-215 verification

Audit `assembled_zip215_correct` against `zip215_contract`. A lane accepts
an encoding of R exactly when there is a signed Edwards point represented
by those bytes and **`[8](Q − R) = 0`**, where **Q = [s]B − [digest mod L]A**.
The y-coordinate is reduced modulo p. The decoder’s signed-root convention
admits either sign for zero. The scatter additionally requires the lane’s
input-valid bit and only writes active indices. Later active writes take
precedence when callers supply repeated indices.
See [Audit.v](coq/Audit.v) and [Equation.v](coq/Equation.v). The shared [candidate proof](../post_hash/Product.v) connects the digest and signed S digits to Q.

## What to audit

* Check the release ELF and the six symbol extents in the manifest.
  All five external calls use certificates for the same ELF. The Coq
  encoder resolves external call targets, private helper and constant
  addresses, internal branches and their signed displacement limits.
  See [Binding.v](coq/Binding.v) and [Caller.v](coq/Caller.v).
* Check the SysV and Rust boundary. Inputs supply SHA-512 digest rows,
  lane-major signed S digits, a valid affine base table and eight valid
  key tables. Input, stack, queue and output allocations have the
  alignment, sizes and disjointness their respective callee contracts
  require. The mutable queue begins empty and the incoming count at push
  is below eight. The ABI proof follows register moves, stack offsets,
  caller-saved clobbers, six SIMD transfers, the occupied count and the
  tail-call arguments. See [Staging.v](../post_hash/Staging.v) and
  [the Rust layout assertions](../../../src/wide/avx512ifma/post_hash_asm.rs).
* Check the grouped semantics of the remaining scalar and SIMD glue.
  Compare each named block’s effects, argument offsets, flags, stack
  scratch and register preservation to its instruction expansion. The
  decoder and cofactor checker supply the single and paired fallback
  masks. The projective-y probe can return any result because it only
  selects a schedule. Reusing a whole byte requires eight exact-match
  bits. Coq checks each queue occupancy and pattern of full bytes and
  proves the resulting output for arbitrary lane masks, initial output
  and in-range indices. See [Calls.v](coq/Calls.v) and
  [Schedule.v](coq/Schedule.v).
* For the predecoded entry check that the incoming decoder-valid bit
  describes the original R bytes, including the invalid case. The theorem
  takes this as an input contract. The Rust driver passes the R point and
  validity mask from the paired assembly decoder. Both entries take the eligibility flags,
  indices and active count from the caller. Hashing, key preparation and
  cache policy remain caller responsibilities.

This is a functional proof in the crate’s grouped-instruction model. The
mapping from grouped operations to native register and memory effects is
part of the audit surface. Physical stack isolation, FFI pointer validity
and the absence of hardware faults are execution assumptions. The shared
machine and memory semantics are described in the
[verification audit guide](../../README.md).

## Replay

Build the release `hot_profile_zip215` executable with the `asm` feature.
Run the following commands with its path in `elf`. The audit builds missing
callee proofs. Pass `--dependencies DIR` to reuse the five audit directories
from the same executable. The final check requires a closed theorem and
runs `coqchk` on its complete dependency graph.

```sh
python3 -B verification/crate/zip215/audit.py "$elf" --output /tmp/zip215-audit
python3 -B verification/crate/zip215/mutations.py "$elf" --audit /tmp/zip215-audit
```
