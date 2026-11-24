# Production batch verification

Start with `assembled_zip215_verify_batch_correct` or
`assembled_dalek_verify_batch_correct`. Each instantiates the same
`batch_contract` at the address and exact linked bytes of the assembly symbol
called by Rust. The statement quantifies over the original descriptors, the
initial contents of the output array and any batch length, including zero.
[Theorems](coq/Object.v) · [Contract, execution and caller premises](coq/Audit.v) ·
[Rust entry points](../../../src/verifier/driver.rs)

For an admissible call the grouped execution returns. Every such return has
status 1, resumes at the caller's return address with RSP advanced by eight,
restores the SysV callee-saved integer registers and leaves byte-valued memory.
Each output byte is 0 or 1. The byte at a descriptor's original output index
is 1 exactly when its signature verifies under the selected policy. Full
chunks, partial chunks, preparation rejecting a whole chunk and ineligible
lanes mixed with eligible lanes are covered. [Loop](coq/Loop.v) · [Output placement](coq/Scatter.v) · [Return](coq/Return.v)

## Acceptance on the input bytes

Both policies require the little-endian signature scalar `S < L`. Decode the
public key to `A`, compute `k = LE(SHA512(R_bytes || A_bytes || message)) mod L`
and let `Q = [S]B − [k]A`. The two 32-byte strings in the hash are exactly the
encodings supplied by the caller, including for noncanonical inputs.

| Policy | Condition for acceptance |
| --- | --- |
| ZIP-215 | The supplied R decodes to a point and `[8](Q − R) = identity`. Decoding reduces the encoded y modulo the field prime and accepts either sign of zero. |
| Dalek strict | `[8]A ≠ identity`, the supplied R is the canonical encoding of Q, and `[8]Q ≠ identity`. |

The definitions of the base point, decoding, compression and challenge are
together in the policy specification. An auditor can read that specification
without following the SIMD layout. [Policy](coq/Policy.v) · [Challenge digest byte order](coq/Digest.v)

## What to audit

1. **The Rust boundary.** Check the policy-to-symbol match and the six SysV
   arguments. The 40-byte descriptor contains a key pointer, signature pointer,
   message pointer, message length and output index. Rust supplies live
   slices, separate writable scratch and output, and distinct in-range indices.
   The theorem covers every such permutation. Rust's construction of the
   descriptors and the loader's mapping of the audited image remain caller
   obligations. [Descriptor layout](../../../src/batch.rs) · [Dispatch](../../../src/verifier/driver.rs)
2. **The caller premises.** Read `admissible` and `Loop.entries`. Check
   no-wrap ranges, stack space, 64-byte scratch alignment, separation,
   and the mapped code and constants at the chosen load bias. The spatial
   preconditions for preparation, SHA, reduction and the ladder are explicit
   premises at each nonempty descriptor suffix. The proof derives scalar values, key-table
   selection, the returned mask and each lane's verdict. The linked fixed-base
   table is checked over all 273 signed multiples from −136 through 136,
   and all 17 entries of the fallback table are checked against the identity.
   [Input placement](coq/Audit.v) · [Per-call premises](coq/Loop.v) · [Static tables](coq/Tables.v)
3. **The wrapper-to-machine correspondence.** Compare the block bodies, call
   displacements, argument registers, frame offsets and tail copy with the
   linked disassembly. The descriptor transpose uses the shared indexed-load
   interpreter. The model composes the separately certified component calls
   using their live buffer views. Some wrapper instruction groups have
   handwritten effects, including tail padding and the eligibility mask
   applied to message lengths. [Wrapper image](coq/Image.v) · [Arguments](coq/Arguments.v) ·
   [Transpose and padding](coq/Routing.v) · [Hash handoff](coq/Hash.v) · [Scoring](coq/Score.v)
4. **The memory claim.** The nonempty execution models nested private storage
   as arbitrary bytes in the writable regions and reconstructs the wrapper's
   saved stack slots. The final-memory guarantee preserves every byte outside
   the output, 25,344-byte scratch and 16 KiB below entry RSP. The proof uses
   that grouped memory boundary. An instruction-by-instruction confinement
   result for every nested write, and equivalence of the entire grouped trace
   to hardware execution, remain outside the theorem. The empty path preserves
   all memory. [Frame model](coq/Return.v) · [Shared trust surface](../../README.md#shared-audit-surface)

## Replay

Use an unstripped release ELF containing both policy entries, the two Rust
read-only tables, and the standalone queue symbols used by the component
certificates. CI links this fixture from the production assembly and uses the
same ELF for all three immediate dependencies. [Link command](../../../.github/workflows/ci.yml) · [Audit targets](../../../.github/verification.mk)

```sh
python3 -B verification/crate/verify_batch/audit.py "$POLICY_ELF" \
  --output /tmp/verify-batch-audit --dependencies "$CALLEE_AUDITS"
python3 -B verification/crate/verify_batch/mutations.py "$POLICY_ELF" \
  --audit /tmp/verify-batch-audit
```

Use a fresh output directory. The audit checks the ELF digest of the component
evidence, re-extracts symbols, recompiles the component proof sources and checks
both fully qualified theorem types. Inspect `manifest.json`, `VerifyBatch/Checked.v`,
the two closed statements in `assumptions.txt` and the exit status of `coqchk`.
The recorded command enables Coq's bytecode reducer for the finite table
calculation and checks the full dependency closure. To replay with ordinary
kernel reduction, run the recorded command in the audit directory with
`-bytecode-compiler no`.

The mutation checks change copies of the linked code and separately reverse
the public acceptance condition with the original machine bytes intact. A
corrupted identity-table limb makes both public contracts provably false.
