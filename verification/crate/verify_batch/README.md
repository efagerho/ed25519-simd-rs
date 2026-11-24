# Production batch verification

Start with `assembled_zip215_verify_batch_correct` or
`assembled_dalek_verify_batch_correct`. Each instantiates the same
`batch_contract` at the address and exact linked bytes of the assembly symbol
called by Rust. The statement quantifies over the original descriptors, the
initial contents of the output array and any batch length, including zero.
[Theorems](coq/Object.v) · [Contract, execution and caller premises](coq/Audit.v) ·
[Rust entry points](../../../src/verifier/driver.rs)

For an admissible call the master theorem provides a return and the store log
of its instruction-level entry prefix. The zero-length return executes
through `ret`. For a nonempty batch, the log ends at the first descriptor
transpose. The grouped verdict uses the original inputs. Every such return has
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
   and the mapped code and constants at the chosen load bias. Read-only callee images and the two static tables must be disjoint from writable memory. The spatial
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
4. **The memory claim.** For a zero count the theorem fetches from the caller's
   byte memory, executes through `ret` and proves that every prefix writes
   nothing. For a nonempty batch it proves that every instruction up to the
   first descriptor transpose writes inside the caller's allowed regions.
   This includes all eight 40-byte copies on the tail path. The checker
   fetches each instruction from the memory produced by the preceding one.
   [Empty return](coq/EntryWrites.v) · [Nonempty entry](coq/StageEntry.v) ·
   [Tail loop](coq/TailWrites.v)
5. **Nested writes.** The caller bounds cover SHA state and digest stores,
   signature digits, round staging, the key-table output and both policy
   scorers' modeled stack writes. Each candidate's linked call pushes its
   return address. The digest wrapper executes its nested scalar reducer and
   returns to the instruction following that call. Replaying these stores
   yields the same reducer output memory used by the ladder's digit handoff. The shared scatter bounds check covers
   every instruction prefix from its mapped entry. From the wrapper's rejection
   call site, the proof follows the return-address push and the scatter's
   actual memory through `ret`. It reaches the wrapper's continuation in at
   most 88 callee instructions, including for malformed lane metadata. Check the buffer and stack
   offsets used to apply each component result. The decoded scorer's entry
   RSP is eight bytes below its aligned point buffer. The nested write regions
   exclude the wrapper's five saved GPRs and its caller's return word.
   [Rejection call and return](coq/RejectCall.v) · [Caller regions](coq/CallWrites.v) · [Nested regions](coq/NestedRegions.v) ·
   [Scorer alignment](coq/Score.v) · [Mapped image](coq/LoadedImage.v)
6. **The remaining boundary.** For a nonempty batch the verdict and
   final-memory guarantee still use grouped execution. It permits arbitrary
   final contents in private storage and restores the wrapper's saved slots.
   For the same nonempty entry CPU and the same prefix log, it permits both
   0 and 1 as the final value of the first scratch byte.
   A continuous byte-memory execution through preparation, decoding, table
   construction, the ladder and the scoring wrappers is still needed to
   cover every intermediate store of a complete call. The current theorem
   preserves every final byte outside the output, 25,344-byte scratch and
   16 KiB below entry RSP. [Call composition](coq/Loop.v) · [Frame model](coq/Return.v) ·
   [Shared trust surface](../../README.md#shared-audit-surface)

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
Redirecting a prologue spill to the caller's return address falsifies the
nonempty entry's confinement claim for every caller satisfying the original
memory placement and code mapping. A concrete execution also writes eight
zero bytes over eight zero bytes.
[Return-slot counterexample](tests/ReturnSlot.v)
