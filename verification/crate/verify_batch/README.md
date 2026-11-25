# Production batch verification

Start with `assembled_zip215_verify_batch_correct` or
`assembled_dalek_verify_batch_correct`. Each instantiates the same
`batch_contract` at the address and exact linked bytes of the assembly symbol
called by Rust. The statement quantifies over the original descriptors, the
initial contents of the output array and any batch length, including zero.
[Theorems](coq/Object.v) · [Contract, execution and caller premises](coq/Audit.v) ·
[Rust entry points](../../../src/verifier/driver.rs)

For an admissible call the master theorem provides a return and the store log
of its instruction-level entry prefix. The zero-length call executes through the outer `ret`, as does a single chunk
with no lane passing the scalar and paired-decoding checks. For other nonempty
batches the same log reaches the next chunk after a rejection, or follows the
call into the key-table builder when an eligible lane exists. The builder
receives the decoded public-key point and the destination for eight tables.
Its return address is read back from the actual stack. A lane is eligible
here exactly when S is canonical and
both encoded Y coordinates admit an Edwards X coordinate. The final signature
verdict on these continuing paths comes from grouped execution on the original
inputs. Every such return has
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
   nothing. Every nonempty batch trace runs through the first nested signature-scalar call. Every recorded write is inside
   the caller’s allowed regions.
   This includes all eight 40-byte copies on the tail path, the four transposed
   vector stores, eight output-index stores and the call's return-address push.
   The child enters with the linked target PC, its return word at RSP and the
   pointer matrix and output metadata addresses in RSI and RCX. All 256 matrix
   bytes match the corresponding fields at the start of the transpose. Each matrix byte also matches its source in
   Rust's original descriptor array. For a short first chunk, the copy loop
   repeats all 40 bytes of the last live descriptor in each padding lane.
   The scalar return mask tests the corresponding original S against L in
   every lane. Valid lanes have 64 signed digits in −8 through 7
   reconstructing S, and invalid lanes have 64 zero digits. The ZIP-215 path enters common preparation directly.
   The Dalek path first pushes RBX and calls common preparation. Both prepare
   the eight scalar pointers in the actual stack and pass scratch + 512 as
   the digit destination. The proof checks the scalar symbol against the live
   byte image, appends its digit stores, and reads the continuation from the
   stack. Replaying the combined log recovers every byte at that return.
   The decoder receives the opmask bits produced by those scalar instructions,
   including bits in registers the scalar call preserved.
   If any scalar is canonical, both entries execute the two 32-byte stores
   for each of eight lanes and call the paired decoder. Its 512 input bytes
   match the original public keys and R encodings, including padded lanes.
   The output point pointer, pair count and pushed return PC are established
   on the same memory. The decoder pushes its five saved registers, aligns RSP,
   allocates 640 bytes, and calls its first field setup. The proof checks the two
   live return words, the four broadcast field constants in every vector lane,
   and confinement of the stack stores. The next sixteen instructions load and
   transpose the public keys. For each lane and each of the four qwords, the
   resulting ZMM register contains the word at the original descriptor’s key
   pointer. The aligned permutation tables are read from the live image.
   The next two instructions collect bit 255 of each key into EAX. The
   following fifteen produce five bounded radix-51 limbs per lane whose
   integer value is the original key modulo 2²⁵⁵. This includes Y encodings
   greater than or equal to the field prime. Five aligned 64-byte stores
   then save Y. Reading each qword back from the live scratch buffer recovers
   the corresponding register limb. The store log covers the 320 destination
   bytes starting at scratch offset 1344 for A and 2624 for R. [Sign and Y extraction](coq/DecoderUnpack.v) ·
   [Y in scratch memory](coq/DecoderSave.v)
   The decoder uses this saved Y as its second multiplication operand. The
   proof follows the calls into the column and convolution helpers, their stack
   writes and returns, and the carry pass. At decoder offset 509, the live
   limbs represent Y² modulo p and limb zero is at least two, as required by
   the following subtraction. [First multiplication](coq/KeySquare.v) ·
   [Native field kernels](coq/DecoderProduct.v) ·
   [Decoder transpose](coq/DecoderWords.v) · [Decoder frame](coq/DecoderFrame.v) · [Decoder entry](coq/BatchDecode.v) · [Encoding copies](coq/PrepareCopies.v)
   The trace continues through the scaling instructions, the carry helper,
   the second multiplication and the stores of U, V and UV. Setup returns
   to decoder offset 73 for A and offset 101 for R using its live stack word.
   The decoder saves the eight public-key signs in R13D, advances the source
   by 256 bytes and the point destination by 1280 bytes, then calls the same
   setup on the eight staged signature encodings. Both calls share one store
   log. The returned CPU retains R’s Y digits and both sign masks.
   Each call derives the U, V and UV limbs in live memory from the native
   scale, carry and product instructions. [Paired setup](coq/PairedSetup.v) ·
   [Setup memory and arithmetic](coq/SetupValues.v)
   The next five instructions save R’s signs and call pow2. The proof checks
   the live arguments, return word, stack alignment, and separation of the
   640-byte result from both 320-byte inputs, private stack and code.
   The pow2 certificate starts with those exact registers and bytes. Its
   block interpreter attaches the linked instruction address to each vector
   store and call-stack push. Replaying those writes on the decoder’s live
   memory gives the memory of the returned CPU. For each of the sixteen inputs the theorem derives the limb bounds and
   the exponentiation result from the corresponding descriptor bytes. With
   Y equal to the low 255 bits and U = 121666·(Y² − 1), the output represents
   (U·(Y² − U))^((p − 5)/8) modulo p. The block model
   exports ZF and leaves CF unspecified at this boundary. On the returned
   CPU, the decoder reloads the four curve constants, enters root selection,
   squares the power for A and multiplies it by the saved U×V. At the first
   comparison the five registers represent (power²)·U·V for each original
   key and satisfy the comparison kernel’s limb bounds. The proof follows both
   masked comparisons, the numerator-zero test, the predicate ORs and the
   transfer to R10. The resulting byte classifies root existence for all
   eight keys. The negative-root mask is kept for the sign-adjustment code.
   The next nested multiply takes U from the live registers and the power
   from the stack. The five stores at offsets 1084 through 1112 write the
   resulting X candidate to point scratch. The theorem identifies all forty
   stored limbs and preserves the validity byte across the call.
   The alternate-root multiply loads the five limbs of the square root of
   minus one from the linked ELF. The decoder then selects a candidate per
   lane, computes its parity and conditionally negates it using the original
   sign bit. The final stores write X, Z = 1 and T = XY, preserving Y. The
   nested return reads its target from the live stack and delivers the eight
   validity bits in EAX. [Signed root](coq/SignedRoot.v) · [Coordinate stores](coq/ExtendedPoint.v) · [Public-key return](coq/KeyReturn.v)
   The caller saves the key byte in R13D, passes the staged R point and
   its own exponentiation result to the same code, and resumes at offset 222
   with both validity bytes. The decoder packs them into EAX, restores RBP, RBX and R12–R14 from their five live stack slots, and executes its outer return to chunk preparation. [Paired point returns](coq/PairReturn.v) · [Signature-R criterion](coq/SignatureDecision.v) · [Decoder return](coq/DecoderReturn.v) · [Eligibility branch and R-validity store](coq/EligibleLanes.v)
   [Field setup and inputs](coq/PowerInputs.v) · [Exponentiation call](coq/DecoderPower.v) · [Return and write log](coq/PowerWrites.v) · [Root comparison input](coq/RootTest.v) · [Validity byte](coq/Selection.v) · [Root candidate](coq/RootCandidate.v)
   If either the scalar mask or the combined eligibility mask is zero, the decoded branches, pops and returns take both
   policies back to the wrapper's preparation continuation with RSP restored,
   the same EAX and no additional stores. The wrapper passes its original
   output pointer and count to scatter. The proof follows the nested return
   back to the wrapper with the combined store log and restored RSP. Its
   status and remaining-count tests then either enter the next chunk or
   execute the five pops and outermost return. For that return the caller
   PC, RSP and every final memory byte are derived from the same execution.
   With one to eight descriptors whose original S values all exceed or
   equal L, the assembly returns 1 and writes zero to every original output
   index. The master theorem requires this instruction-level return. Its five
   pops recover the original saved registers from the stack and RBP retains
   its entry value. The proof derives the verdict, byte memory, and SysV return
   guarantees from this execution. The proof also covers an arbitrary permutation of the output
   indices and the actual active count of a short chunk.
   [Single-chunk corollary](coq/Audit.v) · [Index staging](coq/IndexStores.v) · [Scatter values](coq/ScatterZeros.v)
   [Scalar input and digit correspondence](coq/ScalarInputs.v) · [Rejection result](coq/RejectExecution.v) · [Wrapper exit](coq/RejectFinish.v) · [Rejection scatter](coq/RejectDispatch.v) · [Rejection returns](coq/PrepareUnwind.v) · [Nested scalar call](coq/BatchScalar.v) · [Preparation prologues](coq/PrepareNative.v) ·
   [Empty return](coq/EntryWrites.v) · [Nonempty entry](coq/StageEntry.v) ·
   [Tail copies](coq/TailCopy.v) · [Tail write bounds](coq/TailWrites.v) · [Preparation handoff](coq/StageWrites.v)
5. **Nested writes.** The caller bounds cover SHA state and digest stores,
   signature digits, round staging, the key-table output and both policy
   scorers' modeled stack writes. Chunk preparation writes its eight scalar
   pointers, pushes the linked continuation, and receives the signature-scalar
   result in that same memory. Each candidate's linked call pushes its
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
   [Rejection call and return](coq/RejectedPath.v) · [Native dispatch](coq/FirstDispatch.v) · [Key-table call](coq/TableEntry.v) · [Caller regions](coq/CallWrites.v) · [Nested regions](coq/NestedRegions.v) ·
   [Scorer alignment](coq/Score.v) · [Mapped image](coq/LoadedImage.v)
6. **The remaining boundary.** For batches longer than eight or with an eligible lane in the first
   chunk, the verdict and final-memory guarantee still use grouped execution. It permits arbitrary
   final contents in private storage and restores the wrapper's saved slots.
   For such an entry CPU and the same prefix log, it permits both
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

The positive control supplies a single row with S equal to 2²⁵⁶ − 1 and
initializes the output to 1. Both policy entries reject it, overwrite the
output with 0 and return to the caller. The control checks the saved registers
and each store address. Its replay theorem and mathematical rejection use
the same input and final CPU. [Single-row execution](tests/RejectedBatch.v)

A second control runs the decoder from its transposed input words through the
five stores of Y. One lane encodes 2 and the other seven encode p + 1 with
the sign bit set. It checks the sign mask and reads each unreduced value back
from scratch. [Decoder execution](tests/DecoderY.v)

The mutation checks change copies of the linked code and separately reverse
the public acceptance condition with the original machine bytes intact. A
corrupted identity-table limb makes both public contracts provably false.
Redirecting a prologue spill to the caller's return address falsifies the
nonempty entry's confinement claim for every caller satisfying the original
memory placement and code mapping. A concrete execution also writes eight
zero bytes over eight zero bytes.
Changing one shuffle immediate still reaches the preparation call, but all eight
key slots contain message pointers on a concrete mapped-memory execution.
[Return-slot counterexample](tests/ReturnSlot.v) · [Transpose counterexample](tests/Transpose.v)
