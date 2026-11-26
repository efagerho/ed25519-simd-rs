# Production batch verification

Start with `assembled_zip215_verify_batch_correct` or
`assembled_dalek_verify_batch_correct`. Each instantiates the same
`batch_contract` at the address and exact linked bytes of the assembly symbol
called by Rust. The statement quantifies over the original descriptors, the
initial contents of the output array and any batch length, including zero.
[Theorems](coq/Object.v) · [Contract, execution and caller premises](coq/Audit.v) ·
[Rust entry points](../../../src/verifier/driver.rs)

Both entry points return 1. For any batch length, the byte at each descriptor’s
output index is 1 exactly when that descriptor’s original signature verifies
under the selected policy. The theorem reads these bytes from the CPU that
executes the return to Rust. Replaying its instruction-level store log on
entry memory recovers every final byte, including scratch and stack.
[Native execution](coq/Iteration.v) · [All-row proof](coq/NativeLoop.v)

When preparation builds the public-key
tables, the log includes its six register saves, the 48 stores that initialize the eight identity entries,
the nested arithmetic calls for all eight multiples, and the 15 stores staging
the affine operand. The proof checks the eight-key transpose and the loaded
permutation indices, negation biases and opmask. It follows the eight-key branch
and all seven cached additions through their returns. For each multiple the 48
packing stores write the 320 expected qwords to its 16 signed rows. The builder
restores the six saved registers and its caller’s stack pointer, then returns
to chunk preparation through the return address read from memory. Preparation reads
eight 16-bit offsets from the linked image and stores the selected table pointers.
A second store writes exactly eight bytes. The proof reads each one back as 0 or 1
and identifies which original input made it 1. The common preparation routine
restores its frame and returns 1. Both wrappers clear the message lengths of ineligible lanes before hashing.
The log includes the call to SHA-512, its internal stores and its return.
Replaying the log from the Rust entry gives every byte of memory at that
return. For each eligible lane the 64 digest bytes on the stack are SHA-512 of
the original R, public key and message, in that order.
The shared call-return rule resumes the wrapper with the observed program
counter, stack pointer, memory and ordered writes. For every well-formed
assignment to volatile registers and flags, the next 15 instructions
pass the decoded R mask, eligibility bytes, scalar and digest pointers, output
pointer, and batch length to the policy scorer. Replaying the four argument
stores and the return-address push preserves every digest byte. Those bytes
reach the scorer alongside the signed S digits, the decoded Edwards point R,
and all 17 signed multiples of each decoded public key. The log covers the
scorer’s six register saves and its aligned 1,280-byte point buffer. ZIP-215
calls its candidate immediately. Dalek calls its candidate for a nonempty
strict R mask, after reloading the saved argument pointer from the stack.
Both scorers follow the digest reducer, including the nested
Montgomery reduction and the stores that pack each lane’s 64 signed digits.
For every eligible lane these digits reconstruct the original SHA digest
modulo L. The next linked call passes those digits, the signed S, the selected table
pointers and the coordinate flag to the ladder. ZIP-215 requests extended
coordinates and Dalek requests XYZ. On that actual entry state,
every point returned by the ladder component represents `[S]B − [k]A` for the
original lane. The native trace continues through the first staging return and
the seed calculation. Every staged word comes from the base or key table
entry selected by digit pair 31 in that lane. On the same trace, the 160
qwords written to the accumulator represent the signed odd multiple
selected by the high challenge digit. XYZ satisfy the first doubling’s
input bounds, and every T limb is zero. The first doubling and both cached
additions then execute from that point buffer. Their combined store log
covers the three return-address pushes, each child frame, and each update
to the point. At the return from the even-key addition the original buffer
holds `[16]Odd + Base + Even` in XYZ with reduced limbs and zero T.
The 31 remaining rounds each stage the next digit pair and call the ladder
step on that same point. The returned CPU reads its continuation from the
original stack word. Its point buffer represents `[S]B − [k]A` for each
eligible lane, and replaying its store log gives the returned memory. The
candidate releases its frame, restores RBX and R12 from their saved bytes,
and returns to its policy scorer with RSP pointing at that same point.
[Native seed](coq/LadderSeed.v) · [Top digit pair](coq/LadderTop.v) · [Candidate return](coq/CandidateReturn.v)
Dalek intersects the decoded-R mask with the eight staged
eligibility bytes. It then compares the five original Y limbs against
`p = 2²⁵⁵ − 19` with the sign bit removed. The native lane mask retains precisely
the eligible lanes with Y below p. If that mask is empty, the CPU jumps to the
scorer’s rejection epilogue and sets EAX to zero. Otherwise it calls the linked
small-order check with RDI pointing at the decoded R coordinates. The call
returns to the scorer through its saved address. The scorer clears each lane
whose decoded R satisfies `[8]R = identity`. Its surviving mask specifies the
original eligibility, canonical Y and non-small-order R together. When every lane
is cleared, the scorer restores its six saved registers from the stack and
jumps to scatter with a zero mask. Scatter publishes a zero byte at each live
descriptor’s output index. The same log follows its return to the batch loop
for more rows or through the outer `ret` for the final chunk.
[Scorer frame](coq/ScoreSaved.v) · [Scatter and batch return](coq/ScorePublish.v) · [Dalek candidate call](coq/StrictCandidateCall.v)
[SHA call](coq/HashEntry.v) · [Digest and store log](coq/NativeHash.v) ·
[Call-return rule](../../machine/abi/CallReturn.v) · [Scorer handoff equivalence](tests/HashHandoff.v) · [Scorer entry](coq/ScoreCall.v) · [Scorer execution](coq/ScoreStart.v) · [Native challenge digits](coq/ReducedDigest.v) · [Ladder call](coq/LadderEntry.v) · [Product on the original bytes](coq/LadderProduct.v) · [First staging return](coq/LadderStage.v) · [Dalek R mask](coq/StrictRStart.v) · [Canonical Y decision](coq/StrictRCanonical.v) · [Small-order call and rejection](coq/StrictRCall.v) · [Native return](coq/StrictOrderReturn.v) · [Strict lane decision](coq/StrictScreen.v)

The first chunk and every later chunk share one dispatch proof from the
scalar return. It follows the returned mask bank through decoding and
eligibility screening, then proves either that the chunk has no active lanes
and scatters zeros, or that SHA returns with the inputs needed for scoring.
[Scalar screening](coq/ChunkScreen.v) · [Dispatch from the scalar return](coq/ChunkDispatch.v)

The batch loop uses the same sequencing rule for dispatch, scoring and
publication. In the scorer, each block takes the cursor returned by the
previous block. Dalek’s R screen also passes the mask bank from the first
block through the canonical-Y check. The ZIP-215 torsion check accepts any
incoming mask bank and passes its returned CPU to the verdict block.
[Scoring decision](coq/ScoreDecision.v) · [Mask handoff proofs](tests/ScorerMasks.v)

Both policies require canonical S and decodable R and public-key encodings.
For a decoded key A, the proof relates every signed cached row from −8 to +8
to its Edwards multiple of A. Dalek reads the +8 row of each selected table
and excludes the lane exactly when [8]A is the identity. The proof follows the
filter through its carry-helper calls, conditional flag store and return. The
strict wrapper tests all eight resulting eligibility bytes. If all are zero,
the batch caller scatters zeros, even when the key and R decoded successfully.
[Decoded public keys](coq/DecodedKey.v) · [Signed table rows](coq/PreparedTables.v) ·
[Weak-key decision](coq/FilterMeaning.v) · [Dalek dispatch](coq/StrictDispatch.v)

ZIP-215 passes the product and decoded R to the torsion check. It intersects the
returned bits with R validity. Dalek tests each surviving lane by comparing
`R.y × Q.Z` with `Q.Y`, then `R.x × Q.Z` with `Q.X`. If the first
intersection clears all lanes, it skips the X comparison and publishes zeros.
Both paths pass the resulting mask to scatter, which writes each verdict byte
at its original descriptor index.
[ZIP torsion return](coq/ZipTorsion.v) · [ZIP mask](coq/ZipVerdict.v) · [Dalek coordinate test](coq/StrictCoordinate.v) · [Dalek verdict](coq/StrictVerdict.v) · [Published verdicts](coq/ScoredChunk.v)

The assembly resumes at the caller’s return address with RSP advanced by eight
and restores its SysV callee-saved integer registers. Preparation may reject a
whole chunk, and a scored chunk can contain both eligible and ineligible lanes.
Only live lanes publish output. A padded copy of the last descriptor never
adds an output store. [Scatter targets and preservation](coq/RejectOutputs.v) · [Return](coq/RejectFinish.v)

## Acceptance on the input bytes

Each output byte in `Audit.returned` answers the shared `Ed25519.Signature.signature_accepts` predicate for the original descriptor. The predicate defines the two group equations, scalar cutoff, hash and encoding rules. Its equivalence theorem explains why ZIP-215 can test the cofactored difference and why the strict path can compare coordinates after screening. [Signature formulas and equivalence proofs](../../ed25519/README.md)

Here the audit is the handoff from memory to those formulas. Check the four byte strings produced by `read_input`, including their lengths, the digest's little-endian interpretation and the output index read from each descriptor. [Input descriptor](coq/Policy.v) · [Challenge digest byte order](coq/Digest.v)

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
   premises at each nonempty descriptor suffix. The layout uses a fixed witness for
   mask and table contents. Execution takes the actual mask bank and staged tables.
   The proof derives scalar values, key-table
   selection, the returned mask and each lane's verdict. The linked fixed-base
   table is checked over all 273 signed multiples from −136 through 136,
   and all 17 entries of the fallback table are checked against the identity.
   [Input placement](coq/Audit.v) · [Per-call premises](coq/Loop.v) · [Static tables](coq/Tables.v)
3. **The wrapper-to-machine correspondence.** Compare the block bodies, call
   displacements, argument registers, frame offsets and tail copy with the
   linked disassembly. The first staging run fetches instructions until control
   leaves the wrapper. Its proof identifies the exit as the preparation call and
   accounts for every write through that call. The initial chunk and later chunks
   share the proofs of descriptor selection, transpose, saved stack slots and the
   next descriptor address. Both then use the same scalar and policy dispatch. Check that each nested call consumes the preceding cursor’s
   registers and memory. In particular, the prepare call must stage the last
   live row into short-chunk padding, and the SHA handoff must clear the lengths
   of ineligible lanes. [Selection](coq/ChunkRows.v) · [Staging](coq/StagedRows.v) · [Hash handoff](coq/HashEntry.v) · [Dispatch](coq/FirstDispatch.v)
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
   [Rejection call and return](coq/RejectedPath.v) · [Native dispatch](coq/FirstDispatch.v) · [Key-table initialization](coq/TableStart.v) · [Native cached coordinates](coq/TableValues.v) · [Table staging and transpose](coq/TablePackedInputs.v) · [Signed row contents](coq/TableSignedWords.v) · [Eight-multiple loop](coq/TableRounds.v) · [Builder return](coq/TableUnwind.v) · [Caller regions](coq/CallWrites.v) · [Nested regions](coq/NestedRegions.v) ·
   [Scorer alignment](coq/Score.v) · [Mapped image](coq/LoadedImage.v)
6. **Verdicts across iterations.** Check that `Iteration.more` passes the
   actual scatter continuation into staging and that the recursive call starts
   from the resulting CPU and store log. R12 counts the remaining rows, RBX
   advances by 320 bytes and R13 retains the original output capacity. The
   loop invariant covers every earlier descriptor’s output index, including a
   permuted index. Preparation, SHA and scoring preserve those bytes. Scatter
   writes only to the current live indices. At the final return the invariant
   covers every descriptor. The same trace confines every store to output,
   25,344 bytes of scratch or the 16 KiB below entry RSP.
   [Execution and return](coq/Iteration.v) · [All-row induction](coq/NativeLoop.v) ·
   [Protected output bytes](coq/BatchWindow.v) · [Scatter targets](coq/RejectOutputs.v) ·
   [Staging back edge](coq/ChunkRestart.v) · [Shared trust surface](../../README.md#shared-audit-surface)

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

A nine-row control sends the first eight rows to output indices 1 through 8
and the padded tail to index 0. It checks both policies’ intermediate bytes,
final bytes, and the addresses written during the tail. Shortening the
descriptor stride from 320 to 280 bytes makes the public theorem fail.
[Two-chunk execution](tests/TwoChunks.v) · [Damaged stride](tests/NextDescriptor.v) · [Linked mutations](mutations.py)

A decoder control runs the decoder from its transposed input words through the
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
