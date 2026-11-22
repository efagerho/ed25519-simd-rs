# Strict Dalek post-hash verification

The public theorem is `assembled_dalek_post_hash_correct`. Read its contract
and the lane predicate `accepts` first. For each active lane let
**Q = [s]B − [digest mod L]A**, where the ladder reads the signed digits
of s and the reducer reads the digest words. The lane scores true exactly
when its input eligibility flag is set, **[8]A ≠ 0**, the original 32 bytes
of R equal the canonical compression of Q, and **[8]Q ≠ 0**. The zero
here is the Edwards identity. The Rust verifier calls the decoded entry. The theorem also covers
standalone queue entries with the same acceptance predicate. [Public contract](coq/Audit.v) ·
[Theorem](coq/Object.v)

## What to audit

* **Key filter.** Follow the eight pointers to positive digit 8 in the same
  key tables supplied to the ladder. The filter tests whether the cached
  coordinates represent the identity. It can skip the second comparison
  when the first one fails in every lane. The proof checks the table
  offsets, the biased subtractions and carry bounds, and the two field
  equalities against the cached point representation. [Keys.v](coq/Keys.v)
* **Standalone queue.** Push may immediately score a whole chunk false.
  The low-word shortcut can only send work to the queue or to the full
  eight-encoding screen. A rejecting screen excludes a strict match for
  every lane, for either sign bit. Otherwise push saves the candidate,
  original encodings and metadata and flushes at eight occupied slots.
  Flush handles zero through eight chunks, clears the count, and scatters
  the low mask byte first in queue order. Check the occupied-slot premises
  in `flush_result` and the copy destinations in `push_abi`.
  [Screen.v](coq/Screen.v) · [Queue.v](coq/Queue.v) · [Staging.v](../post_hash/Staging.v)
* **Decoded entry.** Chunk preparation leaves R in the second decoder output and saves
  the high mask byte. Rust passes both to the decoded entry. Trace that
  handoff across the assembly and Rust layouts. The proof obtains both from the linked decoder certificate,
  uses the original radix-51 Y digits for canonicality, rejects small
  order, and tests both X and Y against the projective candidate. A zero
  X cannot pass the small-order check, including the negative-zero case.
  [Chunk preparation](../../../src/wide/avx512ifma/prepare_chunk.S) · [Rust scratch layout](../../../src/wide/avx512ifma/prepare.rs) · [Decoded.v](coq/Decoded.v)
* **Linked code and grouped operations.** Compare the manifest with the
  release ELF for the five Dalek wrappers, the shared scatter routine,
  and their callees. Check each named instruction group against its stated
  effects, including flags, call arguments, scratch, register preservation,
  mask shifts, and VSIB gather addressing. Coq checks the encoded wrapper
  bytes, branch destinations, call targets and helper bindings. The mapping
  from a group to its register and memory effects is part of the trust
  surface, including the decoded-entry frame and the flush call sequence.
  [Caller.v](coq/Caller.v) · [Binding.v](coq/Binding.v) · [Shared machine and memory assumptions](../../README.md)

At the ABI, the caller supplies the digest, signed S digits, valid tables
for B and the eight public keys, initial eligibility flags, and aligned,
valid, disjoint allocations as required by the callee contracts. The
candidate existence clause guarantees a return for well-formed calls with
the reducer's digit bytes passed to the ladder. The call observation ties
that return to the point being scored. The Rust driver hashes the inputs and calls assembly to prepare keys and
check and recode S.
The post-hash theorem takes the resulting S digits and eligibility as inputs.
Standalone queue callers must start with an empty queue and flush the final
partial batch. For in-range active
indices the proof specifies each write in order, preserving every other
output. If multiple chunks target the same index, the last actual store
wins. [Call observation](../post_hash/Product.v) · [Rust ABI and layout](../../../src/wide/avx512ifma/post_hash_asm.rs) · [Rust driver](../../../src/verifier/driver.rs)

## Replay

Build the release audit executable with the standalone push entry retained
as shown in the [recompression replay instructions](../dalek_recompress/README.md#replay).
Set `elf` to its path and use a fresh audit directory. The audit builds
missing callee certificates or reuses them from `--dependencies DIR`
after checking them against the same ELF. It checks the public theorem's
type and assumptions and runs `coqchk` on its dependencies.

```sh
python3 -B verification/crate/dalek_post_hash/audit.py "$elf" --output /tmp/dalek-post-hash-audit
python3 -B verification/crate/dalek_post_hash/mutations.py "$elf" --audit /tmp/dalek-post-hash-audit
```
