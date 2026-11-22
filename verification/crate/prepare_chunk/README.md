# Eight-lane chunk preparation

Audit `assembled_prepare_chunk_correct` for the common ZIP-215 entry and the
Dalek entry. A chunk is ready exactly when at least one signature has
`S < L`, a decodable public key and a decodable R. Dalek also requires that
multiplying that key by eight gives a point other than the identity. If the
three masks have an empty intersection, preparation skips table construction. [Public contract](coq/Audit.v) ·
[Proof](coq/Object.v)

On success, each lane retains the original key and R bytes, and its signed
digits reconstruct S for a canonical scalar or are all zero otherwise.
The low and high decoder mask bytes correspond to keys and R respectively.
The theorem preserves the raw Y limbs needed to check noncanonical R encodings.
All eight computed tables have initialized, bounded rows. For a decodable
key, the selected table contains its signed Edwards multiples from −8 to +8.
For an undecodable key, the selected pointer equals the caller's fallback
pointer. Every eligibility byte is exactly zero or one. A rejected chunk
exposes only its return status. [Output predicates](coq/Composition.v) ·
[Return paths](coq/Dispatch.v)

## What to audit

1. Check both symbol extents and rel32 call targets against the release ELF.
   The common extent includes all eight little-endian offsets used by the
   masked table-pointer addition. The modeled loop advances the pointer row
   by eight bytes and the destination by 32 bytes per lane. Check the branches,
   merged mask, byte expansion, and strict zero-qword test against the native
   instructions. [Block encoding](coq/Caller.v) · [Assembly](../../../src/wide/avx512ifma/prepare_chunk.S)
2. Follow one lane from the two pointer rows to its scalar bytes at
   signature + 32, the paired decoder inputs, and the selected table. Check
   the split of the decoder output into consecutive A and R points and the
   unchanged R rows across the key-table call. The weak-key proof reads
   digit eight through the actual selected pointer and derives its value from
   the builder's table bytes. [Input staging](coq/Staging.v) ·
   [Callee composition](coq/Composition.v) · [Filter](../dalek_post_hash/coq/Keys.v)
3. Check the boundary between the block model and hardware. The theorem
   binds complete wrapper bytes and interprets the wrapper's copies, calls,
   metadata stores and control flow as grouped operations. The scalar callee
   runs on a concrete byte-memory state. The decoder and table builder use
   their existing coordinate and table-write projections. The correspondence
   of these groups to x86 effects, including preservation of saved registers
   and disjoint scratch fields across calls, requires review. A single
   instruction-by-instruction execution of the combined flat memory and
   stack lies outside this contract. [Shared assumptions](../../README.md#shared-audit-surface) ·
   [Decoder contract](../decompress_r/README.md) · [Table contract](../key_table/README.md)
4. Check Rust's pointer lifetimes, feature requirements, scratch alignment and
   offsets against the assembly ABI. The contract allows repeated read-only
   inputs. The outputs and stack occupy separate writable regions, and the
   caller supplies a readable identity table. Rust discards both outputs
   after rejection. [Rust layout and call site](../../../src/wide/avx512ifma/prepare.rs) ·
   [Native differential tests](../../../src/wide/avx512ifma/tests/prepare_chunk.rs)

Run the audit against a linked Dalek ELF retaining the preparation entries and
the Dalek callee symbols. CI uses the `prepare-chunk-mutations` target to
replay same-ELF callee evidence, check the public theorem with `coqchk`, and
recompile it against damaged copies of the binary. [Audit driver](audit.py) ·
[Mutation checks](mutations.py) · [CI targets](../../../.github/verification.mk)
