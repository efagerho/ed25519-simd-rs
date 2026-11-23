# Eight-lane SHA-512 challenge

For each lane `j`, the desired result is the 64 bytes of
`SHA-512(R[j] || A[j] || message[j])`. Byte `i` of that digest belongs at
`out + 64*(i/8) + 8*j + i%8`, where division rounds down. This places each
eight-byte slice in the order consumed by the scalar reducer.
`challenge_digests` states this directly over entry and output memory. It also
covers messages of length zero and lanes that finish in different blocks.
[Output.v](coq/Output.v) · [Rust caller](../../../src/sha512.rs) · [SHA-512 definition](../../sha512/README.md)

## What is proved

`scheduled_rounds_correct` proves for every input block and incoming state
that one lane of the optimized round arithmetic with its 16-slot schedule
produces the same eight working words as the reference's 80 rounds.
At round `t`, the ring contains `W[t..t+15]`. The first 64 rounds each
consume a word and replace it with `W[t+16]`. The last 16 consume the
remaining words. Every intermediate addition may wrap. Coq also proves that
the challenge length fits the standard and that message length `m` gives
`1 + floor((m+80)/128)` padded blocks. [Compression.v](coq/Compression.v) ·
[Length and layout](coq/Output.v)

## What remains for the linked theorem

The release theorem should quantify over every valid SysV entry and prove a
return to the caller with `challenge_digests`, preserved callee-saved
registers, and writes confined to the output and private stack. Its premises
should permit unaligned buffers and overlapping read-only inputs. An empty
message requires zero readable bytes at its supplied pointer.
The current proofs stop at the mathematical lane operations. The following
obligations connect them to the native routine.

1. **Bind code and constants.** Extract the linked symbol and its referenced
   read-only bytes. Check instruction encodings, relative branch and call
   targets, the IV, round constants and byte-shuffle mask. Prove the emitted
   rotates, shifts and ternary-logic immediates implement the functions used
   by the lane theorem. Check new instruction semantics against hardware.
2. **Prove the block loader.** Relate each transposed lane to the corresponding
   block of `Spec.pad`. Cover the initial 64-byte prefix, full and partial
   rows, exact half-block boundaries, the extra padding block, and both
   length words. For a masked byte load, require readability only for the
   enabled byte addresses.
3. **Compose the loops.** Prove the round-register rotation, ring slot and
   constant address at every iteration. Use `scheduled_rounds_correct` and the
   saved incoming state for feed-forward. At block entry, each unfinished
   lane must hold the hash of its preceding blocks. Once a lane finishes,
   later stores must preserve its output. Prove termination at the longest
   lane's last block and preservation of the return address through the
   aligned frame and internal calls.
4. **Audit the result.** Check the byte layout against the reducer and the
   input registers against the Rust call. Exercise the final theorem by
   mutating a constant, a round or shuffle immediate, a masked load, and the
   final-lane store mask in the certified image. Each mutation should break
   certification. [Assembly](../../../src/sha512.S) · [Machine and memory trust surface](../../README.md#shared-audit-surface)

CI checks the current proofs with `make -f .github/verification.mk sha512-spec`
after building the shared Coq libraries.
