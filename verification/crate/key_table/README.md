# Signed public-key tables

The public theorem is `assembled_key_table_correct : key_table_contract`.
For a valid decoded affine point P in a selected lane, table entry 8 + d
represents **[d]P** for every digit from −8 through +8. The single-table
path uses lane zero. The eight-table path writes eight consecutive tables
in lane order. For bounded input limbs, every output byte is initialized
and every limb is below 2⁵², including in lanes rejected by the decoder.
The theorem bounds every table store and proves that the table writes
preserve bytes outside the requested extent. [Public contract](coq/Audit.v) ·
[Linked theorem](coq/Object.v)

## What to audit

1. **Check the assembly call and the consumer.** RDI points to a writable,
   64-byte-aligned 1,280-byte X/Y/Z/T buffer. RSI points to 8-byte-aligned
   storage for RDX tables, with RDX equal to 1 or 8. Each table contains
   seventeen 160-byte rows. The twenty little-endian words in a row encode
   Y−X, Y+X, 2dT and 2Z in radix 2⁵¹. Check that the consumer supplies the
   same lane and signed digit. The builder and the full ladder use the same
   `scalar_cache` definition. The Edwards interpretation requires a valid
   extended point with Z equal to one in the field. It applies to points
   with torsion as well as prime-order points.
   [Eight-table call](../../../src/wide/avx512ifma/prepare_chunk.S) ·
   [Cache representation](../../curve25519/group/Representation.v) ·
   [Ladder table premise](../full_ladder/coq/Operands.v)
2. **Check the code identity and the live operands.** The certificate binds
   every executable block, its branch targets, the permutation and bias tables,
   and all five limbs of 2d to the linked ELF. It also checks the product and
   carry fragments at their interior decoder and torsion addresses and imports
   the linked cached-add theorem. Follow the first iteration's three staged
   fields into the seven full-T, affine cached additions. Check the projection
   of memory-source arithmetic onto the five read-only X limbs, the helper
   register conventions, and the opmask, lane order and half selector of each
   signed store. Unpack and shuffle use the shared byte-level machine model.
   [Byte expansions](coq/Image.v) · [Field kernels](coq/Fields.v) ·
   [Lane and store semantics](coq/Pack.v) · [Caller execution](coq/Execution.v)
3. **Check the production call boundary.** The `native_eight` field starts
   at the linked builder symbol with RDX equal to eight. Its executor reads
   RSP, RDI and RSI from the incoming CPU. Check the disjoint buffers, stack
   placement, code mappings and alignment premises. The result restores
   the six SysV callee-saved registers, advances the 64-bit RSP by eight and
   returns to the word read at entry RSP. The returned write log extends
   the caller’s log with the actual stores, including nested calls. Each
   store lies in the 2,424-byte private stack, the point, or the eight tables.
   The signed entries are read from the returned byte memory. The caller
   can choose the three buffer addresses independently.
   [Callable theorem](coq/NativeBuilder.v) · [Signed memory entries](coq/NativeTable.v) ·
   [Shared machine and memory assumptions](../../README.md#shared-audit-surface)
4. **Check the single-table boundary separately.** The `table_execution`
   field checks the grouped control flow, table writes and arithmetic for
   RDX equal to one or eight. For the lane-zero, single-table path, the
   correspondence of that grouped execution with the native caller and its
   register restoration remains an audit obligation.
   [Grouped execution](coq/Execution.v) · [Frame geometry](coq/Frame.v)

## Replay

Use a linked release ELF containing the builder, decoder, torsion helper and
cached addition. CI reuses the cached-add certificate from the full-ladder audit
of the same ELF. The standalone command builds its dependencies.

```sh
python3 -B verification/crate/key_table/audit.py "$ZIP_ELF" --output /tmp/key-table-audit
python3 -B verification/crate/key_table/mutations.py "$ZIP_ELF" --audit /tmp/key-table-audit
```

The mutations change the frame size, single-lane branch, signed T mask, tail
store, loop bound, affine flag and a shared carry shift. For the carry change,
the audit re-extracts the modified arithmetic instructions and checks a concrete
wrong coordinate before requiring rejection of the public theorem.
