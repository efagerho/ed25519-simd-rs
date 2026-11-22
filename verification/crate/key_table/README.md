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
3. **Check the machine boundary.** The caller model groups the prologue,
   field operations and epilogue. It executes the control flow and table
   writes, and runs cached addition on the current point and staged input
   with arbitrary well-formed temporaries. Writable point, table and stack
   storage must be disjoint from each other and the code. The aligned
   staging area is 960 bytes, and the lowest nested return slot is at most
   2,424 bytes below entry RSP. The byte-level postcondition describes the
   table destination. Correspondence of the grouped caller to native execution,
   including save/restore of SysV registers, remains a human audit obligation.
   [Frame geometry](coq/Frame.v) · [Cached-add call](coq/Advance.v) ·
   [Shared machine and memory assumptions](../../README.md#shared-audit-surface)

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
