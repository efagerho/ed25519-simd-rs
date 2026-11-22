# Shared post-hash proof code

Both policy proofs use the same scalar reduction, point ladder and queue
layout. The public results live with the [Dalek](../dalek_post_hash/README.md)
and [ZIP-215](../zip215/README.md) wrappers.

| Definition | What to audit |
| --- | --- |
| [Staging.v](Staging.v) | Compare the symbolic SysV arguments and register clobbers with the two callees. Check the six queue copy ranges, count offset and point destination against the [standalone queue layout](../../../src/wide/avx512ifma/post_hash.inc). The ladder's final argument selects XYZ for Dalek or extended coordinates for ZIP-215. |
| [Product.v](Product.v) | Follow the same 512 signed digest-digit bytes from the reducer's return to the ladder's input. The point formula reads s from the other digit input and the challenge from the original digest words. |
| [Lanes.v](Lanes.v) | Check that each point occupies twenty eight-lane vector rows in X, Y, Z, T order and that chunk zero uses the low mask byte. |

The [audit builder](build.py) imports linked callee certificates, compares
their retained sources and ELF symbol extents, and compiles the shared Coq
modules in each policy's audit.
