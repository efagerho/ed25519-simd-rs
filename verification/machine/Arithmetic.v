From Coq Require Import ZArith.
From Machine Require Import X86.
Open Scope Z_scope.

(* VPADDQ — Intel Intrinsics Guide
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_add_epi64 *)
Definition vpaddq a b := low64 (a + b).
Definition encode_vpaddq dst a b := rr 1 1 0xd4 dst a b.

(* VPMULLQ — Intel Intrinsics Guide
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_mullo_epi64 *)
Definition vpmullq a b := low64 (a * b).
Definition encode_vpmullq dst a b := rr 2 1 0x40 dst a b.
