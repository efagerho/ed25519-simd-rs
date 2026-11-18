From Coq Require Import ZArith.
From Machine Require Import X86.
Open Scope Z_scope.

(* VPXORQ — Intel Intrinsics Guide
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_xor_epi64 *)
Definition vpxorq := Z.lxor.
Definition encode_vpxorq dst a b := rr 1 1 0xef dst a b.

(* VPANDQ — Intel Intrinsics Guide
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_and_epi64 *)
Definition vpandq := Z.land.
Definition encode_vpandq dst a b := rr 1 1 0xdb dst a b.
