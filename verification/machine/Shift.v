From Coq Require Import ZArith List.
From Machine Require Import X86.
Import ListNotations.
Open Scope Z_scope.

(* VPSLLQ — Intel Intrinsics Guide
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_slli_epi64 *)
Definition vpsllq a n := low64 (Z.shiftl a (Z.of_nat n)).
Definition encode_vpsllq dst a n := rr 1 1 0x73 6 dst a ++ [Z.of_nat n].

(* VPSRLQ — Intel Intrinsics Guide
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_srli_epi64 *)
Definition vpsrlq a n := Z.shiftr a (Z.of_nat n).
Definition encode_vpsrlq dst a n := rr 1 1 0x73 2 dst a ++ [Z.of_nat n].
