From Coq Require Import ZArith.
From Machine Require Import X86.
Open Scope Z_scope.

(* Both forms add the selected half of the unsigned 52-by-52 product to acc.
   high = false selects VPMADD52LUQ
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_madd52lo_epu64
   high = true selects VPMADD52HUQ
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_madd52hi_epu64 *)
Definition madd52 (high : bool) acc a b :=
  let mask := Z.ones 52 in
  let product := Z.land a mask * Z.land b mask in
  low64 (acc + (if high then Z.shiftr product 52 else Z.land product mask)).

Definition encode_madd52 (high : bool) dst a b :=
  rr 2 1 (if high then 0xb5 else 0xb4) dst a b.

(* Unmasked full-vector memory source: eight qwords, no broadcast. *)
Definition encode_madd52_memory (high : bool) dst a base disp :=
  rm_memory 2 1 (if high then 0xb5 else 0xb4) dst a (Z.of_nat base) disp.
