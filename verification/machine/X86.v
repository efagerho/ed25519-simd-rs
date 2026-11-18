From Coq Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition low64 x := Z.land x (Z.ones 64).

(* Unmasked EVEX.512 register forms with 64-bit elements. *)
Definition invbit n k := 1 - (n / 2^k mod 2).
Definition prefix (map pp reg v rm:Z) :=
 [0x62; 128*invbit reg 3 + 64*invbit rm 4 + 32*invbit rm 3 + 16*invbit reg 4 + map;
  0x84 + 8*(15 - v mod 16) + pp; 0x40 + 8*invbit v 4].
Definition modrm mode reg rm := mode*64 + (reg mod 8)*8 + rm mod 8.
Definition rr map pp op (r v m:nat) :=
 let reg:=Z.of_nat r in let rm:=Z.of_nat m in
 prefix map pp reg (Z.of_nat v) rm ++ [op;modrm 3 reg rm].

Definition le32 (n:Z) := map (fun k=>n / 2^k mod 256) [0;8;16;24].
