From Coq Require Import ZArith List Bool.
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

(* Unmasked full-vector memory forms: base + signed displacement, a 64-byte
   compressed tuple, optional RSP/R12 SIB, and explicit zero for RBP/R13. *)
Definition rm_memory (map pp op : Z) (r v : nat) (base disp : Z) :=
  let reg := Z.of_nat r in
  let rm := base mod 8 in
  let scaled := disp / 64 in
  let '(mode, displacement) :=
    if (disp =? 0) && negb (rm =? 5) then (0, [])
    else if (disp mod 64 =? 0) && (-128 <=? scaled) && (scaled <? 128)
         then (1, [scaled mod 256])
         else (2, le32 disp) in
  prefix map pp reg (Z.of_nat v) base ++ [op; modrm mode reg rm]
  ++ (if rm =? 4 then [0x24] else []) ++ displacement.
