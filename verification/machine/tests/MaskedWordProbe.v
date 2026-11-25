From Coq Require Import List ZArith Strings.String.
From Machine Require Import execution.MaskedWords execution.MaskTrace execution.Packed
 isa.Move tests.model.Oracle.
Import ListNotations. Local Open Scope Z_scope.

Definition threshold := 2^63.
Definition prefix := Move.encode_load 0 7 0.
Definition ops target := [Compare BelowU 1 0 0 (Rip target); Union 3 1 1;
 Compare EqualQ 2 0 0 (Rip target); Union 1 1 2;
 Compare EqualQ 2 1 0 (Reg 0); Compare AtLeastU 4 0 0 (Rip target); MoveImm false 1; Splat 1;
 MaskedWords.Add 0 3 0 1; Blend 4 2 1 0; Compare AtLeastU 2 4 0 (Rip target)].
Definition suffix := Packed.encode (Store 0 4) ++ MaskTrace.encoding (KmovEax 2) ++ [0xc3].
Definition middle t := match MaskedWords.assemble (Z.of_nat (List.length prefix)) (ops t) with Some bs=>bs | None=>[] end.
Definition target := Z.of_nat (List.length (prefix++middle 0++suffix)).
Definition bytes := prefix++middle target++suffix++[0;0;0;0;0;0;0;128].
Definition sample seed j := if Z.testbit seed (Z.of_nat j) then threshold else
 if Z.testbit seed (8+Z.of_nat j) then threshold-1 else 2^64-1.
Definition result seed j := fold_left (MaskedWords.step (j<?8)%nat (fun _=>threshold)) (ops target)
 (Lane (fun _=>sample seed j) (fun _=>true) 0).
Definition observe seed := [seed;mask_word 16 (fun j=>Z.b2z(mask (result seed j) 2%nat))]++
 map (fun j=>MaskedWords.zmm (result seed j) 4%nat) (seq 0 8).
Definition seeds := [0;255;0xff00;0x55aa;0x2d93].
Definition report inputs := String.concat "|"%string (numbers bytes::map (fun seed=>numbers(observe seed)) inputs).
