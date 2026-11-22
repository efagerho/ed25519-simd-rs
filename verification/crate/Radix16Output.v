From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Packed execution.LinkedCalls memory.FlatMemory isa.Shift.
From Curve25519 Require Import SignedRadix16.
Import ListNotations. Local Open Scope nat_scope.
Definition expand w e o := [ShiftQ false 7 w 4; And 7 7 5; And w w 5;
 Sub 7 7 6; Sub w w 6; Unpack false e w 7; Unpack true o w 7].
Definition pair a b c d imm lane := [Shuffle 0 a b imm; Shuffle 1 c d imm;
 Shuffle 2 0 1 0x88; Shuffle 3 0 1 0xdd; Store lane 2; Store (lane+2) 3].
Definition write_digits := [Imm false 15%Z; Broadcast true 5; Imm false 8%Z; Broadcast true 6] ++
 expand 0 8 9 ++ expand 1 10 11 ++ expand 2 12 13 ++ expand 3 14 15 ++
 pair 8 10 12 14 0x44 0 ++ pair 9 11 13 15 0x44 1 ++
 pair 8 10 12 14 0xee 4 ++ pair 9 11 13 15 0xee 5.

Local Open Scope Z_scope.
Definition chunk x i := (x/2^(64*Z.of_nat i)) mod 2^64.
Definition digit_expr (words:nat->nat->expr) lane k :=
 let w:=words (k/16)%nat lane in
 let bits:=if Nat.even k then w else RightQ w 4 in
 SubB (AndB (Octet bits (k mod 16 / 2)%nat) (Octet (Lit 15) 0)) (Octet (Lit 8) 0).
(* Taking a lower nibble commutes with dropping a multiple of sixteen
   after division, including at the boundary of a packed qword. *)
Local Lemma slice_mod x d m t : 0<d -> 0<m -> 0<t ->
 ((x mod (d*(m*t)))/d) mod m = (x/d) mod m.
Proof.
 intros D M T; set (p:=d*(m*t));pose proof(Z.div_mod x p ltac:(unfold p;nia)) as E.
 replace (x/d) with (x mod p/d+(x/p*t)*m).
 - now rewrite Z.mod_add by lia.
 - transitivity ((x mod p+((x/p)*(m*t))*d)/d).
   + rewrite Z.div_add by lia;ring.
   + f_equal;unfold p in *;nia.
Qed.
Local Lemma byte_nibble x k :
 Z.land (word_byte x k) 15 = (x/2^(8*k)) mod 16.
Proof.
 unfold word_byte; change 15 with (Z.ones 4); rewrite Z.land_ones by lia.
 change (2^4) with 16.
 set (a:=x/2^(8*k)); pose proof(slice_mod a 1 16 16 ltac:(lia) ltac:(lia) ltac:(lia)) as H.
 now rewrite !Z.div_1_r in H.
Qed.
Lemma routed_digit s (w:nat->nat->expr) x j k :
 (k<64)%nat -> (forall i,(i<4)%nat -> value s (w i j)=chunk (x+bias 64) i) ->
 value s (digit_expr w j k) = digit x k mod 256.
Proof.
 intros K Words. unfold digit_expr. set (i:=(k/16)%nat). set (r:=(k mod 16)%nat).
 assert (I:(i<4)%nat) by (unfold i;pose proof(Nat.div_mod k 16 ltac:(lia));lia).
 assert (R:(r<16)%nat) by (unfold r;apply Nat.mod_upper_bound;lia).
 assert (Split:k=(16*i+r)%nat) by (unfold i,r;apply Nat.div_mod;lia).
 assert (Even:Nat.even k=Nat.even r).
 { rewrite Split,Nat.even_add,Nat.even_mul;change (Bool.eqb true (Nat.even r)=Nat.even r); destruct (Nat.even r);reflexivity. }
 rewrite Even. unfold digit,nibble.
 pose proof (Words i I) as W.
 cbn [value];change (word_byte 15 0) with 15;change (word_byte 8 0) with 8.
 rewrite byte_nibble.
 assert (N: forall d, 0<=d<16 ->
     (chunk (x+bias 64) i /16^d) mod 16 = ((x+bias 64)/16^(16*Z.of_nat i+d)) mod 16).
 { intros d D. unfold chunk.
   replace (2^(64*Z.of_nat i)) with (16^(16*Z.of_nat i)) by
     (change 16 with (2^4) at 1; rewrite <- Z.pow_mul_r by lia; f_equal;ring).
   replace (2^64) with (16^d*(16*16^(15-d))) by
     (replace 16 with (16^1) at 2 by reflexivity; rewrite <- !Z.pow_add_r by lia;
      replace (d+(1+(15-d))) with 16 by ring; reflexivity).
   rewrite slice_mod by (try apply Z.pow_pos_nonneg;lia).
   rewrite Z.div_div, <-Z.pow_add_r by (try apply Z.pow_nonzero;try apply Z.pow_pos_nonneg;lia).
   reflexivity. }
 assert (KZ:Z.of_nat k=16*Z.of_nat i+Z.of_nat r) by lia.
 rewrite KZ.
 destruct (Nat.even r) eqn:E.
 - rewrite W. replace (2^(8*Z.of_nat (r/2))) with (16^Z.of_nat r).
   + now rewrite N by lia.
   + change 16 with (2^4);rewrite <- Z.pow_mul_r by lia; f_equal.
     clearbody r; do 16 (destruct r as [|r]; [vm_compute in E |- *; congruence|]); lia.
 - change (value s (RightQ (w i j) 4)) with (vpsrlq (value s (w i j)) 4).
   rewrite W;unfold vpsrlq;rewrite Z.shiftr_div_pow2 by lia.
   rewrite Z.div_div by (try apply Z.pow_nonzero;try apply Z.pow_pos_nonneg;lia).
   replace (2^Z.of_nat 4*2^(8*Z.of_nat (r/2))) with (16^Z.of_nat r).
   + now rewrite N by lia.
   + change 16 with (2^4); rewrite <-Z.pow_mul_r, <-Z.pow_add_r by lia; f_equal.
     clearbody r; do 16 (destruct r as [|r]; [vm_compute in E |- *; congruence|]); lia.
Qed.

Definition output_state := fold_left step write_digits initial.
Definition byte_check j k := match stores output_state j with
 | Some v=>expr_beq (byte v k) (digit_expr Initial j k) | None=>false end.
Lemma output_routed j k : (j<8)%nat -> (k<64)%nat ->
 exists v, stores output_state j=Some v /\ byte v k=digit_expr Initial j k.
Proof.
 intros J K. assert (C:forallb (fun l=>forallb (byte_check l) (seq 0 64)) (seq 0 8)=true)
 by (vm_compute;reflexivity).
 apply (proj1 (forallb_forall _ _)) with (x:=j) in C;[|apply in_seq;lia].
 apply (proj1 (forallb_forall _ _)) with (x:=k) in C;[|apply in_seq;lia].
 unfold byte_check in C;destruct (stores output_state j) as [v|];[|discriminate].
 exists v;split;[reflexivity|now apply internal_expr_dec_bl].
Qed.
