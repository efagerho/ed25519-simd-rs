From Curve25519 Require Import SignedRadix16.
From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Packed execution.LinkedCalls memory.FlatMemory isa.Shift.
From Ed25519Simd.Scalar Require Import ScalarSpec.
From Ed25519Simd.Radix16 Require Import Program Packing.
Import ListNotations. Local Open Scope Z_scope.

Definition result_state := fold_left step tail initial.
Definition expected lane k :=
 let w:=packed (k/16)%nat lane in
 let bits:=if Nat.even k then w else RightQ w 4 in
 SubB (AndB (Octet bits (k mod 16 / 2)%nat) (Octet (Lit 15) 0)) (Octet (Lit 8) 0).
Definition check lane k := match stores result_state lane with
 | Some v=>expr_beq (byte v k) (expected lane k) | None=>false end.
Local Lemma checked : forallb (fun j=>forallb (check j) (seq 0 64)) (seq 0 8)=true.
Proof. vm_compute; reflexivity. Qed.
Lemma routed lane k : (lane<8)%nat -> (k<64)%nat ->
 exists v,stores result_state lane=Some v /\ byte v k=expected lane k.
Proof.
 intros L K; pose proof checked as C.
 apply (proj1 (forallb_forall _ _)) with (x:=lane) in C; [|apply in_seq;lia].
 apply (proj1 (forallb_forall _ _)) with (x:=k) in C; [|apply in_seq;lia].
 unfold check in C;destruct(stores result_state lane)as[v|];[|discriminate].
 exists v;split;[reflexivity|now apply internal_expr_dec_bl].
Qed.

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
Lemma expected_digit s j k :
 (k<64)%nat -> (forall i,(i<5)%nat -> 0<=limb_words s (8*i+j)%nat<B) ->
 value s (expected j k) = (digit (lane_output (limb_words s) j) k) mod 256.
Proof.
 intros K Bnd. unfold expected. set (i:=(k/16)%nat). set (r:=(k mod 16)%nat).
 assert (I:(i<4)%nat) by (unfold i;pose proof(Nat.div_mod k 16 ltac:(lia));lia).
 assert (R:(r<16)%nat) by (unfold r;apply Nat.mod_upper_bound;lia).
 assert (Split:k=(16*i+r)%nat) by (unfold i,r;apply Nat.div_mod;lia).
 assert (Even:Nat.even k=Nat.even r).
 { rewrite Split,Nat.even_add,Nat.even_mul;change (Bool.eqb true (Nat.even r)=Nat.even r); destruct (Nat.even r);reflexivity. }
 rewrite Even. set (x:=lane_output (limb_words s) j + bias 64).
 unfold digit,nibble; fold x.
 pose proof (packed_word s j i I Bnd) as W; fold x in W.
 change (value s (packed i j) = chunk x i) in W.
 cbn [value];change (word_byte 15 0) with 15;change (word_byte 8 0) with 8.
 rewrite byte_nibble.
 assert (N: forall d, 0<=d<16 ->
     (chunk x i /16^d) mod 16 = (x/16^(16*Z.of_nat i+d)) mod 16).
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
 - change (value s (RightQ (packed i j) 4)) with (vpsrlq (value s (packed i j)) 4).
   rewrite W;unfold vpsrlq;rewrite Z.shiftr_div_pow2 by lia.
   rewrite Z.div_div by (try apply Z.pow_nonzero;try apply Z.pow_pos_nonneg;lia).
   replace (2^Z.of_nat 4*2^(8*Z.of_nat (r/2))) with (16^Z.of_nat r).
   + now rewrite N by lia.
   + change 16 with (2^4); rewrite <-Z.pow_mul_r, <-Z.pow_add_r by lia; f_equal.
     clearbody r; do 16 (destruct r as [|r]; [vm_compute in E |- *; congruence|]); lia.
Qed.
