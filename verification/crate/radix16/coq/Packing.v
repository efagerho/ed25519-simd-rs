From Curve25519 Require Import SignedRadix16.
From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Arithmetic isa.Shift isa.X86 execution.Packed execution.LinkedCalls memory.ByteMemory.
From Ed25519Simd Require Import Radix16Output.
From Ed25519Simd.Scalar Require Import ScalarSpec.
Local Open Scope Z_scope.

Definition biased i j := Add (Lit 0x8888888888888) (Load i j).
Fixpoint carried i j := match i with O=>biased 0 j | S k=> Add (biased i j) (RightQ (carried k j) 52) end.
Definition packed i j :=
 let lo:=carried i j in
 Add (if Nat.eqb i 0 then lo else RightQ lo (12*i))
     (LeftQ (biased (S i) j) (52-12*i)).
Definition limb_words s := buffer_words (mem s) (regs s 7%nat).

Local Lemma small_add a b : 0<=a+b<2^64 -> vpaddq a b=a+b.
Proof. unfold vpaddq,low64. rewrite Z.land_ones by lia. apply Z.mod_small. Qed.
Local Lemma pack_add a b shift :
 vpaddq a (vpsllq b shift) = (a + b*2^Z.of_nat shift) mod 2^64.
Proof. unfold vpaddq,vpsllq,low64. rewrite !Z.land_ones, Z.shiftl_mul_pow2,
 Z.add_mod_idemp_r by lia. reflexivity. Qed.

Ltac four i := destruct i as [|[|[|[|i]]]]; try lia.
Local Definition radix a b := a+2^52*b.
Local Lemma drop_limb a b c : radix a (radix b c)/2^52 = radix (b+a/2^52) c.
Proof. unfold radix. rewrite (Z.mul_comm (2^52)), Z.div_add by lia. ring. Qed.
Local Lemma window a b c d f g : 0<d -> f*d=2^52 -> 2^52*f=g*2^64 ->
 (radix a (radix b c)/d) mod 2^64 = (a/d+b*f) mod 2^64.
Proof.
 intros D F G; unfold radix.
 replace (a+2^52*(b+2^52*c)) with (a+(b*f+c*(g*2^64))*d) by (rewrite <-G; replace (a+(b*f+c*(2^52*f))*d) with (a+(b+c*2^52)*(f*d)) by ring; rewrite F;ring).
 rewrite Z.div_add by lia.
 replace (a/d+(b*f+c*(g*2^64))) with ((a/d+b*f)+(c*g)*2^64) by ring.
 now rewrite Z.mod_add by lia.
Qed.
Local Lemma drop_bias x i : (i<4)%nat ->
 chunk (x + bias 65) i = chunk (x + bias 64) i.
Proof.
 intro I; unfold chunk; four i;
 match goal with |- ((_ / ?d) mod _) = _ =>
 let m:=eval vm_compute in (2^256/d) in
 replace (x + bias 65) with (x+bias 64+(8*m)*d) by
   (replace (x+bias 64+8*m*d) with (x+(bias 64+8*m*d)) by ring;reflexivity);
 rewrite Z.div_add by (vm_compute;discriminate);
 let k:=eval vm_compute in (8*m/2^64) in change (8*m) with (k*2^64);
 apply Z.mod_add;lia end.
Qed.

Local Lemma pack_expr s a b n : value s (Add a (LeftQ b n)) =
 (value s a+value s b*2^Z.of_nat n) mod 2^64.
Proof. apply pack_add. Qed.

Local Lemma right_value s v k : value s (RightQ v k) = value s v / 2^Z.of_nat k.
Proof. apply Z.shiftr_div_pow2;lia. Qed.

Local Lemma carry_bound x : 0<=x<2^53 -> 0<=x/2^52<2.
Proof. intros;split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia. Qed.

Lemma packed_word s j i : (i<4)%nat ->
 (forall k,(k<5)%nat -> 0<=limb_words s (8*k+j)%nat<B) ->
 value s (packed i j)=chunk (lane_output (limb_words s) j+bias 64) i.
Proof.
 intros I Bound.
 set (b:=fun k=>0x8888888888888+limb_words s (8*k+j)%nat).
 assert (H:forall k,(k<5)%nat -> value s (biased k j)=b k).
 { intros k K; apply small_add. specialize(Bound k K); unfold B,limb_words in *;lia. }
 assert (C:forall k,(k<5)%nat -> 0<=value s (carried k j)<2^53).
 { induction k; intro K.
   - change (0<=value s (biased 0 j)<2^53). rewrite H by lia; unfold b;
     specialize(Bound 0%nat ltac:(lia));unfold B in *;lia.
   - change (0<=vpaddq (value s (biased (S k) j)) (vpsrlq (value s (carried k j)) 52)<2^53).
     rewrite H by lia;unfold b,vpsrlq;rewrite Z.shiftr_div_pow2 by lia.
     specialize(IHk ltac:(lia)); apply carry_bound in IHk;specialize(Bound (S k) K);unfold B in *;
     change (Z.of_nat 52) with 52;rewrite small_add by lia;lia. }
 assert (Succ:forall k,(S k<5)%nat -> value s (carried (S k) j)=
   b (S k)+value s (carried k j)/2^52).
 { intros k K; change (vpaddq (value s (biased (S k) j)) (vpsrlq (value s (carried k j)) 52)=b (S k)+value s (carried k j)/2^52).
   rewrite H by lia;unfold vpsrlq;rewrite Z.shiftr_div_pow2 by lia.
   change (Z.of_nat 52) with 52;apply small_add. specialize(C k ltac:(lia)); apply carry_bound in C;
   specialize(Bound (S k) K);unfold B,b in *;lia. }
 rewrite <-drop_bias by exact I.
 replace (lane_output (limb_words s) j + bias 65) with
   (radix (b 0%nat) (radix (b 1%nat) (radix (b 2%nat) (radix (b 3%nat) (radix (b 4%nat) 0))))).
 2:{ unfold b,radix. change (bias 65) with 0x88888888888888888888888888888888888888888888888888888888888888888.
     unfold lane_output. cbn [Radix.number List.map seq];unfold B;ring. }
 (* Drop 0..3 complete limbs, then take the 64-bit window that starts
    0, 12, 24 or 36 bits into the next limb. *)
 four i; unfold packed,chunk; rewrite pack_expr; cbn [Nat.eqb]; try rewrite right_value.
 1: change (2^(64*Z.of_nat 0)) with (2^0);
   rewrite (window _ _ _ (2^0) (2^52) (2^40)) by (first [reflexivity|lia]);
   rewrite Z.div_1_r.
 2: change (2^(64*Z.of_nat 1)) with (2^52*2^12);
   rewrite <-Z.div_div, drop_limb by lia;
   rewrite (window _ _ _ (2^12) (2^40) (2^28)) by (first [reflexivity|lia]).
 3: change (2^(64*Z.of_nat 2)) with (2^52*(2^52*2^24));
   do 2 (rewrite <-Z.div_div, drop_limb by lia);
   rewrite (window _ _ _ (2^24) (2^28) (2^16)) by (first [reflexivity|lia]).
 4: change (2^(64*Z.of_nat 3)) with (2^52*(2^52*(2^52*2^36)));
   do 3 (rewrite <-Z.div_div, drop_limb by lia);
   rewrite (window _ _ _ (2^36) (2^16) (2^4)) by (first [reflexivity|lia]).
 all: rewrite !H by lia; repeat rewrite Succ by lia;
      change (value s (carried 0 j)) with (value s (biased 0 j)); rewrite H by lia;reflexivity.
Qed.
