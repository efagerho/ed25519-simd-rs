From Coq Require Import List ZArith Bool Lia.
From Machine Require Import Blocks Instructions WordBounds.
From Ed25519Simd.Scalar Require Import Program ScalarSpec ScalarMath Product Reduction Montgomery Borrow.
Import ListNotations. Open Scope Z_scope.
Lemma mask_B x : Z.land x(B-1)=x mod B.
Proof. change(Z.land x(Z.ones 52)=x mod 2^52);apply Z.land_ones;lia. Qed.
Definition code := skipn 83(fragment_code scalar_program 7)++
 fragment_code scalar_program 8++fragment_code scalar_program 9++
 fragment_code scalar_program 10++fragment_code scalar_program 11.
(* The equation is checked against the actual subtraction and selection instructions. *)
Lemma output_digits load r : constants_ok r ->forall i,(i<5)%nat ->
 run load code r i=select(r i)(diff r i(borrow_at r i))(borrow_at r 5).
Proof.
 intros Const i I.
 pose proof(Const 26%nat _ eq_refl)as C26;pose proof(Const 27%nat _ eq_refl)as C27;
 pose proof(Const 28%nat _ eq_refl)as C28;pose proof(Const 29%nat _ eq_refl)as C29;
 pose proof(Const 30%nat _ eq_refl)as C30.
 let c:=eval vm_compute in code in change code with c.
 assert(Cases:i=0%nat \/ i=1%nat \/ i=2%nat \/ i=3%nat \/ i=4%nat)by lia.
 destruct Cases as[-> | [-> | [-> | [-> | ->]]]];
 cbv [run bits put fst snd Nat.eqb Logic.vpxorq Logic.vpandq Arithmetic.vpsubq Shift.vpsrlq];
 rewrite ?C26,?C27,?C28,?C29,?C30;
 unfold X86.low64;rewrite !Z.land_ones,!Z.shiftr_div_pow2 by lia;
 change(2^52)with B;change(2^64)with W;
 repeat rewrite subtract_twice;
 cbv [select diff borrow_at borrow modulus_digit];
 rewrite Z.lxor_nilpotent;
 rewrite !mask_B,!mod_word_B,!Z.sub_0_r;reflexivity.
Qed.
Theorem finish_correct load r : constants_ok r ->
 (forall i,(i<5)%nat->0<=r i<B) ->0<=pack r 0<2*L ->
 pack(run load code r)0=pack r 0 mod L /\
 (forall i,(i<5)%nat->0<=run load code r i<B).
Proof.
 intros Const Bounds Range.
 assert(Pack:forall s,pack s 0=low s 5).
 { intro s;rewrite low_pack;unfold pack;f_equal;apply map_ext;intro i;now rewrite Nat.add_0_l. }
 rewrite Pack in Range;destruct(canonical_digits r Bounds Range)as[E D].
 split.
 - rewrite !Pack;rewrite <-E;rewrite !low_pack;f_equal;apply map_ext_in;intros i I;apply in_seq in I;apply output_digits;auto;lia.
 - intros i I;rewrite output_digits by assumption;apply D,I.
Qed.
