From Curve25519.group Require Import PointDecoding.
From Coq Require Import ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Affine Decompression.
From Curve25519 Require Import Radix51Digits.
From Ed25519Simd.Decode Require Import Decode.
From Ed25519Simd.VerifyBatch Require Import Policy RootDecision.
From Ed25519Simd.VerifyBatch Require RootCandidate RootAdjusted RootSign.
Local Open Scope Z_scope.
Local Opaque Power.apply_kernel DecoderProduct.kernel.

Definition same (f g:nat->Z):=forall i,(i<5)%nat -> f i=g i.
Lemma same_value f g : same f g -> value f=value g.
Proof. intro E;unfold value,pack;now rewrite (limbs_ext _ _ E). Qed.
Lemma same_bound f g : same f g -> bounded g -> bounded f.
Proof. intros E B i I;rewrite E by exact I;apply B,I. Qed.
Lemma same_split f g : same f g -> split_field g -> split_field f.
Proof. intros E B i I;rewrite E by exact I;apply B,I. Qed.

Lemma selected w (minus:bool) f g : bounded f -> value f=root_candidate w ->
 same g (if minus then mul DecoderProduct.kernel f sqrt_limbs else f) ->
 bounded g /\ value g=corrected_root w minus.
Proof.
 intros B V E;unfold corrected_root;destruct minus;[|split;[exact(same_bound _ _ E B)|now rewrite(same_value _ _ E)]].
 destruct(mul_ok _ _ _ (proj1 DecoderProduct.multiplication) (bounded_split _ B) sqrt_bound) as [Bound [_ Value]].
 split;[exact (same_bound _ _ E Bound)|rewrite(same_value _ _ E),Value,V;reflexivity].
Qed.

Lemma signed s j w out : bounded (vectors s j) -> Z.testbit (regs s 9%nat) (Z.of_nat j)=encoded_sign w ->
 same out (RootSign.adjusted s j) ->
 split_field out /\ value out=signed_root (encoded_sign w) (value(vectors s j)).
Proof.
 intros B Tag E;set (h:=vectors s j) in *;set (flip:=xorb (canonical_odd h) (encoded_sign w)).
 assert (X:same out (if flip then neg_digits h else h)).
 { intros i I;rewrite E,RootSign.sign_math,Tag by assumption;unfold flip;destruct(xorb _ _);reflexivity. }
 pose proof(neg_digits_ok _ B) as [NB Opp];apply congruent_value in Opp;rewrite residue_opp in Opp.
 split;[apply (same_split _ _ X);destruct flip;auto using bounded_split|].
 rewrite(same_value _ _ X);unfold flip,signed_root;rewrite canonical_odd_ok by exact B.
 change (Z.odd (pack h mod prime)) with (parity (value h)).
 destruct(parity(value h)),(encoded_sign w);exact Opp || reflexivity.
Qed.

Theorem registers sig pol bias e valid raw chosen masks out j w :
 RootCandidate.result sig pol bias e valid raw -> RootAdjusted.result pol bias e raw masks chosen out ->
 (j<8)%nat -> let u:=vectors(machine valid) j in let t:=NativeScale.row (machine valid) (regs(machine valid) 6%nat) j in
 split_field u -> value u=numerator(encoded_y w) -> split_field t -> value t=root_power(encoded_y w) ->
 bounded(vectors(machine chosen) j) /\ value(vectors(machine chosen) j)=corrected_root w (masks 4%nat j).
Proof.
 intros Raw Ch J u t U UV T TV;destruct(mul_ok _ u t (proj1 DecoderProduct.multiplication) U T) as [B [_ V]].
 assert (Eq:same (vectors(machine raw) j) (mul DecoderProduct.kernel u t)).
 { intros i I;exact (proj1(RootCandidate.live_x _ _ _ _ _ _ Raw j i J I)). }
 apply (selected w _ (vectors(machine raw) j));[exact (same_bound _ _ Eq B)|rewrite(same_value _ _ Eq),V,UV,TV;reflexivity|].
 intros i I;rewrite (RootAdjusted.root _ _ _ _ _ _ _ Ch j i J I);unfold RootAdjusted.adjusted;destruct(masks 4%nat j);reflexivity.
Qed.
