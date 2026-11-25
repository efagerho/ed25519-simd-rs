From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory.
From Curve25519 Require Import Edwards Radix51.
From Curve25519.group Require Import PrimeField Affine Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Limbs Decode.
From Ed25519Simd.VerifyBatch Require Import Policy BatchDecode NativeScale RootValue.
From Ed25519Simd.VerifyBatch Require ReturnedPoint.
Local Open Scope Z_scope.
Local Opaque Power.apply_kernel DecoderProduct.kernel.

Definition buffer sig e s:=buffer_words (mem s) (BatchDecode.point e sig).
Definition coord w j c i:=cell w (5*c+i)%nat j.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition encoded_y sig e (w:nat->Z) := forall j,(j<8)%nat ->
 let y:=coord w j 1 in BatchDecode.radix_digits y /\ limbs y=original_encoding sig e j mod 2^255.
Definition geometry sig e (w:nat->Z):=cache_bounds false w /\ encoded_y sig e w /\ forall j P,(j<8)%nat ->
 Policy.decodes (original_encoding sig e j) P ->
 represents_point true (point_values w j) P /\ value(coord w j 2)=1%fp.

Lemma memory_coord sig e s c j i : coord (buffer sig e s) j c i=
 row s (BatchDecode.point e sig+320*Z.of_nat c) j i.
Proof.
 unfold coord,cell,buffer,buffer_words,row;f_equal;repeat first [rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul];ring.
Qed.
Lemma keep sig e s t : preserved (Return.span (BatchDecode.point e sig) 1280) (mem s) (mem t) ->
 geometry sig e (buffer sig e s) -> geometry sig e (buffer sig e t).
Proof.
 intros M [B [Raw P]];assert (Eq:forall k,(k<160)%nat -> buffer sig e t k=buffer sig e s k).
 { intros k K;apply preserved_read with (outside:=Return.span (BatchDecode.point e sig) 1280);[exact M|].
   intros i I;change (0<=i<8) in I;unfold Return.span;lia. }
 split;[intros i j I J;unfold cell;change (i<20)%nat in I;rewrite Eq by lia;apply B;assumption|].
 split.
 { intros j J;destruct(Raw j J) as [T Val];cbv zeta.
   assert (Y:same (coord (buffer sig e t) j 1) (coord (buffer sig e s) j 1)) by
    (intros i I;unfold coord,cell;apply Eq;lia).
   split;[intros i I;rewrite Y by exact I;apply T,I|rewrite <-Val;apply limbs_ext,Y]. }
 intros j G J R;destruct(P j G J R) as [Rep Z1];split;[now rewrite(point_values_ext _ _ _ Eq J)|].
 rewrite <-Z1;apply same_value;intros i I;unfold coord,cell;apply Eq;lia.
Qed.

Theorem returned sig pol bias e s q : ReturnedPoint.result sig pol bias e s q ->
 (forall j,(j<8)%nat ->
 let x0:=vectors(machine s) j in let y0:=row (machine s) (BatchDecode.point e sig+320) j in
 split_field x0 /\ BatchDecode.radix_digits y0 /\ limbs y0=original_encoding sig e j mod 2^255 /\
 forall P,Policy.decodes (original_encoding sig e j) P -> value x0=x P) ->
 geometry sig e (buffer sig e (machine q)).
Proof.
 intros Out Inputs;destruct(ReturnedPoint.point_before_return _ _ _ _ _ _ Out) as [a [A M]].
 set (w:=buffer sig e (machine q)).
 assert (Lane:forall j,(j<8)%nat -> let X:=vectors(machine s) j in let Y:=row (machine s) (BatchDecode.point e sig+320) j in
  same (coord w j 0) X /\ same (coord w j 1) Y /\ same (coord w j 2) one /\ same (coord w j 3) (mul DecoderProduct.kernel X Y)).
 { intros j J;cbv zeta;unfold w;repeat split;intros i I;rewrite memory_coord.
   all: unfold row at 1;rewrite M.
   all: pose proof(ExtendedPoint.point_rows _ _ _ _ _ _ A j i J I) as [X [Y [Z T]]].
   - change (320*Z.of_nat 0) with 0;rewrite Z.add_0_r;exact X.
   - exact Y.
   - exact Z.
   - exact T. }
 assert (One:split_field one) by (intros [|[|[|[|[|i]]]]] I;vm_compute;easy).
 split.
 - intros i j I J;change (i<20)%nat in I;destruct (Inputs j J) as [BX [BY _]];destruct(Lane j J) as [X [Y [Z T]]].
   assert (Bound:forall c,(c<4)%nat -> split_field(coord w j c)).
   { intros [|[|[|[|c]]]] C;try lia;[exact(same_split _ _ X BX)|exact(same_split _ _ Y (digits_split _ BY))|exact(same_split _ _ Z One)|].
     apply(same_split _ _ T),bounded_split,(proj1(mul_ok _ _ _ (proj1 DecoderProduct.multiplication) BX (digits_split _ BY))). }
   pose proof(Nat.div_mod i 5 ltac:(lia)) as D;pose proof(Nat.mod_upper_bound i 5 ltac:(lia)) as R.
   specialize(Bound (i/5)%nat ltac:(lia) (i mod 5)%nat R);unfold coord in Bound;rewrite <-D in Bound;unfold Radix51.split in Bound;lia.
 - split.
   { intros j J;destruct(Inputs j J) as [_ [Bound [Val _]]];destruct(Lane j J) as [_ [Y _]].
     split;[intros i I;rewrite Y by exact I;apply Bound,I|rewrite <-Val;apply limbs_ext,Y]. }
   intros j P J In;destruct (Inputs j J) as [BX [BY [YVal XVal]]];destruct (Lane j J) as [X [Y [Z T]]].
   assert (YP:fy(original_encoding sig e j)=y P) by exact (eq_sym(proj1 In)).
   pose proof(same_value _ _ X) as VX;rewrite (XVal P In) in VX.
   assert (YField:value(row (machine s) (point e sig+320) j)=fy(original_encoding sig e j))
     by (unfold value,pack;now rewrite YVal).
   pose proof(same_value _ _ Y) as VY;rewrite YField,YP in VY.
   pose proof(same_value _ _ Z) as VZ;change (value one) with 1%fp in VZ.
   pose proof(same_value _ _ T) as VT;destruct(mul_ok _ _ _ (proj1 DecoderProduct.multiplication) BX (digits_split _ BY)) as [_ [_ Product]].
   rewrite Product,(XVal P In),YField,YP in VT.
   split;[|exact VZ];change ((value(coord w j 2)<>0%fp /\ value(coord w j 0)=(x P*value(coord w j 2))%fp /\
    value(coord w j 1)=(y P*value(coord w j 2))%fp) /\ (true=true -> value(coord w j 3)=(x P*y P*value(coord w j 2))%fp)).
   assert (unit:forall z:fp,z=(z*value(coord w j 2))%fp) by (intro z;rewrite VZ;ring).
   split.
   + split.
     * rewrite VZ;discriminate.
     * split.
       -- exact (eq_trans VX (unit (x P))).
       -- exact (eq_trans VY (unit (y P))).
   + intros _;exact (eq_trans VT (unit (x P*y P)%fp)).
Qed.
End Iteration.
