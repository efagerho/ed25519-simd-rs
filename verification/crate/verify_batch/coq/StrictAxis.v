From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require GZnZ.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.VectorProcedure memory.ByteMemory.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Affine Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Limbs Decode.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require StrictOperands StrictMatchMath ScorePoint.
Local Open Scope Z_scope.

Definition index (vertical:bool):nat:=if vertical then 1 else 0.
Definition axis (vertical:bool):=if vertical then y else x.
Definition matches vertical e j A R:=axis vertical (ScorePoint.product e j A)=axis vertical R.

Lemma memory_coord s b c j i : StrictOperands.limb s b (320*Z.of_nat c) j i=
 DecodedRows.coord (buffer_words (mem s) b) j c i.
Proof.
 unfold StrictOperands.limb,DecodedRows.coord,cell,buffer_words;f_equal;
 repeat first [rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul];ring.
Qed.
Lemma split_coord w j c : cache_bounds false w -> (j<8)%nat -> (c<4)%nat -> split_field(DecodedRows.coord w j c).
Proof. intros B J C i I;specialize (B (5*c+i)%nat j ltac:(change (5*c+i<20)%nat;lia) J);unfold DecodedRows.coord,split;lia. Qed.

Lemma product_value vertical w j P :
 represents_point false (point_values w j) P ->
 let z:=value(DecodedRows.coord w j 2) in
 z<>0%fp /\ value(DecodedRows.coord w j (index vertical))=(axis vertical P*z)%fp.
Proof.
 intros [[NZ [X Y]] _];destruct vertical;split;assumption.
Qed.
Lemma affine_value vertical w j R :
 represents_point true (point_values w j) R -> value(DecodedRows.coord w j 2)=1%fp ->
 value(DecodedRows.coord w j (index vertical))=axis vertical R.
Proof.
 intros [[NZ [X Y]] _] Z;change (value(DecodedRows.coord w j 0)=(x R*value(DecodedRows.coord w j 2))%fp) in X;
 change (value(DecodedRows.coord w j 1)=(y R*value(DecodedRows.coord w j 2))%fp) in Y.
 rewrite Z in X,Y;destruct vertical;cbn [index axis];[rewrite Y|rewrite X];ring.
Qed.

Theorem checked vertical e s t j A R : (j<8)%nat -> HashLayout.eligible Dalek e j ->
 decodes (little_endian(key_bytes(HashLayout.row e j))) A ->
 decodes (BatchDecode.original_encoding true e j) R ->
 ScorePoint.points Dalek e s -> StrictOperands.inputs vertical e s t ->
 StrictMatchMath.constants (vectors s j) -> StrictMatchMath.constants (vectors t j) ->
 (high_test (Instructions.run no_read StrictMatchMath.suffix (vectors t j)) 0=true <-> matches vertical e j A R).
Proof.
 intros J On DA DR [QB QV [RB [_ RV]]] In C T.
 set (q:=ScorePoint.accumulator e s) in *;set (r:=DecodedRows.buffer true e s) in *;set(k:=index vertical).
 assert (Off:StrictOperands.off vertical=320*Z.of_nat k) by (destruct vertical;reflexivity).
 assert (K:(k<4)%nat) by (destruct vertical;unfold k,index;lia).
 assert (Inputs:StrictMatchMath.prepared (vectors t j) (DecodedRows.coord r j k) (DecodedRows.coord q j 2) (DecodedRows.coord q j k)).
 { intros i I;destruct(In j i J I) as [L [Z S]];rewrite L,Z,S,Off;change 640 with (320*Z.of_nat 2);rewrite !memory_coord.
   split;[reflexivity|split;[reflexivity|f_equal;destruct (Nat.eqb i 0);[exact (C 2%nat ltac:(lia))|exact(C 3%nat ltac:(lia))]]]. }
 rewrite (StrictMatchMath.match_coord _ _ _ _ Inputs T (split_coord _ _ _ RB J K)
     (split_coord q j 2%nat (strict_split _ QB) J ltac:(lia)) (split_coord _ _ _ (strict_split _ QB) J K)).
 destruct(RV j R J DR) as [Rep Z1];pose proof(affine_value vertical _ _ _ Rep Z1) as Ar;fold k in Ar;rewrite Ar.
 destruct(product_value vertical _ _ _ (QV j A J On DA)) as [NZ Eq];fold k in Eq;rewrite Eq.
 set(z:=value(DecodedRows.coord q j 2)) in *;unfold matches;split;[intro E|intros ->;reflexivity].
 replace (axis vertical (ScorePoint.product e j A)) with ((axis vertical (ScorePoint.product e j A)*z)/z)%fp by (field;exact NZ).
 rewrite <-E;field;exact NZ.
Qed.
