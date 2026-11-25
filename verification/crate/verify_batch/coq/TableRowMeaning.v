From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls memory.ByteMemory.
From Curve25519 Require Import Radix51.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Kernels Power Decode.
From Ed25519Simd.KeyTable Require Fields Rows Pack.
From Ed25519Simd.VerifyBatch Require TableSignedWords.
Local Open Scope Z_scope.

Definition point e s:=buffer_words (mem s) (TableEntry.point e).
Definition stored e digit sign s j i:=read_word (mem s) (TablePackRows.row e digit sign (Z.of_nat j)+8*Z.of_nat i).
Lemma kernels:Rows.kernels_ok DecoderProduct.kernel.
Proof. split;[vm_compute;reflexivity|destruct op;vm_compute;reflexivity]. Qed.

Lemma coordinate e s j c i : TableColumn.coord e s j c i=Rows.coord (point e s) j c i.
Proof.
 unfold TableColumn.coord,Rows.coord,point,cell,buffer_words;f_equal;repeat first [rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul];ring.
Qed.

Lemma as_field op e s j i :
 Fields.compute DecoderProduct.kernel (TableColumn.coord e s j) op i=
 Fields.compute DecoderProduct.kernel (Rows.coord (point e s) j) op i.
Proof.
 destruct op;unfold Fields.compute;cbn [Fields.linear_op];unfold Decode.mul,Power.apply_kernel,Fields.linear_result;
   apply Instructions.run_ext;[reflexivity| |reflexivity| |reflexivity| |reflexivity|].
 all: intros k;unfold Power.feed;destruct(Kernels.constant k);[reflexivity|];
   destruct (k<?5)%nat;[apply coordinate|];destruct(k<?10)%nat;apply coordinate || reflexivity.
Qed.
Local Opaque Power.apply_kernel Fields.linear_result.
Lemma column e s j i : (i<20)%nat ->
 TablePackedInputs.column e s j i=Rows.column DecoderProduct.kernel (point e s) j i.
Proof.
 intro N;unfold Rows.column,Rows.fields,TablePackedInputs.column,TableColumn.value.
 unfold TableProduct.two_dt,TableProduct.field;change (TableOperands.inputs (TableEntry.point e) s j) with (TableColumn.coord e s j 3).
 rewrite <-as_field. do 20 (destruct i as [|i];[reflexivity|]);lia.
Qed.
Lemma as_row e d sign s t j i :
 TableSignedWords.signed e d (TablePackedInputs.column e s) t -> (j<8)%nat -> (i<20)%nat ->
 stored e d sign t j i=Rows.row DecoderProduct.kernel (point e s) sign j i.
Proof.
 intros S J I;unfold stored;rewrite S by assumption;unfold Rows.row,Pack.signed_word.
 destruct sign;[apply column,I|];destruct (Nat.ltb_spec i 5);[apply column;lia|];
 destruct(Nat.ltb_spec i 10);[apply column;lia|];destruct(Nat.ltb_spec i 15);cbn [Rows.eval];rewrite column by lia;reflexivity.
Qed.

Theorem represents e d sign s t j :
 TableSignedWords.signed e d (TablePackedInputs.column e s) t -> cache_bounds false (point e s) -> (j<8)%nat ->
 let row:=stored e d sign t j in
 (forall i,(i<20)%nat -> 0<=row i<2^52) /\ forall P, represents_point true (point_values (point e s) j) P ->
 represents_cache (scalar_cache false row) (if sign then P else negative P).
Proof.
 intros S B J row;assert (E:forall i,(i<20)%nat -> row i=Rows.row DecoderProduct.kernel (point e s) sign j i)
   by (intros i N;apply as_row;assumption).
 split;[intros i N;rewrite E by exact N;apply Rows.row_bounds;auto using kernels|].
 intros P R;pose proof(Rows.row_rep _ _ j sign P kernels B J R) as Rep.
 replace (scalar_cache false row) with (scalar_cache false (Rows.row DecoderProduct.kernel (point e s) sign j));[exact Rep|].
 unfold scalar_cache,cache_from_fields;f_equal;try match goal with |-Some _=Some _=>f_equal end;apply limbs_ext;intros;symmetry;apply E;lia.
Qed.
