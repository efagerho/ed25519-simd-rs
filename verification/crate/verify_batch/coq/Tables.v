(* Check the immutable Rust tables once, directly from the linked words.
   Advance one Edwards addition per row, starting at the lowest signed digit. *)
From Coq Require Import List ZArith Bool Lia.
From Coqprime.elliptic Require GZnZ.
From Machine Require Import execution.LinkedCalls memory.ByteMemory.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import Edwards.
From Curve25519.group Require Import PrimeField Affine Representation SignedMultiple.
From Ed25519Simd.VerifyBatch Require Import Policy Candidate BaseTable IdentityTable.
Import ListNotations. Local Open Scope Z_scope.

Definition width (aff:bool) := if aff then 15%nat else 20%nat.
Definition radius (aff:bool) := if aff then 136 else 8.
Definition equal_fp (a b:fp) := Z.eqb (GZnZ.val Field.prime a) (GZnZ.val Field.prime b).
Lemma equal_fp_sound a b : equal_fp a b=true -> a=b.
Proof. destruct a,b;unfold equal_fp;intros H;apply GZnZ.zirr,Z.eqb_eq,H. Qed.

Definition row_ok aff (row:list Z) P :=
 let q:=scalar_cache aff (fun i=>nth i row 0) in
 (Nat.eqb (length row) (width aff) &&
 forallb (fun w=>(0<=?w)&&(w<?2^52)) row &&
 equal_fp (residue (y_minus_x q)) (y P-x P)%fp &&
 equal_fp (residue (y_plus_x q)) (y P+x P)%fp &&
 equal_fp (residue (t2d q)) ((1+1)*PrimeField.d*x P*y P)%fp &&
 match doubled_z q with None=>true | Some z=>equal_fp (residue z) (1+1)%fp end)%bool.

Lemma row_sound aff row P : row_ok aff row P=true ->
 let f i:=nth i row 0 in
 (forall i,(i<width aff)%nat -> 0<=f i<2^52) /\ represents_cache (scalar_cache aff f) P.
Proof.
 intros H f. unfold row_ok in H;cbv zeta in H;fold f in H. repeat rewrite andb_true_iff in H.
 destruct H as [[[[[Len Bound] Minus] Plus] Product] Zed].
 apply Nat.eqb_eq in Len;split.
 - intros i I. apply forallb_forall with (x:=f i) in Bound;[|apply nth_In;lia].
   apply andb_true_iff in Bound as [Lo Hi];split;[apply Z.leb_le|apply Z.ltb_lt];assumption.
 - apply equal_fp_sound in Minus,Plus,Product. exists 1%fp.
   split;[discriminate|]. split;[rewrite Minus;ring|]. split;[rewrite Plus;ring|].
   split;[rewrite Product;ring|]. destruct aff;[reflexivity|].
   apply equal_fp_sound in Zed.
   transitivity (1+1)%fp;[exact Zed|ring].
Qed.

Fixpoint checked aff P current rows := match rows with
 | []=>true | r::rs=>row_ok aff r current && checked aff P (plus P current) rs end.
Lemma checked_nth aff P rows : forall d i, checked aff P (scale d P) rows=true ->
 (i<length rows)%nat -> row_ok aff (nth i rows []) (scale (d+Z.of_nat i) P)=true.
Proof.
 induction rows as [|r rs IH];intros d [|i] H I;cbn in I;try lia.
 - apply andb_true_iff in H as [R _]. now rewrite Z.add_0_r.
 - apply andb_true_iff in H as [_ H]. rewrite <-scale_succ in H.
   replace (d+Z.of_nat (S i)) with (Z.succ d+Z.of_nat i) by lia.
   exact (IH _ i H ltac:(lia)).
Qed.

Definition contents aff P rows :=
 Z.of_nat(length rows)=2*radius aff+1 /\ checked aff P (scale (-radius aff) P) rows=true.
Definition mapped_table e bias r pc aff rows :=
 regs e r=bias+pc /\ forall d, FullLadder.Operands.legal_index aff d ->
 forall i,(i<width aff)%nat ->
 read_word (mem e) (regs e r+(if aff then 120*(136+d) else 160*(8+d))+8*Z.of_nat i)=
 nth i (nth (Z.to_nat(radius aff+d)) rows []) 0.
Definition mapped e bias :=
 mapped_table e bias 9 BaseTable.address true BaseTable.rows /\
 mapped_table e bias 8 IdentityTable.address false IdentityTable.rows.

Lemma loaded_table e bias r pc aff P rows : contents aff P rows -> mapped_table e bias r pc aff rows ->
 static_table e (regs e r) aff P.
Proof.
 intros [N Checked] [_ M] d D. set (k:=Z.to_nat(radius aff+d)).
 assert (B:(k<length rows)%nat /\ Z.of_nat k=radius aff+d).
 { unfold k,FullLadder.Operands.legal_index,radius in *;destruct aff;split;lia. }
 pose proof (checked_nth aff P rows (-radius aff) k Checked (proj1 B)) as C.
 replace (-radius aff+Z.of_nat k) with d in C by lia.
 destruct (row_sound _ _ _ C) as [Bound Reps].
 cbv zeta;set (f:=fun i=>read_word _ _) in *.
 assert (Eq:forall i,(i<width aff)%nat -> f i=nth i (nth k rows []) 0) by (apply M,D).
 split;[intros;rewrite Eq;apply Bound || assumption;assumption|].
 erewrite row_ext;[exact Reps|exact Eq].
Qed.

Definition verified := contents true generator BaseTable.rows /\ contents false identity IdentityTable.rows.
Lemma loaded e bias : verified -> mapped e bias -> constants e.
Proof.
 intros [Base Id] [B I];split.
 - eapply loaded_table;[exact Base|exact B].
 - eapply loaded_table;[exact Id|exact I].
Qed.
