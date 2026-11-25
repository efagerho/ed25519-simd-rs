From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.ByteMemory.
From Curve25519 Require Import Radix51 group.Affine group.Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.FullLadder Require NativeSeed.

Local Open Scope Z_scope.
Local Opaque Seed.code.
Definition input s base j i:=SeedProjection.cell (mem s) base i j.
Lemma buffer_cell m a i j :
 cell (buffer_words m a) i j=SeedProjection.cell m a i j.
Proof. unfold cell,buffer_words,SeedProjection.cell;f_equal;rewrite Nat2Z.inj_add,Nat2Z.inj_mul;ring. Qed.

Lemma cache_of_row f row : (forall i,(i<20)%nat -> f i=row i) ->
 Seed.cache f=scalar_cache false row.
Proof.
 intro H;unfold Seed.cache,scalar_cache,cache_from_fields;f_equal;
 try match goal with |-Some _=Some _ => f_equal end;apply limbs_ext;intros i I;apply H;lia.
Qed.

(* Interpret the twenty stored limbs using the signed table row that supplied
   the three staged fields. The seed also writes a zero T in every lane. *)
Theorem checked pc pad pair ladder pt base s u B A :
 valid_inputs pc pad ladder -> valid_tables ladder B A -> (pair<32)%nat ->
 (forall i j,(i<20)%nat -> (j<8)%nat ->
   input s base j i=table_row ladder j false (weight ladder j pair S.Odd) i) ->
 (forall j i,(j<8)%nat -> (i<20)%nat ->
   SeedProjection.cell (mem u) pt i j=Seed.out (NativeSeed.lane s pt base j) i) ->
 let w:=buffer_words (mem u) pt in loose_xyz w /\
 (forall j,(j<8)%nat -> represents_xyz (point_values w j) (operand_point ladder B A j pair S.Odd)) /\
 forall i j,(i<5)%nat -> (j<8)%nat -> cell w (15+i)%nat j=0.
Proof.
 intros V Tables N Staged R w.
 assert (Bound:forall j,(j<8)%nat -> Seed.bounded (input s base j)).
 { intros j J i I;rewrite Staged by assumption;apply (proj1(Tables j false _ J (valid_weight pc pad ladder pair S.Odd j V N J))) in I;exact I. }
 assert (Row:forall i j,(i<20)%nat -> (j<8)%nat ->
   cell w i j=Seed.out (Seed.execute (input s base j) (NativeSeed.initial s pt j)) i).
 { intros i j I J;unfold w;rewrite buffer_cell;exact (R j i J I). }
 split.
 - intros c j C J;eapply loose_ext;[|apply (Seed.seed_bound _ c (Bound j J))].
   intros i I;symmetry;rewrite Row by lia;apply Seed.routed;assumption.
 - split.
   + intros j J;assert (E:point_values w j=Seed.output_point (input s base j) (NativeSeed.initial s pt j)).
     { unfold point_values,point_from_fields,word_coordinate,field_at,Seed.output_point;f_equal;
       apply limbs_ext;intros i I;apply Row;lia. }
     rewrite E;apply Seed.seed_represents;[apply Bound,J|].
     rewrite (cache_of_row _ _ (fun i I=>Staged i j I J));exact (proj2(Tables j false _ J (valid_weight pc pad ladder pair S.Odd j V N J))).
   + intros i j I J;rewrite Row by lia;apply Seed.zero_t,I.
Qed.
