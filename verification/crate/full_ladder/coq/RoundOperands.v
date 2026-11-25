From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.ByteMemory memory.FlatMemory.
From Curve25519 Require Import Radix51 group.Affine group.Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.FullLadder Require Import Operands.
Local Open Scope Z_scope.

Definition selected s base pair flat:=forall k i j,(i<SA.columns k)%nat -> (j<8)%nat ->
 read_word flat (base+64*Z.of_nat (SA.first_row k+i)+8*Z.of_nat j)=table_row s j (affine k) (weight s j pair k) i.
Definition cache flat base k:=buffer_words flat (base+64*Z.of_nat(SA.first_row k)).

Lemma stable s base pair before after : selected s base pair before ->
 preserved (fun x=>base<=x<base+3520) before after -> selected s base pair after.
Proof.
 intros S F k i j I J;rewrite <-(S k i j I J);apply (preserved_read 8 _ _ _ _ F).
 intros n N;change (0<=n<8) in N;rewrite Nat2Z.inj_add;destruct k;cbn [SA.first_row SA.columns] in *;lia.
Qed.
Lemma cell_selected s base pair flat k i j : selected s base pair flat -> (i<SA.columns k)%nat -> (j<8)%nat ->
 cell (cache flat base k) i j=table_row s j (affine k) (weight s j pair k) i.
Proof.
 intros S I J;rewrite <-(S k i j I J);unfold cell,cache,buffer_words;f_equal;rewrite !Nat2Z.inj_add,Nat2Z.inj_mul;ring.
Qed.
Theorem checked pc pad s base pair flat k B A : valid_inputs pc pad s -> valid_tables s B A -> (pair<32)%nat ->
 selected s base pair flat -> let a:=cache flat base k in cache_bounds (affine k) a /\
 forall j,(j<8)%nat -> represents_cache (cache_values (affine k) a j) (operand_point s B A j pair k).
Proof.
 intros V T N S a;apply from_selected_words;[exact T|intros;apply (valid_weight pc pad);assumption|].
 intros;apply (cell_selected _ _ _ _ _ _ _ S);assumption.
Qed.
