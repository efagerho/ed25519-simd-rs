From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.MaskedWords execution.WordSemantics
 execution.WordBounds memory.ByteMemory memory.MemoryGeometry.
From Curve25519 Require Import Scalar SignedRadix16.
From Ed25519Simd Require Import Radix16Output.
From Ed25519Simd.SignatureScalar Require Import Program Audit Inputs Arithmetic.
Import ListNotations. Local Open Scope Z_scope.

(* Evaluate the actual register schedule over arbitrary incoming vector and
   mask registers. Only the four transposed words and three RIP loads survive. *)
Section Circuit.
Variables (r:nat->Z) (ks:nat->bool) (acc:Z) (rd:Z->Z) (t:Z).
Let ops:=compare_order t++bias_words.
Let start:=Lane r ks acc.
Let compared:=fold_left (step true rd) (compare_order t) start.
Let st:=fold_left (step true rd) ops start.
Let ok:=below (r 8%nat) (r 9%nat) (r 10%nat) (r 11%nat) (rd t) (rd (t+8)) (rd (t+24)).
Local Lemma flag_value : mask compared 1%nat=ok.
Proof.
 unfold ok,below.
 replace 0 with (Z.lxor (r 4%nat) (r 4%nat)) at 1 by apply Z.lxor_nilpotent.
 reflexivity.
Qed.
Lemma circuit_words : mask st 1%nat=ok /\ forall i,(i<4)%nat ->
 zmm st i=if ok then output_word (r 8%nat) (r 9%nat) (r 10%nat) (r 11%nat) i else B.
Proof.
 split;[exact flag_value|].
 intros i I. unfold st,ops;rewrite fold_left_app;fold compared.
 assert (Pack:forall (v:lane) n,(n<4)%nat ->
   zmm (fold_left (step true rd) bias_words v) n=
   if mask v 1%nat then output_word (zmm v 8%nat) (zmm v 9%nat) (zmm v 10%nat) (zmm v 11%nat) n else B)
   by (intros v [|[|[|[|n]]]] N;try lia;reflexivity).
 rewrite Pack,flag_value by assumption;reflexivity.
Qed.
Lemma high_mask_clear : mask (fold_left (step false rd) ops start) 1%nat=false.
Proof. reflexivity. Qed.
End Circuit.

Definition accepted s j := scalar s j <? L.
Definition selected s j := if accepted s j then scalar s j else 0.

Section Run.
Context {entry pc n ro slide} (P:placement entry pc n (slide+ro)) (W:well_formed entry).
Variable incoming:nat->nat->bool.
Let rd t:=read_word (mem entry) (word (slide+t)).
Hypothesis literals: rd ro=l0 /\ rd (ro+8)=l1 /\ rd (ro+24)=l3.
Lemma lane_result j : (j<8)%nat ->
 let state:=lanes ro slide entry incoming j in
 mask state result_mask=accepted entry j /\
 forall i,(i<4)%nat -> zmm state i=chunk (selected entry j+bias 64) i.
Proof.
 intro J;unfold lanes,MaskedWords.execute;rewrite (proj2 (Nat.ltb_lt _ _) J).
 pose proof (circuit_words (vectors (loaded entry) j) (incoming j) (regs (loaded entry) 0%nat) rd ro)
   as [M V].
 cbv zeta;change (mem (loaded entry)) with (mem entry);fold rd.
 set (v:=vectors (loaded entry) j) in *.
 assert (Load:forall i,(i<4)%nat -> v (8+i)%nat=in_word entry j i)
   by (intros;apply (loaded_word P);assumption).
 set (a:=in_word entry j 0);set (b:=in_word entry j 1);
 set (c:=in_word entry j 2);set (d:=in_word entry j 3).
 assert (Wa:v 8%nat=a) by apply (Load 0%nat ltac:(lia)).
 assert (Wb:v 9%nat=b) by apply (Load 1%nat ltac:(lia)).
 assert (Wc:v 10%nat=c) by apply (Load 2%nat ltac:(lia)).
 assert (Wd:v 11%nat=d) by apply (Load 3%nat ltac:(lia)).
 destruct literals as [L0 [L1 L3]].
 rewrite Wa,Wb,Wc,Wd,L0,L1,L3 in M,V.
 assert (Bound:forall i,0<=in_word entry j i<Q) by (intro;apply read_word_bound,W).
 assert (S:scalar entry j=four_words a b c d) by apply scalar_words.
 assert (Ok:below a b c d l0 l1 l3=accepted entry j).
 { unfold accepted;rewrite S;apply below_correct;apply Bound. }
 rewrite Ok in M,V. split;[exact M|].
 intros i I;rewrite V by assumption;unfold selected;destruct (accepted entry j).
 - rewrite S;apply biased_chunk;auto;apply Bound.
 - now apply rejected_chunk.
Qed.
Lemma high_result j : (8<=j)%nat -> mask (lanes ro slide entry incoming j) result_mask=false.
Proof. intro H;unfold lanes,MaskedWords.execute;rewrite (proj2 (Nat.ltb_ge _ _) H);apply high_mask_clear. Qed.
End Run.
