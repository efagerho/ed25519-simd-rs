From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds execution.WordSemantics memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require CallerSpills Prologue IndexStores ChunkRows.
Local Open Scope Z_scope.

(* The reference CPU always denotes the Rust caller. A window changes the
   rows consumed by one iteration, while RSI at the root still bounds every
   output index. The first window is selected only at the outer entry. *)
Class t := { first:nat; before:bytes }.
Definition initial:t:={| first:=0; before:=fun _=>0 |}.
#[global] Existing Instance initial | 100.
Definition at_memory i m:t:={| first:=i; before:=m |}.
Definition at_row i:=at_memory i (fun _=>0).

Section Window.
Context `{w:t}.
Definition output_byte e x:=span (output e) (Z.of_nat(Scatter.count e)) x.
Definition stack_slot e x:=sp e-40<=x<sp e.
(* The snapshot is the real memory at the start of this window. Previous
   descriptor positions can be anywhere in the output permutation. *)
Definition earlier e x:=placement e /\ output_byte e x /\ exists i,(i<first)%nat /\ x=output e+Z.of_nat(Scatter.position e i).
Definition protected e x:=match first with O=>stack_slot e x | S _=>stack_slot e x \/ earlier e x end.
Definition expected e x:=match first with O=>Return.saved_memory e x | S _=>
 if ((sp e-40<=?x)&&(x<?sp e))%bool then Return.saved_memory e x else before x end.
Definition saved e (m:bytes):=forall x,protected e x -> m x=expected e x.
Definition saved_caller e s:=saved e (mem s) /\ regs s 5%nat=regs e 5%nat.

Lemma cases e x:protected e x -> stack_slot e x \/ earlier e x.
Proof. unfold protected;destruct first;auto. Qed.
Definition external_byte e x:=(x<sp e-16384 \/ sp e+8<=x) /\ (x<scratch e \/ scratch e+25344<=x).
Lemma geometry e x:protected e x -> sp e-40<=x<sp e \/
 external_byte e x.
Proof.
 intro X;destruct(cases _ _ X) as [S|[P [O _]]];[left;exact S|right].
 destruct(out_stack _ P), (out_scratch _ P);unfold external_byte,output_byte,span,disjoint in *;lia.
Qed.
Lemma raw_saved e m:saved e m -> CallerSpills.saved e m.
Proof.
 intros H x X;assert (K:protected e x) by (unfold protected;destruct first;[exact X|left;exact X]).
 rewrite (H x K);unfold expected;destruct first;[reflexivity|].
 rewrite (proj2(Z.leb_le _ _) (proj1 X)),(proj2(Z.ltb_lt _ _) (proj2 X));reflexivity.
Qed.
Lemma attach e m:CallerSpills.saved e m -> (forall x,earlier e x -> m x=before x) -> saved e m.
Proof.
 intros S E x X;destruct(cases _ _ X) as [Stack|Older].
 - unfold expected;destruct first;[apply S,Stack|].
   rewrite (proj2(Z.leb_le _ _) (proj1 Stack)),(proj2(Z.ltb_lt _ _) (proj2 Stack));apply S,Stack.
 - destruct Older as [P [Out [i [I At]]]];pose proof(out_stack _ P) as Sep.
   unfold expected;destruct first eqn:F;[lia|].
   destruct ((sp e-40<=?x)&&(x<?sp e))%bool eqn:T.
   + apply Bool.andb_true_iff in T as [L U];apply Z.leb_le in L;apply Z.ltb_lt in U;
     unfold output_byte,span,disjoint in *;lia.
   + apply E;split;[exact P|split;[exact Out|exists i;rewrite F;auto]].
Qed.
Lemma previous e m:placement e -> Scatter.indices e -> (first<=Scatter.count e)%nat -> saved e m ->
 forall i,(i<first)%nat -> m(output e+Z.of_nat(Scatter.position e i))=before (output e+Z.of_nat(Scatter.position e i)).
Proof.
 intros P [Idx _] N H i I;set(x:=output e+Z.of_nat(Scatter.position e i)).
 assert (O:output_byte e x) by (specialize(Idx i ltac:(lia));unfold x,output_byte,span;lia).
 assert (A:earlier e x) by (split;[exact P|split;[exact O|exists i;auto]]).
 assert (T:protected e x) by (unfold protected;destruct first;[lia|auto]).
 rewrite (H _ T);unfold expected;destruct first;[lia|].
 destruct ((sp e-40<=?x)&&(x<?sp e))%bool eqn:B;[|reflexivity].
 apply Bool.andb_true_iff in B as [L U];apply Z.leb_le in L;apply Z.ltb_lt in U;
 destruct(out_stack _ P);unfold output_byte,span in *;lia.
Qed.

Definition remaining e:=match first with O=>Scatter.count e | S _=>(Scatter.count e-first)%nat end.
Definition row e j:=ChunkRows.lane first (remaining e) j.
Definition active e:=Nat.min (remaining e) 8.
Definition next_count e:=match first with O=>Prologue.rows_left(regs e 6%nat)
 | S _=>Z.of_nat(remaining e-8) end.
Definition next_descriptor e v:=(8<remaining e)%nat -> v=word(regs e 7%nat+(40*Z.of_nat first+320)).
Definition index e j:=descriptor (mem e) (regs e 7%nat) (row e j) 32.
Definition metadata e:=IndexStores.metadata (Rows.frame e) (Z.of_nat(active e)) (index e).

Lemma rest e:remaining e=(Scatter.count e-first)%nat.
Proof. unfold remaining;destruct first;lia. Qed.
Lemma live_row e j:(0<remaining e)%nat -> (row e j<Scatter.count e)%nat.
Proof. unfold row,ChunkRows.lane;rewrite rest;lia. Qed.
Lemma own_row e j:(j<remaining e)%nat -> row e j=(first+j)%nat.
Proof. unfold row,ChunkRows.lane;intros;rewrite Nat.min_l by lia;reflexivity. Qed.
Lemma relative_range e j:(0<remaining e)%nat -> (j<8)%nat ->
 (first<=row e j<first+active e)%nat.
Proof. unfold row,ChunkRows.lane,active;lia. Qed.
Lemma total e:(0<remaining e)%nat -> (first+remaining e=Scatter.count e)%nat.
Proof. rewrite rest;lia. Qed.
Lemma live_count e:well_formed e -> next_count e=Z.of_nat(remaining e-8).
Proof.
 intros [W _];unfold next_count,remaining;destruct first;[|reflexivity].
 unfold Prologue.rows_left,Scatter.count;specialize(W 6%nat);rewrite (word_fits _ W).
 destruct(Z.ltb_spec (regs e 6%nat) 8);[lia|];rewrite word_fits by (unfold word64 in *;lia);lia.
Qed.
End Window.
