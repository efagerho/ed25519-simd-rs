From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds execution.WordSemantics memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require Prologue IndexStores ChunkRows.
Local Open Scope Z_scope.

(* The reference CPU always denotes the Rust caller. A window changes the
   rows consumed by one iteration, while RSI at the root still bounds every
   output index. The first window is selected only at the outer entry. *)
Class t := { first:nat }.
Definition initial:t:={| first:=0 |}.
Definition at_row i:t:={| first:=i |}.

Section Window.
Context `{w:t}.
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
Lemma live_count e:well_formed e -> next_count e=Z.of_nat(remaining e-8).
Proof.
 intros [W _];unfold next_count,remaining;destruct first;[|reflexivity].
 unfold Prologue.rows_left,Scatter.count;specialize(W 6%nat);rewrite (word_fits _ W).
 destruct(Z.ltb_spec (regs e 6%nat) 8);[lia|];rewrite word_fits by (unfold word64 in *;lia);lia.
Qed.
End Window.
