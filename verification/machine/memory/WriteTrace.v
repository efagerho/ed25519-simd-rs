From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Blocks memory.FlatMemory.
Import ListNotations. Local Open Scope Z_scope.

(* A store carries the bytes consumed by the memory update. Several events
   with the same PC represent the enabled lanes of one masked instruction. *)
Record store := Store { pc : Z; address : Z; size : nat; payload : Z -> Z }.
Definition commit m w := write_bytes m (address w) (Z.of_nat (size w)) (payload w).
Definition replay (m : bytes) ws := fold_left commit ws m.
Definition touches w x := address w <= x < address w + Z.of_nat (size w).
Definition permits (region : Z -> Prop) w := forall x, touches w x -> region x.
Definition confined region ws := Forall (permits region) ws.

Lemma replay_app m xs ys : replay m (xs ++ ys) = replay (replay m xs) ys.
Proof. apply fold_left_app. Qed.

Lemma frame region ws : confined region ws -> forall m x, ~region x ->
 replay m ws x = m x.
Proof.
 induction 1 as [|w ws Allowed Tail IH]; intros m x Outside; [reflexivity|].
 change (replay (commit m w) ws x = m x). rewrite IH by assumption.
 apply write_outside. intro H. apply Outside, Allowed, H.
Qed.

Definition qword ip a v := Store ip a 8 (word_byte v).
Definition vector ip a v := Store ip a 64 (vector_byte v).
Definition masked_qwords ip a (enabled : nat -> bool) (v : nat -> Z) :=
 map (fun j => qword ip (a+8*Z.of_nat j) (v j)) (filter enabled (seq 0 8)).

Lemma masked_footprint ip a enabled v x :
 (exists w, In w (masked_qwords ip a enabled v) /\ touches w x) <->
 exists j, (j<8)%nat /\ enabled j=true /\ a+8*Z.of_nat j<=x<a+8*Z.of_nat j+8.
Proof.
 unfold masked_qwords. split.
 - intros [w [I X]]. apply in_map_iff in I as [j [<- J]].
   apply filter_In in J as [J E]. apply in_seq in J. exists j;split;[lia|split;assumption].
 - intros [j [J [E X]]]. exists (qword ip (a+8*Z.of_nat j) (v j));split;[apply in_map_iff;exists j;split;[reflexivity|];apply filter_In;split;[apply in_seq;lia|exact E]|exact X].
Qed.

(* Translate the existing block interpreter's memory effects without
   recomputing their destinations or values. *)
Definition block_store loc ip e d := match e with
 | DataOp (Write r a) => [vector ip (address_of loc a) (fun j=>zmm d j r)]
 | Push a t => [qword ip (address_of loc a) (pc_word loc t)]
 | _ => [] end.

Lemma block_store_memory loc ip e d m :
 replay m (block_store loc ip e d) = write_event loc e d m.
Proof. destruct e as [[]| |];reflexivity. Qed.

Lemma block_store_footprint loc ip e d x :
 (exists w, In w (block_store loc ip e d) /\ touches w x) <->
 exists cell, destination e=Some cell /\ inside loc cell x.
Proof.
 destruct e as [[]| |]; cbn [block_store destination In]; split;
 intros [w [H X]]; try contradiction; try discriminate;
 first [destruct H as [<-|[]];eexists;split;[reflexivity|exact X]|
        injection H as <-;eexists;split;[now left|exact X]].
Qed.
