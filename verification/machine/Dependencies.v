From Coq Require Import List ZArith Bool.
From Machine Require Import Instructions.
From Machine Require Logic.
Import ListNotations.

(* Track which register values two executions agree on. XOR of a register
   with itself is independent of its old value. *)
Definition same_result (mem : nat -> Z -> bool) (known:nat -> bool) dst op :=
 match op with
 | Copy a | Shl a _ | Shr a _ => known a
 | Load b d => mem b d
 | Xor a b => Nat.eqb a b || (known a && known b)
 | Add a b | Sub a b | Mul a b | And a b => known a && known b
 | Madd _ a b => known dst && known a && known b end.
Fixpoint agreement mem code known := match code with
 | [] => known
 | (dst,op)::rest => agreement mem rest (put known dst (same_result mem known dst op)) end.
Lemma same_result_sound mem known dst op l1 l2 r1 r2 :
 (forall b d, mem b d = true -> l1 b d = l2 b d) ->
 (forall i, known i = true -> r1 i = r2 i) ->
 same_result mem known dst op = true -> bits l1 r1 dst op = bits l2 r2 dst op.
Proof.
 intros L R. destruct op; cbn [same_result bits];
 try (intro H; solve [rewrite (R _ H); reflexivity | now rewrite (L _ _ H)]).
 all: try (intro H; repeat rewrite Bool.andb_true_iff in H;
     decompose [and] H; repeat match goal with K:?f ?i = true |- _ => rewrite (R _ K); clear K end;
     reflexivity).
 destruct (Nat.eqb a b) eqn:E; cbn.
 - apply Nat.eqb_eq in E; subst. unfold Logic.vpxorq; now rewrite !Z.lxor_nilpotent.
 - intro H. apply Bool.andb_true_iff in H as [A B]; now rewrite (R _ A),(R _ B).
Qed.
Lemma agreement_sound mem code known l1 l2 r1 r2 :
 (forall b d, mem b d = true -> l1 b d = l2 b d) ->
 (forall i, known i = true -> r1 i = r2 i) ->
 forall i, agreement mem code known i = true -> run l1 code r1 i = run l2 code r2 i.
Proof.
 intro L; revert known r1 r2; induction code as [|[dst op] rest IH];
 intros known r1 r2 R; cbn [agreement run]; auto.
 apply IH. intros j. unfold put. destruct (Nat.eqb dst j); [apply same_result_sound; assumption | apply R].
Qed.
Lemma untouched l code r i :
 forallb (fun ins => negb (Nat.eqb (fst ins) i)) code = true ->
 run l code r i = r i.
Proof.
 revert r; induction code as [|[dst op] rest IH]; intros r H; cbn [run]; auto.
 apply Bool.andb_true_iff in H as [D H]. rewrite IH by exact H.
 apply Bool.negb_true_iff in D. cbn in D. unfold put; now rewrite D.
Qed.
