From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.Packed memory.PackedMemory
  memory.FlatMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

Definition instruction ip s sym op : list store := match op with
 | Packed.Store row r | StoreAligned row r =>
   [WriteTrace.Store ip (regs s 7%nat+64*Z.of_nat row) 64
     (fun k=>value s (byte (zmm sym r) (Z.to_nat k)))]
 | _=>[] end.
Fixpoint trace pc s sym ops := match ops with []=>[] | op::tail=>
 instruction pc s sym op ++ trace (pc+Z.of_nat(length(encode op))) s (step sym op) tail end.
Definition region s rows x := regs s 7%nat<=x<regs s 7%nat+64*Z.of_nat rows.

Lemma one_store aligned rows pc s sym op :
 valid_with_alignment aligned rows op=true ->
 confined (region s rows) (instruction pc s sym op) /\
 forall x,mem (finish rows (step sym op) s) x=
   replay (mem (finish rows sym s)) (instruction pc s sym op) x.
Proof.
 intros V;destruct op;try solve [split;[constructor|reflexivity]].
 all: cbn [valid_with_alignment] in V;repeat rewrite andb_true_iff in V;
 assert (R:(row<rows)%nat) by (apply Nat.ltb_lt;tauto);
 split;[constructor;[unfold region,permits,touches;cbn [size address];lia|constructor]|
        intro;apply store_writes_bytes,R].
Qed.

Lemma replay_ext m m' ws : (forall x,m x=m' x) -> forall x,replay m ws x=replay m' ws x.
Proof.
 revert m m';induction ws as [|w t IH];intros m m' E x;[apply E|].
 apply IH;intro y;unfold commit,write_bytes;destruct (_ && _)%bool;auto.
Qed.

Theorem sequence aligned rows ops : forall pc s sym,
 forallb (valid_with_alignment aligned rows) ops=true ->
 confined (region s rows) (trace pc s sym ops) /\
 forall x, mem (finish rows (fold_left step ops sym) s) x =
 replay (mem (finish rows sym s)) (trace pc s sym ops) x.
Proof.
 induction ops as [|op t IH];intros pc s sym V;[split;[constructor|reflexivity]|].
 apply andb_true_iff in V as [H T].
 destruct (one_store _ _ pc s sym op H) as [W M].
 destruct (IH (pc+Z.of_nat(length(encode op))) s (step sym op) T) as [Ws Ms].
 cbn [trace fold_left]. split;[apply Forall_app;auto|]. intro x.
 rewrite Ms,replay_app;apply replay_ext,M.
Qed.

Corollary execution aligned rows pc ops s :
 forallb (valid_with_alignment aligned rows) ops=true ->
 let ws:=trace pc s initial ops in
 confined (region s rows) ws /\
 forall x,mem (execute rows ops s) x=replay (mem s) ws x.
Proof.
 intro V;destruct (sequence _ _ ops pc s initial V) as [W M];split;[exact W|].
 intro x;rewrite <- (replay_ext (mem (finish rows initial s)) (mem s) _);
 [exact (M x)|]. intro y;unfold finish;cbn [mem initial stores];destruct (_ && _)%bool;reflexivity.
Qed.
