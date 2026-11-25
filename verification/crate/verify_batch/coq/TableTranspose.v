From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords
 execution.MappedFetch execution.InstructionRoute execution.PermutationBlock memory.WriteTrace.
From Ed25519Simd.KeyTable Require Pack.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableEntry TableFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition moves op:=match op with
 | Pack.Unpack hi d a b=>[PermutationBlock.Unpack hi d a b]
 | Pack.Shuffle d a b imm=>[PermutationBlock.Shuffle d a b imm] | _=>[] end.
Definition code:=flat_map moves (Pack.transpose false).
Definition exit:list line:=[(1076,2%nat,Jump (1168-1078))].
Lemma image:linked TableFrame.text (route 756 code) /\ PermutationBlock.after 756 code=1076 /\ linked TableFrame.text exit.
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition reg (second:bool) n:=nth n (if second then [24;25;5;6;7;8;9;0]%nat else [16;17;18;19;20;21;22;23]%nat) 0%nat.
Definition indexes:=fold_left rearrange code (fun r j=>(r,j)).
Lemma layout second key limb : (key<8)%nat -> (limb<8)%nat -> indexes (reg second key) limb=(reg second limb,key).
Proof.
 assert (C:forallb (fun second=>forallb (fun key=>forallb (fun limb=>
   let '(r,j):=indexes (reg second key) limb in Nat.eqb r (reg second limb) && Nat.eqb j key)
    (seq 0 8)) (seq 0 8)) [false;true]=true) by (vm_compute;reflexivity).
 intros K I;apply forallb_forall with (x:=second) in C;[|destruct second;cbn;auto].
 apply forallb_forall with (x:=key) in C;[|apply in_seq;lia];apply forallb_forall with (x:=limb) in C;[|apply in_seq;lia].
 destruct(indexes (reg second key) limb) as [r j];apply Bool.andb_true_iff in C as [R J];apply Nat.eqb_eq in R,J;subst;reflexivity.
Qed.
Lemma tail i j : (i<4)%nat -> (j<8)%nat -> indexes (1+i)%nat j=((1+i)%nat,j).
Proof.
 intros I J;destruct i as [|[|[|[|i]]]];try lia;destruct j as [|[|[|[|[|[|[|[|j]]]]]]]];try lia;vm_compute;reflexivity.
Qed.
Local Opaque code.
Definition execute bias:=segment (TableFrame.base bias) TableFrame.text (length code+1).
Record post e p q:Prop:=Post {
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 registers:regs(machine q)=regs(machine p);
 memory_after:mem(machine q)=mem(machine p);
 rows:forall second key limb,(key<8)%nat -> (limb<8)%nat ->
  vectors(machine q) limb (reg second key)=vectors(machine p) key (reg second limb);
 tail_rows:forall i j,(i<4)%nat -> (j<8)%nat -> vectors(machine q) j (1+i)%nat=vectors(machine p) j (1+i)%nat
}.

Theorem checked pol bias e p : loaded pol bias (mem e) (writable e) ->
 ip p=TableFrame.base bias+756 -> accounted e (writable e) p -> well_formed(machine p) ->
 exists q,execute bias p=Some q /\ ip q=TableFrame.base bias+1168 /\ post e p q.
Proof.
 intros I PC Acc W;set (s:=machine p);set (o:=TableFrame.base bias) in *;set (c:=LinkedRun.carry p).
 destruct(image) as [Code [End Exit]].
 destruct(run_ops o _ _ _ s c Code) as [t [R [G [M [F V]]]]];rewrite End in R.
 assert (Jump:run 1 (ScalarBytes.fetch o TableFrame.text) (State(Running 1076) t c)=Some(State(Running 1168) t c,[]))
   by (apply (InstructionRoute.checked _ _ _ Exit);reflexivity).
 pose proof(run_append _ _ _ _ _ R _ _ _ Jump) as Run.
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(at_segment _ _ p o TableFrame.text _ 756 _ _ Acc PC Map Sep Run (Forall_nil _)) as [Next Paid].
 assert (Supply:forall r j,live t r j=let '(b,k):=indexes r j in live s b k).
 { intros r j;rewrite V.
   pose proof(related (fun pair value=>value=live s (fst pair) (snd pair)) code (fun r j=>(r,j)) (live s)
        ltac:(intros;reflexivity) r j) as H;fold indexes in H;destruct(indexes r j);exact H. }
 eexists;split;[exact Next|split;[reflexivity|constructor]].
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ W Next).
 - exact G.
 - exact M.
 - intros second key limb K N;change (live t (reg second key) limb=live s (reg second limb) key);now rewrite Supply,layout.
 - intros i j N J;change (live t (1+i)%nat j=live s (1+i)%nat j);now rewrite Supply,tail.
Qed.
