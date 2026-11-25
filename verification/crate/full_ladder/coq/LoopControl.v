From Coq Require Import List Bool ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarBytes
 execution.ScalarWords execution.InstructionRoute execution.MappedFetch execution.StoreHistory memory.WriteTrace.
From Ed25519Simd.FullLadder Require Import LinkedBytes LoopFrame.
Import ListNotations. Local Open Scope Z_scope.
Definition start_path:list line:=[(822,6%nat,Imm32 15 31)].
Definition back_path:list line:=[(875,3%nat,Dec32 15);(878,2%nat,Branch Unequal (-52))].
Lemma image:linked symbol_bytes start_path /\ linked symbol_bytes back_path.
Proof. split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition start slide:=segment (slide+entry_pc) symbol_bytes 1.
Definition advance slide:=segment (slide+entry_pc) symbol_bytes 2.
Definition target n:=if Nat.eqb n 0 then 880 else 828.
Record change (at_pc count:Z) p q:Prop:=Change {
 next:ip q=at_pc; counter:regs(machine q) 15%nat=count;
 same:forall g,g<>15%nat -> regs(machine q) g=regs(machine p) g;
 memory:mem(machine q)=mem(machine p); log_kept:log q=log p; words:well_formed(machine q)
}.

Lemma start_checked slide p:ip p=slide+entry_pc+822 -> well_formed(machine p) ->
 mapped (mem(machine p)) (slide+entry_pc) symbol_bytes ->
 exists q,start slide p=Some q /\ change (slide+entry_pc+828) 31 p q.
Proof.
 intros PC W Map;set(u:=set (machine p) 15 31).
 assert (R:run 1 (ScalarBytes.fetch (slide+entry_pc) symbol_bytes) (State(Running 822) (machine p) (carry p))=
  Some(State(Running 828) u (carry p),[])) by (apply (InstructionRoute.checked _ _ _ (proj1 image));reflexivity).
 destruct(StoreHistory.segment_checked (fun _=>False) _ _ _ _ _ _ _ PC Map ltac:(tauto) R (Forall_nil _)) as [Run H].
 eexists;split;[exact Run|constructor];try reflexivity;try (cbn [finish log];apply app_nil_r).
 - intros g G;unfold u;cbn [finish machine cpu_state set set_regs regs];unfold put;rewrite (proj2(Nat.eqb_neq 15 g) ltac:(congruence));reflexivity.
 - exact (segment_wf _ _ _ _ _ W Run).
Qed.
Lemma advance_checked slide p n:ip p=slide+entry_pc+875 -> well_formed(machine p) ->
 regs(machine p) 15%nat=Z.of_nat n+1 -> (n<31)%nat ->
 mapped (mem(machine p)) (slide+entry_pc) symbol_bytes ->
 exists q,advance slide p=Some q /\ change (slide+entry_pc+target n) (Z.of_nat n) p q.
Proof.
 intros PC W Count N Map;set(i:=Z.of_nat n);set(u:=with_zf (set(machine p) 15 i) (i=?0)).
 assert (Dec:(regs(machine p) 15%nat-1) mod 2^32=i).
 { rewrite Count;fold i;replace (i+1-1) with i by ring;apply Z.mod_small;unfold i;lia. }
 assert (Zero:(i=?0)=Nat.eqb n 0) by (destruct n;reflexivity).
 assert (R:run 2 (ScalarBytes.fetch (slide+entry_pc) symbol_bytes) (State(Running 875) (machine p) (carry p))=
   Some(State(Running(target n)) u (carry p),[])).
 { apply (InstructionRoute.checked _ _ _ (proj2 image));cbn [back_path follow step cpu_state cf loc eval_condition with_zf flag option_map app].
   rewrite Dec;unfold u,target;rewrite Zero;destruct(Nat.eqb n 0);reflexivity. }
 destruct(StoreHistory.segment_checked (fun _=>False) _ _ _ _ _ _ _ PC Map ltac:(tauto) R (Forall_nil _)) as [Run H].
 eexists;split;[exact Run|constructor];try reflexivity;try (cbn [finish log];apply app_nil_r).
 - intros g G;unfold u;cbn [finish machine cpu_state with_zf set set_regs regs];unfold put;rewrite (proj2(Nat.eqb_neq 15 g) ltac:(congruence));reflexivity.
 - exact (segment_wf _ _ _ _ _ W Run).
Qed.
Lemma intact_after slide s pc n p q:intact slide s (machine p) -> change pc n p q -> intact slide s (machine q).
Proof.
 intros F C;destruct F as [BP BX K B S Slots Input];constructor;
 try (rewrite (same _ _ _ _ C) by discriminate;assumption).
 - now rewrite (memory _ _ _ _ C).
 - intros a w I x X;rewrite (memory _ _ _ _ C);apply (Input _ _ I _ X).
Qed.
Lemma history pc n p q region:change pc n p q -> StoreHistory.extends region p q.
Proof.
 intro E;exists [];split;[rewrite (log_kept _ _ _ _ E);symmetry;apply app_nil_r|split;[constructor|intro x;rewrite (memory _ _ _ _ E);reflexivity]].
Qed.
