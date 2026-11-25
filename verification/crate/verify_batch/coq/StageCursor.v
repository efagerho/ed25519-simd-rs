From Coq Require Import List ZArith Lia.
From Machine Require Import execution.ScalarRefinement isa.Instructions execution.LinkedCalls execution.WordBounds execution.WordSemantics execution.ScalarBytes
 execution.MappedFetch execution.FrameInstructions memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Image Rows Return EntryWrites DescriptorStores StageWrites.
Import ListNotations. Local Open Scope Z_scope.

Definition before_add:=inputs++publish++indices.
Theorem advanced o text delta e s c t ws:bound text delta -> placement e -> regs s 4%nat=Rows.frame e ->
 run 42 (ScalarBytes.fetch o text) (State(Running(offset Stage)) s c)=Some(t,ws) ->
 regs(cpu_state t) 3%nat=word(regs s 3%nat+320) /\ regs(cpu_state t) 5%nat=regs s 5%nat.
Proof.
 intros [Code Call] P SP R;set(a:=offset Stage+FrameInstructions.width before_add).
 change (decoded text (offset Stage) (before_add++[(7%nat,Add64 3 320)]++setup)) in Code.
 destruct(prefix_decoded _ _ before_add _ Code) as [First [Add Args]];fold a in Add,Args.
 pose proof(stack_ok _ P) as [[Lo Hi] _].
 assert (Fit:fits64 (Rows.frame e) 928) by (unfold fits64,Rows.frame,sp in *;lia).
 destruct(sequence o text 0 928 (Rows.frame e) before_add ltac:(lia) Fit eq_refl (offset Stage) s c
   ltac:(change (0<=82);lia) First SP) as [v [cv [w [Read [Stack _]]]]];fold a in Read.
 assert (Kept:forall g,g=3%nat \/ g=5%nat -> regs v g=regs s g).
 { intros g K;apply (kept_sequence o text g before_add (offset Stage) s c _ _ ltac:(change (0<=82);lia) First ltac:(destruct K as [->| ->];reflexivity) Read). }
 set (m:=word(word(regs v 3%nat)+320));set (u:=with_zf (set v 3 m) (m=?0)).
 assert (Next:exists cf,run 1 (ScalarBytes.fetch o text) (State(Running a) v cv)=Some(State(Running(offset PrepareArgs)) u cf,[])).
 { cbn [run];rewrite (fetch_at o text a v cv 7 _ ltac:(change (0<=346);lia) Add);eexists;reflexivity. }
 destruct Next as [cf Next].
 destruct(setup_args o text (offset PrepareArgs) u cf e Args ltac:(change (0<=353);lia) P Stack)
    as [q [Prep [StackQ _]]].
 assert (G:forall g,g=3%nat \/ g=5%nat -> regs q g=regs u g).
 { intros g K;apply (kept_sequence o text g setup (offset PrepareArgs) u cf _ _ ltac:(change (0<=353);lia) Args ltac:(destruct K as [->| ->];reflexivity) Prep). }
 change (offset PrepareArgs+27) with (offset CallPrepare) in Prep.
 set(child:=push q (o+offset Prepared)).
 assert (Enter:exists w',run 1 (ScalarBytes.fetch o text) (State(Running(offset CallPrepare)) q cf)=
   Some(State(Running(word(o+delta)-o)) child cf,w')).
 { cbn [run];rewrite (fetch_at o text (offset CallPrepare) q cf 5 _ ltac:(change (0<=380);lia) Call).
   cbn [step option_map];unfold delta_call;change (offset CallPrepare+Z.of_nat 5) with (offset Prepared).
   replace (offset Prepared+(delta-offset Prepared)) with delta by ring;
   eexists;reflexivity. }
 destruct Enter as [w' Enter];pose proof(run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ Read _ _ _ Next) _ _ _ Prep) _ _ _ Enter) as Full.
 change (length before_add+1+4+1)%nat with 42%nat in Full;rewrite R in Full;injection Full as -> _.
 change (regs q 3%nat=word(regs s 3%nat+320) /\ regs q 5%nat=regs s 5%nat).
 rewrite (G 3%nat),(G 5%nat) by auto;change (word(word(regs v 3%nat)+320)=word(regs s 3%nat+320) /\ regs v 5%nat=regs s 5%nat).
 rewrite word_add,(Kept 3%nat),(Kept 5%nat) by auto;auto.
Qed.
