From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.StoreHistory
 memory.ByteMemory memory.FlatMemory memory.WriteTrace abi.SysV.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Operands Audit FirstStage LoopFrame.
From Ed25519Simd.FullLadder Require LoopStageCall RoundOperands.
Import ListNotations. Local Open Scope Z_scope.
Local Notation text := StageRound.ObjectBytes.symbol_bytes.

Definition band s x:=base_of s-8<=x<base_of s+3520.
Lemma work s x:band s x -> writable s x.
Proof. intro X;right;unfold band,base_of,staging,pad_of,top in *;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia. Qed.
Lemma outside_image slide s a n : placement slide s -> In (a,n) images ->
 forall x,slide+a<=x<slide+a+n -> ~writable s x.
Proof. intros P I;destruct(loaded_images _ _ P a n I) as [_ [Point Stack]];unfold writable,top,disjoint in *;intros;lia. Qed.

Definition resume q :=
 if list_eq_dec Z.eq_dec (snapshot (mem(machine q)) (ip q) (length text)) text then
 let '(pc,v):=S.run (ip q) (machine q) in Some (Cursor pc v None (log q++SA.writes (ip q) (machine q)))
 else None.
Definition execute slide p:=bind (LoopStageCall.enter slide p) resume.

Record result slide s n p q:Prop:=Result {
 next:ip q=slide+entry_pc+853; words:well_formed(machine q); stack:regs(machine q) 4%nat=base_of s;
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 frame:intact slide s (machine q);
 writes:StoreHistory.extends (band s) p q;
 rows:RoundOperands.selected s (base_of s) n (mem(machine q))
}.

Theorem checked slide s n p:placement slide s -> valid_inputs (slide+stage_pc) (pad_of s) s ->
 well_formed(machine p) -> intact slide s (machine p) -> ip p=slide+entry_pc+828 ->
 regs(machine p) 4%nat=base_of s -> regs(machine p) 15%nat=Z.of_nat n+1 -> (n<31)%nat ->
 mapped (mem(machine p)) (slide+entry_pc) symbol_bytes -> mapped (mem(machine p)) (slide+stage_pc) text ->
 exists q,execute slide p=Some q /\ result slide s n p q.
Proof.
 intros P V W F PC SP Count N Map Code.
 destruct(LoopStageCall.checked _ _ _ _ P (proj1 V) W F PC SP Count N Map) as [u [Call E]].
 pose proof(LoopStageCall.writes _ _ _ _ _ E) as Push.
 pose proof(LoopStageCall.at_stage _ _ _ _ _ E) as At.
 assert (Image:mapped (mem(machine u)) (slide+stage_pc) text).
 { eapply StoreHistory.image;[eapply StoreHistory.lend;[apply LoopStageCall.slot_work|exact Push]|exact Code|].
   apply outside_image;[exact P|right;left;reflexivity]. }
 pose proof(LoopStageCall.frame _ _ _ _ _ E) as UF.
 pose proof(LoopStageCall.args _ _ _ _ _ E) as Args;pose proof(LoopStageCall.args_for _ _ _ Args) as G.
 destruct Args as [Stack [Dst Args]].
 pose proof(sources _ _ _ UF) as M.
 pose proof(placement_preserved _ _ _ _ G M ltac:(lia) _ _ (proj2 V n ltac:(lia))) as Layout.
 pose proof(LoopStageCall.words _ _ _ _ _ E) as Words.
 pose proof(SA.stage_correct _ SO.assembled_stage_round_correct _ _ Layout Words) as Post.
 destruct(SA.write_footprint _ SO.assembled_stage_round_correct _ _ Layout) as [Safe Replay].
 pose proof(SA.returned_words _ SO.assembled_stage_round_correct (slide+stage_pc) (machine u) Words) as WF.
 cbv zeta in Post;destruct(S.run (slide+stage_pc) (machine u)) as [pc v] eqn:R in Post,Replay,WF.
 destruct Post as [_ [_ [_ [Back [Restored [Kept [_ [_ Row]]]]]]]].
 set(q:=Cursor pc v None (log u++SA.writes (slide+stage_pc) (machine u))).
 assert (Tail:StoreHistory.extends (band s) u q).
 { exists (SA.writes (slide+stage_pc) (machine u));split;[reflexivity|split;[|exact Replay]].
   eapply Forall_impl;[|exact Safe];intros w H x X;specialize(H x X);unfold SA.destination in H;rewrite Dst in H;unfold band;lia. }
 exists q;split.
 - unfold execute;rewrite Call;cbn [bind];unfold resume;rewrite At,(snapshot_mapped _ _ _ Image).
   destruct(list_eq_dec _ text text);[now rewrite R|contradiction].
 - constructor;try exact WF.
   + change (pc=slide+entry_pc+853);rewrite Back,Stack;apply (LoopStageCall.back _ _ _ _ _ E).
   + change (regs v 4%nat=base_of s);rewrite Restored,Stack;ring.
   + intros r I;change (regs v r=regs(machine p) r);rewrite Kept by exact I;apply (LoopStageCall.saved _ _ _ _ _ E),I.
   + apply (LoopFrame.after slide s u q P UF);[intros r I;apply Kept;cbv [live In] in I;cbv [sysv_saved In];tauto|].
     exact (StoreHistory.lend _ _ _ _ (work s) Tail).
   + eapply StoreHistory.compose;[|exact Tail];eapply StoreHistory.lend;[|exact Push];unfold band,LoopStageCall.slot;intros;lia.
   + intros k i j I J;unfold q;cbn [machine];rewrite <-Dst,Row by assumption.
     eapply selected_data;[exact G|exact M|lia|exact V|exact J|exact I].
Qed.
