From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.StoreHistory abi.SysV
 memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require abi.FramePointer.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Operands Audit FirstStage.
From Ed25519Simd.FullLadder Require StageEntry TopPair.
Local Open Scope Z_scope.

Definition top s:=regs s 4%nat.
Definition header s x:=top s-64<=x<top s+8.
Definition writable s x:=regs s 7%nat<=x<regs s 7%nat+1280 \/ top s-5032<=x<top s-64.
Definition saved_memory slide s:=WriteTrace.replay (mem s)
 (FramePointer.stores (slide+entry_pc) (top s) (regs s)++StageEntry.spill (slide+entry_pc) (top s) s).
Definition live g:=In g (3::5::12::13::14::nil)%nat.
Record intact slide s v : Prop:=Intact {
 frame_pointer:regs v 5%nat=top s-8; accumulator:regs v 3%nat=regs s 7%nat;
 keys:regs v 12%nat=regs s 6%nat; base_table:regs v 13%nat=regs s 2%nat; scalar:regs v 14%nat=regs s 1%nat;
 header_bytes:preserved (header s) (saved_memory slide s) (mem v);
 sources:sources_unchanged s v
}.

Lemma after slide s p q : placement slide s -> intact slide s (machine p) ->
 (forall r,live r -> regs(machine q) r=regs(machine p) r) ->
 StoreHistory.extends (writable s) p q -> intact slide s (machine q).
Proof.
 intros P F Reg Hist;destruct F as [BP BX K B S Slots External].
 constructor;try (rewrite Reg by (cbv [live In];tauto);assumption).
 - intros x X;rewrite (StoreHistory.preserves _ _ _ Hist);[apply Slots,X|].
   pose proof(point_stack _ _ P);unfold writable,header,top,disjoint in *;lia.
 - intros a n I x X;rewrite (StoreHistory.preserves _ _ _ Hist);[apply (External a n I x X)|].
   destruct(source_regions _ _ P a n I);unfold writable,top,disjoint in *;lia.
Qed.
Lemma top_region s x:TopPair.allowed s x -> writable s x.
Proof.
 unfold TopPair.allowed,TopPoint.region,TopPair.point,writable,top,base_of,staging,pad_of;
 pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia.
Qed.
Lemma first slide s u : placement slide s -> valid_inputs (slide+stage_pc) (pad_of s) s ->
 StageEntry.entry_state slide s u -> intact slide s (snd(S.run (slide+stage_pc) u)).
Proof.
 intros P V E;destruct(entry_inputs _ _ _ P E) as [G M].
 pose proof(placement_preserved _ _ _ _ G M ltac:(lia) _ _ (proj2 V 31%nat ltac:(lia))) as Layout.
 pose proof(SA.stage_correct _ SO.assembled_stage_round_correct _ _ Layout (StageEntry.stage_words _ _ _ E)) as Post.
 cbv zeta in Post;destruct(S.run _ _) as [pc v] in Post|-*;cbn [snd].
 destruct Post as [_ [_ [_ [_ [_ [Saved [F _]]]]]]].
 destruct(StageEntry.stage_arguments _ _ _ E) as [SP [DI [SI [DX [CX [R8 [I [BX [K [B S]]]]]]]]]].
 assert (Dst:regs u 7%nat=base_of s) by (apply G;cbv [In];tauto).
 constructor;try (rewrite Saved by (cbv [sysv_saved In];tauto);assumption || exact (StageEntry.saved_rbp _ _ _ E)).
 - intros x X;rewrite F.
   + rewrite (StageEntry.stage_memory _ _ _ E);unfold saved_memory,StageEntry.stores;rewrite (app_assoc _ _ (_::nil)),replay_app.
     change (commit (saved_memory slide s) (StageEntry.call_store (slide+entry_pc) (top s)) x=saved_memory slide s x).
     unfold commit,StageEntry.call_store;apply write_outside;change (~(StageEntry.base (top s)-8<=x<StageEntry.base (top s)-8+8)).
     unfold StageEntry.base,header,top in *;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia.
   + unfold SA.destination;rewrite Dst;unfold base_of,staging,pad_of,header,top in *;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia.
 - intros a n I' x X;rewrite F;[apply (M a n I' x X)|].
   destruct(source_regions _ _ P a n I') as [_ Sep];unfold SA.destination;rewrite Dst.
   unfold base_of,staging,pad_of,disjoint in *;pose proof(Z.mod_pos_bound (regs s 4%nat) 64 ltac:(lia));lia.
Qed.
