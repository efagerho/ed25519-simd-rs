From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch execution.StoreHistory memory.ByteMemory memory.FlatMemory.
From Ed25519Simd Require Import Wide51 PointResults.
From Ed25519Simd.LadderStep Require Callees LeafHistory.
From Ed25519Simd.FullLadder Require Import LinkedBytes Program Operands Native Audit LoopFrame.
From Ed25519Simd.FullLadder Require LoopStage TopPair.
Import ListNotations. Local Open Scope Z_scope.
Definition texts:=[(entry_pc,symbol_bytes);(stage_pc,StageRound.ObjectBytes.symbol_bytes);
 (L.wrapper_pc,L.symbol_bytes);(L.double4_pc,Callees.doubling_bytes);(L.cached_pc,Callees.addition_bytes)].
Definition loaded slide m:=forall a code,In (a,code) texts -> mapped m (slide+a) code.
Lemma sizes a code:In (a,code) texts -> In (a,Z.of_nat(length code)) images.
Proof. intros [E|[E|[E|[E|[E|[]]]]]];injection E as <- <-;cbv [images In];tauto. Qed.
Lemma after slide s p q:placement slide s -> loaded slide (mem(machine p)) -> StoreHistory.extends (writable s) p q ->
 loaded slide (mem(machine q)).
Proof.
 intros P Map Hist a code Member;eapply StoreHistory.image;[exact Hist|apply Map,Member|];apply LoopStage.outside_image;[exact P|apply sizes,Member].
Qed.
Lemma step_images slide m:loaded slide m -> LeafHistory.images slide m.
Proof.
 intro I;split;[apply I;do 2 right;left;reflexivity|split];[rewrite Callees.double_binding|rewrite Callees.add_binding];apply I;
 [do 3 right;left|do 4 right;left];reflexivity.
Qed.
Definition point s p:=buffer_words (mem(machine p)) (regs s 7%nat).
Lemma point_kept slide s p q : placement slide s -> StoreHistory.extends (LoopStage.band s) p q ->
 agrees_words 160 (point s q) (point s p).
Proof.
 intros P H i I;apply (preserved_read 8 (fun x=>~LoopStage.band s x));[apply (StoreHistory.preserves _ _ _ H)|].
 pose proof(LA.cache_point _ _ _ _ _ (ladder_placement _ _ _ (child_layout _ _ P))) as Sep.
 pose proof(point_stack _ _ P) as Stack;pose proof(Z.mod_pos_bound (top s) 64 ltac:(lia)).
 unfold LoopStage.band,disjoint,base_of,staging,pad_of,top in *;intros k K;change (0<=k<8) in K;lia.
Qed.
Lemma strict_kept a b:agrees_words 160 a b -> strict b -> strict a.
Proof. intros E W c j C J i I;unfold cell;rewrite E by lia;apply (W c j C J i I). Qed.
