From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.StoreHistory abi.FrameRestore
 memory.ByteMemory memory.MemoryGeometry memory.WriteTrace abi.SysV.
From Ed25519Simd.FullLadder Require Import LinkedBytes Audit LoopFrame.
From Ed25519Simd.FullLadder Require LoopSlots.
Import ListNotations. Local Open Scope Z_scope.
Definition ret_path:list line:=[(894,1%nat,Ret)].
Lemma image:linked symbol_bytes (FrameRestore.path 880) /\ linked symbol_bytes ret_path.
Proof. split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute slide:=segment (slide+entry_pc) symbol_bytes 8.
Record result s p q:Prop:=Result {
 back:ip q=read_word (mem s) (top s); stack:regs(machine q) 4%nat=top s+8;
 saved:forall g,In g sysv_saved -> regs(machine q) g=regs s g;
 words:well_formed(machine q); bytes:mem(machine q)=mem(machine p);
 stores:StoreHistory.extends (LoopFrame.writable s) p q
}.
Theorem checked slide s p: placement slide s -> well_formed s -> intact slide s (machine p) -> well_formed(machine p) ->
 ip p=slide+entry_pc+880 -> mapped (mem(machine p)) (slide+entry_pc) symbol_bytes ->
 exists q,execute slide p=Some q /\ result s p q.
Proof.
 intros P W F WF PC Code;pose proof(frame_range _ _ P) as Range.
 destruct(FrameRestore.execute (slide+entry_pc) symbol_bytes 880 (machine p) (carry p) (top s) (regs s) (proj1 image)
   ltac:(unfold top,fits64 in *;lia) (frame_pointer _ _ _ F) (LoopSlots.saved _ _ _ F W)) as [Rest [M [SP [G _]]]].
 set(v:=FrameRestore.restored (top s) (machine p)) in *;set(r:=read_word (mem s) (top s)).
 assert (Pop:stack_top (regs v) (mem v)=r).
 { unfold stack_top,r;rewrite SP,M,(word_fits (top s)) by apply W;apply (LoopSlots.link _ _ _ F). }
 assert (End:run 1 (ScalarBytes.fetch (slide+entry_pc) symbol_bytes) (State(Running 894) v (carry p))=
   Some(State(Returned r) (LinkedCalls.returning v) (carry p),[])).
 { apply (InstructionRoute.checked _ _ _ (proj2 image));cbn [ret_path follow step loc cpu_state cf caller_step stack_step
    target_ip result_regs result_mem option_map app]. rewrite Pop,(word_fits r) by (apply read_word_bound,W);reflexivity. }
 pose proof(run_append _ _ _ _ _ Rest _ _ _ End) as R.
 destruct(StoreHistory.segment_checked (fun _=>False) _ _ _ _ _ _ _ PC Code ltac:(tauto) R (Forall_nil _)) as [Fetch Hist].
 eexists;split;[exact Fetch|constructor];try reflexivity.
 - change (word(regs v 4%nat+8)=top s+8);rewrite SP;apply word_fits;unfold top,fits64,word64 in *;lia.
 - intros g I;change (put (regs v) 4 (word(regs v 4%nat+8)) g=regs s g).
   unfold put;assert (g<>4%nat) by (intros ->;cbv [sysv_saved In] in I;intuition discriminate);rewrite (proj2(Nat.eqb_neq 4 g) ltac:(congruence));apply G,I.
 - exact (segment_wf _ _ _ _ _ WF Fetch).
 - exact (StoreHistory.lend (fun _=>False) (LoopFrame.writable s) _ _ (fun x H=>False_rect _ H) Hist).
Qed.
