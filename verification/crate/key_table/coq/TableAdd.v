From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Blocks execution.LinkedCalls execution.LinkedRun execution.LocatedReturn
 execution.KnownRegisters execution.WordSemantics execution.WordBounds memory.MemoryTrace memory.ByteMemory memory.BlockWrites memory.FlatMemory memory.WriteTrace abi.SysV.
From Ed25519Simd.CachedAdd Require Import CachedAddABI CachedAddMemory CachedAddSpec CachedAddBytes.
From Ed25519Simd.CachedAdd Require Program FrameProof Audit Object.
From Ed25519Simd.KeyTable Require TableAddCall.
From Ed25519Simd.KeyTable Require Import CallLayout.
Import ListNotations. Local Open Scope Z_scope.

Definition program:=Program.add_cached_program.
Definition initial bias e p:=let s:=machine p in
 entry_from_bytes true true (TableAddLayout.layout bias e) TableAddLayout.pad (regs s) (vectors s) (flag s) (mem s).
Definition execute bias e p:=option_map resumed (LocatedReturn.execute program (abi_layout true)
 (TableAddLayout.layout bias e) 200 (initial bias e p) p).
Record post (root:cpu) bias e p q:Prop:=Post {
 address:ip q=TableAddLayout.back bias;
 writes:accounted root (writable e) q;
 words:well_formed(machine q);
 stack:regs(machine q) 4%nat=CallLayout.stage e;
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 outside:preserved (fun x=>~PointFrame.writable_byte (TableAddLayout.layout bias e) TableAddLayout.pad x)
       (mem(machine p)) (mem(machine q));
 point_result:cached_add_spec true true
   (buffer_words (mem(machine p)) (CallLayout.point_ptr e)) (buffer_words (mem(machine p)) (CallLayout.stage e))
   (buffer_words (mem(machine q)) (CallLayout.point_ptr e))
}.

Lemma path bias e p : well_formed(machine p) ->
 exists c es,record_path 200 program (abi_layout true) (fst(initial bias e p))=Some(c,es).
Proof.
 intro W;unfold initial,entry_from_bytes;cbn [fst].
 pose proof(CachedAdd.FrameProof.frame_checked true true (Control Caller (fun r=>Int(regs(machine p) r)) (flag(machine p)) (fun _=>None))
   TableAddLayout.pad (regs(machine p) 5%nat) ltac:(right;right;right;left;reflexivity) (proj1 W 5%nat)) as H.
 fold program in H;destruct(record_path _ _ _ _) as [[c es]|];[eauto|discriminate].
Qed.
Local Opaque CachedAdd.Program.add_cached_program.

Theorem checked (root:cpu) bias e a p : placement e -> loaded root bias e ->
 TableAddCall.entry root bias e a p -> exists q,execute bias e p=Some q /\ post root bias e p q.
Proof.
 intros P I E;set (loc:=TableAddLayout.layout bias e);set (s:=machine p);set (st:=initial bias e p).
 pose proof(TableAddCall.arguments _ _ _ _ _ E) as Args;fold loc s in Args.
 pose proof(TableAddCall.words _ _ _ _ _ E) as W;pose proof(TableAddCall.writes _ _ _ _ _ E) as Acc.
 destruct(CachedAdd.Audit.run_concrete CachedAdd.Object.assembled_cached_add_correct true true loc TableAddLayout.pad (regs s) (vectors s) (flag s) (mem s) Args)
   as [Aligned [last [after Cert]]];fold st in Cert.
 pose proof(byte_guarantee Cert) as Frame.
 pose proof(concrete_entry_representable true true loc TableAddLayout.size TableAddLayout.pad (regs s) (vectors s) (flag s) (mem s) Args) as Rep.
 assert (Known:known_registers(fst st)).
 { intros r U;pose proof(proj2(proj2(proj2 Rep)) r) as K;change (CachedAddBytes.scalar_value loc (gpr (fst st) r)=Some(regs s r)) in K;
   now rewrite U in K. }
 destruct(lift_return _ _ _ _ _ _ _ _ _ Known (did_return Cert) Frame) as [_ [WF Preserve]].
 assert (Image:MappedFetch.mapped (mem s) (code_base loc) (ProgramLayout.image program)).
 { change (MappedFetch.mapped (mem s) (bias+TableAddLayout.origin) (ProgramLayout.image Program.add_cached_program)).
   rewrite (CachedAdd.Audit.code_matches CachedAdd.Object.assembled_cached_add_correct);exact (proj1(mapped_now _ _ _ I _ _ _ Acc TableAddLayout.image)). }
 destruct(LocatedReturn.checked program (abi_layout true) loc 200 _ _ st last p after
    (TableAddCall.address _ _ _ _ _ E) Image (path _ _ _ W) (did_return Cert) Frame) as [ws [Run [Inner Memory]]].
 assert (Safe:confined (writable e) ws).
 { eapply Forall_impl;[|exact Inner];intros w OK x X;specialize(OK x X).
   change (CallLayout.point_ptr e<=x<CallLayout.point_ptr e+1280 \/ CallLayout.stage e-1344-16<=x<PointFrame.entry_rsp loc TableAddLayout.pad) in OK.
   unfold loc in OK;rewrite TableAddLayout.entry_sp in OK;pose proof(CallLayout.depth e P).
   apply (permits _ P);destruct OK as [A|B];[right;left;exact A|left;unfold span;lia]. }
 set (v:=export_state loc last after);set (q:=Cursor (caller_pc loc) v None (log p++ws)).
 exists q;split;[unfold execute;fold loc st;rewrite Run;reflexivity|constructor].
 - reflexivity.
 - apply append_accounted;[exact Acc|exact Safe|intro x;exact (f_equal (fun m=>m x) Memory)].
 - exact WF.
 - pose proof(restored_stack Cert) as S;change (Some(gpr(fst last) 4%nat)=Some(Ptr(PointFrame.scratch,1344))) in S;injection S as S.
   change (LinkedCalls.decode loc (gpr(fst last) 4%nat)=CallLayout.stage e);rewrite S.
   change (word(CallLayout.stage e-1344+1344)=CallLayout.stage e).
   rewrite Z.sub_add;apply word_fits;destruct(stack_fit _ P) as [L H];pose proof(CallLayout.depth e P);unfold word64;lia.
 - intros r K;change (LinkedCalls.decode loc (gpr(fst last) r)=regs s r);rewrite (SysV.saved_registers Cert r K).
   destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];apply word_fits,W.
 - exact Preserve.
 - exact (computed_output Cert).
Qed.
