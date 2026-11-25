From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Blocks execution.LinkedCalls execution.LinkedRun execution.LocatedReturn
 execution.KnownRegisters execution.WordSemantics execution.WordBounds memory.MemoryTrace memory.ByteMemory memory.BlockWrites memory.FlatMemory memory.WriteTrace abi.SysV.
From Ed25519Simd.CachedAdd Require Import CachedAddABI CachedAddMemory CachedAddSpec CachedAddBytes.
From Ed25519Simd.CachedAdd Require Program FrameProof Audit Object.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableAddCall.
Import ListNotations. Local Open Scope Z_scope.

Definition program:=Program.add_cached_program.
Definition initial pol bias e p:=let s:=machine p in
 entry_from_bytes true true (TableAddLayout.layout pol bias e) TableAddLayout.pad (regs s) (vectors s) (flag s) (mem s).
Definition execute pol bias e p:=option_map resumed (LocatedReturn.execute program (abi_layout true)
 (TableAddLayout.layout pol bias e) 200 (initial pol bias e p) p).
Record post pol bias e p q:Prop:=Post {
 address:ip q=TableAddLayout.back bias;
 writes:accounted e (Return.writable e) q;
 words:well_formed(machine q);
 stack:regs(machine q) 4%nat=TableAddLayout.stage pol e;
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 outside:preserved (fun x=>~PointFrame.writable_byte (TableAddLayout.layout pol bias e) TableAddLayout.pad x)
       (mem(machine p)) (mem(machine q));
 point_result:cached_add_spec true true
   (buffer_words (mem(machine p)) (TableEntry.point e)) (buffer_words (mem(machine p)) (TableAddLayout.stage pol e))
   (buffer_words (mem(machine q)) (TableEntry.point e))
}.

Lemma path pol bias e p : well_formed(machine p) ->
 exists c es,record_path 200 program (abi_layout true) (fst(initial pol bias e p))=Some(c,es).
Proof.
 intro W;unfold initial,entry_from_bytes;cbn [fst].
 pose proof(CachedAdd.FrameProof.frame_checked true true (Control Caller (fun r=>Int(regs(machine p) r)) (flag(machine p)) (fun _=>None))
   TableAddLayout.pad (regs(machine p) 5%nat) ltac:(right;right;right;left;reflexivity) (proj1 W 5%nat)) as H.
 fold program in H;destruct(record_path _ _ _ _) as [[c es]|];[eauto|discriminate].
Qed.
Local Opaque CachedAdd.Program.add_cached_program.

Theorem checked pol bias e a p : Return.placement e -> loaded pol bias (mem e) (Return.writable e) ->
 TableAddCall.entry pol bias e a p -> exists q,execute pol bias e p=Some q /\ post pol bias e p q.
Proof.
 intros P I E;set (loc:=TableAddLayout.layout pol bias e);set (s:=machine p);set (st:=initial pol bias e p).
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
   rewrite (CachedAdd.Audit.code_matches CachedAdd.Object.assembled_cached_add_correct);exact (proj1(mapped_now _ _ _ I _ _ _ Acc (TableAddLayout.image pol))). }
 destruct(LocatedReturn.checked program (abi_layout true) loc 200 _ _ st last p after
    (TableAddCall.address _ _ _ _ _ E) Image (path _ _ _ _ W) (did_return Cert) Frame) as [ws [Run [Inner Memory]]].
 assert (Safe:confined (Return.writable e) ws).
 { eapply Forall_impl;[|exact Inner];intros w OK x X;specialize(OK x X).
   change (TableEntry.point e<=x<TableEntry.point e+1280 \/ TableAddLayout.stage pol e-1344-16<=x<PointFrame.entry_rsp loc TableAddLayout.pad) in OK.
   unfold loc in OK;rewrite TableAddLayout.entry_sp in OK;pose proof(TableAddLayout.stack pol e).
   destruct OK as [A|B];[right;left;unfold Return.span,TableEntry.point in *|left;unfold Return.span];lia. }
 set (v:=export_state loc last after);set (q:=Cursor (caller_pc loc) v None (log p++ws)).
 exists q;split;[unfold execute;fold loc st;rewrite Run;reflexivity|constructor].
 - reflexivity.
 - apply append_accounted;[exact Acc|exact Safe|intro x;exact (f_equal (fun m=>m x) Memory)].
 - exact WF.
 - pose proof(restored_stack Cert) as S;change (Some(gpr(fst last) 4%nat)=Some(Ptr(PointFrame.scratch,1344))) in S;injection S as S.
   change (LinkedCalls.decode loc (gpr(fst last) 4%nat)=TableAddLayout.stage pol e);rewrite S.
   change (word(TableAddLayout.stage pol e-1344+1344)=TableAddLayout.stage pol e).
   rewrite Z.sub_add;apply word_fits;destruct(stack_ok _ P) as [[L H] _];pose proof(TableAddLayout.stack pol e);unfold word64;lia.
 - intros r K;change (LinkedCalls.decode loc (gpr(fst last) r)=regs s r);rewrite (SysV.saved_registers Cert r K).
   destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];apply word_fits,W.
 - exact Preserve.
 - exact (computed_output Cert).
Qed.
