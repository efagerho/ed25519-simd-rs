From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Blocks execution.LinkedCalls execution.LinkedRun
 execution.LocatedReturn execution.MappedFetch execution.WordBounds execution.KnownRegisters
 memory.FlatMemory memory.MemoryTrace memory.ByteMemory memory.WriteTrace abi.CallFrame abi.SysV.
From Ed25519Simd Require Import PointResults.
From Ed25519Simd.LadderStep Require Import Callees.
From Ed25519Simd.Double4 Require FrameProof.
From Ed25519Simd.CachedAdd Require FrameProof.
Local Open Scope Z_scope.

(* Both leaves enter on the caller's byte memory. Each successful run
   appends the stores at their instruction addresses to the incoming log. *)
Definition double pc sc pad p:=
 let loc:=call_loc sc pc (machine p) in let s:=machine p in
 option_map resumed (LocatedReturn.execute Double4.Program.double4_program
  Double4ABI.abi_layout loc 200 (D.entry_from_bytes loc pad (regs s) (vectors s) (flag s) (mem s)) p).
Definition add pc sc pad f a p:=
 let loc:=call_loc sc pc (machine p) in let s:=machine p in
 option_map resumed (LocatedReturn.execute CachedAdd.Program.add_cached_program
  (CachedAddABI.abi_layout a) loc 200 (A.entry_from_bytes f a loc pad (regs s) (vectors s) (flag s) (mem s)) p).
Record result sc p q:Prop:=Result {
 flags:carry q=None;
 back:ip q=read_word (mem(machine p)) (regs(machine p) 4%nat);
 frame:call_post sc (machine p) (machine q);
 writes:exists ws,log q=log p++ws /\ confined (callee_writable sc (machine p)) ws /\
   mem(machine q)=WriteTrace.replay (mem(machine p)) ws
}.

Lemma returned sc pc pad p out ws :
 let s:=machine p in let loc:=call_loc sc pc s in
 regs s 4%nat=sc+1288+pad -> call_post sc s out ->
 confined (PointFrame.writable_byte loc pad) ws -> mem out=WriteTrace.replay (mem s) ws ->
 result sc p (Cursor (caller_pc loc) out None (log p++ws)).
Proof.
 intros s loc SP Frame Safe M;constructor;[reflexivity|reflexivity|exact Frame|].
 exists ws;split;[reflexivity|split;[|exact M]].
 eapply Forall_impl;[|exact Safe];intros w OK x X;specialize(OK x X).
 change (regs s 7%nat<=x<regs s 7%nat+1280 \/ sc-16<=x<sc+1288+pad) in OK.
 change (regs s 7%nat<=x<regs s 7%nat+1280 \/ sc-16<=x<regs s 4%nat);now rewrite SP.
Qed.

Lemma double_run dp sc pad p :
 let s:=machine p in let loc:=call_loc sc dp s in ip p=dp ->
 mapped (mem s) dp doubling_image -> well_formed s -> regs s 4%nat=sc+1288+pad ->
 word64(regs s 4%nat+8) -> Double4Memory.valid_placement loc dsize pad ->
 exists q,double dp sc pad p=Some q /\ result sc p q /\
 double_spec defer_double (point_words s) (buffer_words(mem(machine q))(regs s 7%nat)) /\
 forall ap,dispatch dp ap sc pad dp s (ip q) (machine q).
Proof.
 intros s loc PC Map W SP End Place.
 assert (E:D.concrete_entry loc dsize pad (regs s)(vectors s)(mem s)).
 { constructor;try apply W;try assumption;try reflexivity;change(read_word(mem s)(sc+1288+pad)=read_word(mem s)(regs s 4%nat));now rewrite SP. }
 set (st:=D.entry_from_bytes loc pad (regs s) (vectors s) (flag s) (mem s)).
 destruct (Double4.Audit.run_concrete Double4.Object.assembled_double4_correct loc pad _ _ (flag s) _ E)
    as [_ [last [after Cert]]];fold st in Cert.
 pose proof(did_return Cert) as Ret;pose proof(byte_guarantee Cert) as Bytes.
 assert (Path:exists c es,record_path 200 Double4.Program.double4_program Double4ABI.abi_layout (fst st)=Some(c,es)).
 { pose proof(Double4.FrameProof.frame_checked (Control Caller (fun r=>Int(regs s r)) (flag s) (fun _=>None))
      pad (regs s 5%nat) (proj1 Place) (proj1 W 5%nat)) as H;unfold st,D.entry_from_bytes;cbn [fst].
   destruct(record_path _ _ _ _) as [[c es]|];[eauto|discriminate]. }
 destruct(LocatedReturn.checked _ _ loc 200 _ _ st last p after PC Map Path Ret Bytes) as [ws [Run [Safe M]]].
 destruct(D.concrete_entry_representable _ _ _ _ _ (flag s) _ E)as[_[_[_ Entry]]].
 fold st in Entry;use_return Ret Bytes Entry.
 exists (Cursor (caller_pc loc) (export_state loc last after) None (log p++ws)).
 split;[unfold double;fold s loc st;now rewrite Run|split;[|split;[exact (computed_output Cert)|intro ap;constructor;exact Hrun]]].
 apply (returned sc dp pad p _ ws SP);[|exact Safe|exact M].
 eapply project_return;try eassumption;try apply W;[reflexivity|apply (restored_stack Cert)|apply (saved_registers Cert)].
Qed.

Lemma add_run ap sc pad f a p :
 let s:=machine p in let loc:=call_loc sc ap s in ip p=ap ->
 mapped (mem s) ap addition_image -> well_formed s -> regs s 4%nat=sc+1288+pad ->
 word64(regs s 4%nat+8) -> regs s 2%nat=CachedAddABI.flag_word f -> regs s 1%nat=CachedAddABI.flag_word a ->
 CachedAddMemory.valid_placement a loc asize pad ->
 exists q,add ap sc pad f a p=Some q /\ result sc p q /\
 CachedAddSpec.cached_add_spec f a (point_words s) (buffer_words(mem s)(regs s 6%nat))
   (buffer_words(mem(machine q))(regs s 7%nat)) /\
 forall dp,dispatch dp ap sc pad ap s (ip q) (machine q).
Proof.
 intros s loc PC Map W SP End F Aflag Place.
 assert (E:A.concrete_entry f a loc asize pad (regs s)(vectors s)(mem s)).
 { constructor;try apply W;try assumption;try reflexivity;change(read_word(mem s)(sc+1288+pad)=read_word(mem s)(regs s 4%nat));now rewrite SP. }
 set (st:=A.entry_from_bytes f a loc pad (regs s) (vectors s) (flag s) (mem s)).
 destruct (CachedAdd.Audit.run_concrete CachedAdd.Object.assembled_cached_add_correct f a loc pad _ _ (flag s) _ E)
    as [_ [last [after Cert]]];fold st in Cert.
 pose proof(did_return Cert) as Ret;pose proof(byte_guarantee Cert) as Bytes.
 assert (Path:exists c es,record_path 200 CachedAdd.Program.add_cached_program (CachedAddABI.abi_layout a) (fst st)=Some(c,es)).
 { pose proof(CachedAdd.FrameProof.frame_checked f a (Control Caller (fun r=>Int(regs s r)) (flag s) (fun _=>None))
      pad (regs s 5%nat) (proj1(proj1 Place)) (proj1 W 5%nat)) as H;unfold st,A.entry_from_bytes;cbn [fst].
   destruct(record_path _ _ _ _) as [[c es]|];[eauto|discriminate]. }
 destruct(LocatedReturn.checked _ _ loc 200 _ _ st last p after PC Map Path Ret Bytes) as [ws [Run [Safe M]]].
 destruct(A.concrete_entry_representable _ _ _ _ _ _ _ (flag s) _ E)as[_[_[_ Entry]]].
 fold st in Entry;use_return Ret Bytes Entry.
 exists (Cursor (caller_pc loc) (export_state loc last after) None (log p++ws)).
 split;[unfold add;fold s loc st;now rewrite Run|split;[|split;[exact (computed_output Cert)|intro dp;eapply run_add;[exact F|exact Aflag|exact Hrun]]]].
 apply (returned sc ap pad p _ ws SP);[|exact Safe|exact M].
 eapply project_return;try eassumption;try apply W;[reflexivity|apply (restored_stack Cert)|apply (saved_registers Cert)].
Qed.
