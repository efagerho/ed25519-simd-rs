From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks execution.LinkedCalls execution.LinkedRun execution.WordBounds
 execution.LocatedReturn execution.KnownRegisters memory.MemoryTrace memory.FlatMemory memory.ByteMemory memory.WriteTrace memory.BlockWrites abi.SysV.
From Machine Require execution.LocatedEvents.
From Ed25519Simd.Pow2 Require Import Pow2ABI Pow2Memory Pow2Spec Pow2Bytes.
From Ed25519Simd.Pow2 Require Program FrameProof Object Audit ObjectBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage DecoderPower NativeWords.
Local Open Scope Z_scope.

Definition program:=Pow2.Program.pow2_program.
Definition initial pol bias e p:=let s:=machine p in
 entry_from_bytes (locations pol bias e) (regs s) (vectors s) (flag s) (mem s).
Definition execute pol bias e p:=LocatedReturn.execute program abi_layout (locations pol bias e) 1024 (initial pol bias e p) p.
Definition returned pol bias e p r:=let loc:=locations pol bias e in let st:=initial pol bias e p in
 let last:=final_state r in let q:=resumed r in let flat:=mem(machine q) in
 call_result program abi_layout st last (output_initialized program st last)
  (byte_result program loc st last (mem(machine p)) flat)
  (pow2_spec (buffer_words (mem(machine p)) (origin loc input_a))
             (buffer_words (mem(machine p)) (origin loc input_b))
             (buffer_words flat (origin loc Pow2ABI.output))) /\
 callee_returns program abi_layout loc st (mem(machine p)) (ip q) (machine q) /\
 ip q=return_pc bias /\ well_formed(machine q) /\ accounted e (Return.writable e) q.

Lemma search incoming : exists c es,record_path 1024 program abi_layout (initial_control incoming)=Some(c,es).
Proof.
 pose proof(Pow2.FrameProof.frame_checked incoming) as Enough;fold program in Enough.
 destruct(record_path _ _ _ _) as [[c trace]|];[eauto|discriminate].
Qed.
Local Opaque program.

Theorem from_entry pol bias e p : Return.placement e -> loaded pol bias (mem e) (Return.writable e) -> DecoderPower.entry pol bias e p ->
 well_formed(machine p) -> valid_placement (locations pol bias e) DecoderPower.size ->
 exists r,execute pol bias e p=Some r /\ returned pol bias e p r.
Proof.
 intros P I [At [Paid [SP [Out [A [B [Link Signs]]]]]]] W Place.
 set (loc:=locations pol bias e) in *;set (s:=machine p) in *;set (st:=initial pol bias e p).
 assert (Args:concrete_entry loc DecoderPower.size (regs s) (vectors s) (mem s)).
 { constructor;[exact Place|apply W|apply W|apply W| |exact Out|exact A|exact B|].
   - change (regs s 4%nat=KeySquare.link_slot pol e-1928+1928);lia.
   - change (read_word (mem s) (KeySquare.link_slot pol e-1928+1928)=return_pc bias);replace (KeySquare.link_slot pol e-1928+1928) with (KeySquare.link_slot pol e) by ring;exact Link. }
 destruct(Pow2.Audit.run_concrete Pow2.Object.assembled_symbol_correct loc (regs s) (vectors s) (flag s) (mem s) Args) as [final [after Cert]].
 fold st in Cert.
 pose proof (byte_guarantee Cert) as Bytes.
 assert (Known:known_registers (fst st)).
 { intros r;change (Blocks.gpr (fst (entry_from_bytes loc (regs s) (vectors s) (flag s) (mem s))) r<>Unknown).
   pose proof(proj2(proj2(proj2(concrete_entry_representable _ _ _ _ (flag s) _ Args))) r) as Word.
   intro U;rewrite U in Word;discriminate. }
 destruct(lift_return _ _ _ _ _ _ _ _ _ Known (did_return Cert) Bytes) as [Call [WF Keep]].
 assert (Image:MappedFetch.mapped (mem s) (code_base loc) (ProgramLayout.image program)).
 { change (MappedFetch.mapped (mem s) (bias+Decode.DecoderBytes.pow_pc) (ProgramLayout.image Pow2.Program.pow2_program)).
   rewrite (Pow2.Audit.code_matches Pow2.Object.assembled_symbol_correct).
   exact (proj1(BatchScalar.mapped_now _ _ _ I _ _ _ Paid (power_in pol))). }
 destruct(LocatedReturn.checked program abi_layout loc 1024 _ _ st final p after At Image (search _) (did_return Cert) Bytes)
   as [ws [Run [Inside Mem]]].
 assert (Bound:confined (Return.writable e) ws).
 { apply Forall_impl with (P:=permits (writable_byte loc));[|exact Inside].
   intros w R x X;specialize(R x X);left;unfold span.
   change (KeySquare.link_slot pol e+8<=x<KeySquare.link_slot pol e+8+640 \/ KeySquare.link_slot pol e-1928+1928-1936<=x<KeySquare.link_slot pol e-1928+1928-8) in R.
   pose proof(KeySquare.depth pol e);lia. }
 unfold execute;fold loc st;rewrite Run;eexists;split;[reflexivity|].
 unfold returned;fold loc st s;cbn [final_state resumed ip log machine export_state mem].
 split;[exact Cert|split;[exact Call|split;[reflexivity|split;[exact WF|]]]].
 split;[apply Forall_app;exact (conj (proj1 Paid) Bound)|].
 intro x;change (after x=WriteTrace.replay (mem e) (log p++ws) x);rewrite Mem,WriteTrace.replay_app;apply replay_equal, Paid.
Qed.

Record checkpoints:=Checkpoints { before_power:DecoderPower.trace; after_power:result }.
Definition observe pol bias e p bank:=
 bind (DecoderPower.observe bias p bank) (fun args=>option_map (Checkpoints args) (execute pol bias e (exponent_entry args))).
Definition post pol bias e r:=DecoderPower.post pol bias e (before_power r) /\
 returned pol bias e (exponent_entry(before_power r)) (after_power r).
Theorem from_decoder pol bias e p bank : Return.placement e -> loaded pol bias (mem e) (Return.writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> BatchDecode.entry pol bias e p -> well_formed(machine p) ->
 exists r,observe pol bias e p bank=Some r /\ post pol bias e r.
Proof.
 intros P I Al Entry W;destruct(DecoderPower.from_decoder _ _ _ _ bank P I Al Entry) as [args [To Args]].
 destruct(from_entry _ _ _ _ P I (proj1(proj2 Args)) (pow2_entry_words _ _ _ _ W To) (proj2(proj2 Args))) as [r [R Done]].
 exists (Checkpoints args r);split;[unfold observe;rewrite To;cbn [bind];now rewrite R|exact (conj Args Done)].
Qed.
