From Coq Require Import List ZArith Bool Lia.
From Machine Require Import abi.SysV execution.Blocks execution.WordBounds execution.WordSemantics execution.LinkedCalls
 execution.LinkedRun execution.LocatedReturn memory.ByteMemory memory.FlatMemory memory.MemoryTrace.
From Ed25519Simd.Pow2 Require Import Pow2ABI Pow2Bytes Pow2Memory.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare DecoderPower PowerWrites.
Import ListNotations. Local Open Scope Z_scope.

(* Resume the decoder at its own continuation with its still-live registers
   and the memory left by the block interpreter. *)
Definition ready pol bias e q:=
 ip q=return_pc bias /\ accounted e (Return.writable e) q /\ well_formed(machine q) /\
 regs(machine q) 4%nat=link_slot pol e+8 /\ decoder_registers pol e (machine q) /\
 key_signs e (machine q) /\ forall j,(j<8)%nat ->
 Z.testbit (regs(machine q) 14%nat) (Z.of_nat j)=Z.testbit (original_encoding true e j) 255.

Theorem after_return pol bias e p r : Return.placement e -> DecoderPower.entry pol bias e p -> well_formed(machine p) ->
 returned pol bias e p r -> ready pol bias e (resumed r) /\
 preserved (fun x=>~writable_byte (locations pol bias e) x) (mem(machine p)) (mem(machine(resumed r))).
Proof.
 intros P [At [Paid [SP [Out [A [B [Link [Key [Sig [BX [BP Count]]]]]]]]]]] Before [Cert [Call [End [WF Done]]]].
 set (loc:=locations pol bias e) in *;set (st:=initial pol bias e p) in *;set (q:=resumed r) in *.
 destruct Call as [last [fuel [events [RT [_ [_ [_ Export]]]]]]].
 assert (E:last=final_state r) by exact (return_unique _ _ _ _ _ RT (did_return Cert));subst last.
 assert (G:forall i,regs(machine q) i=LinkedCalls.decode loc (gpr(fst(final_state r)) i)).
 { intro i;rewrite Export;reflexivity. }
 assert (Kept:forall i,In i sysv_saved -> regs(machine q) i=regs(machine p) i).
 { intros i InReg;rewrite G,(SysV.saved_registers Cert i InReg);cbn [sysv_saved In] in InReg;
   destruct InReg as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];apply word_fits,Before. }
 assert (Stack:regs(machine q) 4%nat=link_slot pol e+8).
 { pose proof(restored_stack Cert) as R.
   change (Some (gpr(fst(final_state r)) 4%nat)=Some(Ptr (Pow2ABI.stack,1936))) in R;injection R as R.
   rewrite G,R;change (word(link_slot pol e-1928+1936)=link_slot pol e+8).
   pose proof(depth pol e);destruct(Return.stack_ok _ P) as [[Lo Hi] _];rewrite word_fits by (unfold word64;lia);lia. }
 split.
 - split;[exact End|split;[exact Done|split;[exact WF|split;[exact Stack|]]]].
   unfold decoder_registers,key_signs;split;[rewrite !Kept by (cbn;tauto);tauto|].
   split;intros j J;rewrite Kept by (cbn;tauto);[apply Key|apply Sig];exact J.
 - exact (proj1(proj2(proj2(proj2(byte_guarantee Cert))))).
Qed.
