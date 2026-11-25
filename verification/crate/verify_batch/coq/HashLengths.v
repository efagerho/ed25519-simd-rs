From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require execution.MaskedResult.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require PreparedReturn.
Import ListNotations. Local Open Scope Z_scope.

Definition branch:list line:=[(385,2%nat,Test32 0);(387,6%nat,Branch Equal (541-393))].
Definition mask_ops:=[MaskedResult.WidenBytes 0 4 832;MaskedResult.TestQ 1 0 0;MaskedResult.ZeroRow 0 1 4 704].
Definition bound text:=linked text branch /\ MaskedResult.assemble 393 mask_ops=Some(firstn 22 (skipn 393 text)) /\ (415<length text)%nat.
Definition execute o text p ks:=bind (segment o text 2 p) (fun a=>MaskedResult.execute o mask_ops a ks).
Definition tested p:=Cursor (ip p) (with_zf (machine p) false) (Some false) (log p).
Definition enabled e s j:=negb(mem s (PrepareOutputs.dest e+64+Z.of_nat j)=?0).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition length e s j:=if enabled e s j then descriptor (mem e) (regs e 7%nat) (BatchWindow.row e j) 24 else 0.

Theorem checked o text e p ks : bound text -> placement e -> MemoryGeometry.fits64 o (Z.of_nat(List.length text)) ->
 mapped (mem e) o text -> (forall x,o<=x<o+Z.of_nat(List.length text) -> ~writable e x) ->
 ip p=o+385 -> regs(machine p) 0%nat=1 -> regs(machine p) 4%nat=Rows.frame e ->
 accounted e (writable e) p -> well_formed(machine p) -> WrapperInputs.layout e (mem(machine p)) ->
 exists q bank,execute o text p ks=Some(q,bank) /\ ip q=o+415 /\ MaskedResult.unchanged e (writable e) (tested p) q /\
 forall j,(j<8)%nat -> vectors(machine q) j 0%nat=length e (machine p) j.
Proof.
 intros [Br [Enc Bound]] P [OL OH] Image Sep PC AX SP Acc W Layout;set (s:=machine p) in *.
 set (t:=with_zf s false).
 assert (R:run 2 (ScalarBytes.fetch o text) (State(Running 385) s (LinkedRun.carry p))=Some(State(Running 393) t (Some false),[])).
 { apply (InstructionRoute.checked _ _ _ Br);cbn [branch follow loc cpu_state cf step eval_condition flag with_zf option_map];now rewrite AX. }
 pose proof(image_after e (writable e) p o text Acc Image Sep) as Map.
 destruct(at_segment _ _ p o _ 2 385 _ _ Acc PC Map Sep R (Forall_nil _)) as [First A].
 set (a:=LinkedRun.finish o p (State(Running 393) t (Some false),[])) in *.
 set (m:=fun j=>mem s (word(regs s 4%nat+832)+Z.of_nat j)).
 set (k:=MaskedResult.set_mask ks 1 8 (fun j=>negb(Z.land (m j) (m j)=?0))).
 set (v:=vector_dest (vector_dest t 0 m) 0 (fun j=>if k 1%nat j then vector_load s j 4 704 else 0)).
 assert (Eval:MaskedResult.evaluate o (machine a) ks mask_ops=Some(v,k)) by reflexivity.
 destruct(MaskedResult.mapped_slice o text e (writable e) a ks 393 22 mask_ops v k OL OH Map eq_refl A
     (segment_wf _ _ _ _ _ W First) Bound Enc Eval) as [q [Block [End [CPU U]]]].
 exists q,k;split;[unfold execute;rewrite First;exact Block|split;[exact End|split]].
 - constructor;[exact (MaskedResult.accounted_after _ _ _ _ U)|exact (MaskedResult.words_after _ _ _ _ U)|
     exact (MaskedResult.registers_after _ _ _ _ U)|exact (MaskedResult.memory_after _ _ _ _ U)| |].
   + rewrite (MaskedResult.history _ _ _ _ U);apply app_nil_r.
   + (* TEST clears CF before the vector instructions. *)
     exact (MaskedResult.carry_after _ _ _ _ U).
 - intros j J;rewrite CPU;change ((if k 1%nat j then vector_load s j 4 704 else 0)=length e s j).
   unfold k,MaskedResult.set_mask,put;cbn [Nat.eqb];rewrite (proj2(Nat.ltb_lt j 8) J);cbn [andb];rewrite Z.land_diag.
   destruct(stack_ok _ P) as [[L H] _].
   unfold length,enabled,m,PrepareOutputs.dest,vector_load;rewrite SP,!word_fits by (unfold word64,Rows.frame,sp in *;lia).
   replace (Rows.frame e+768+64) with (Rows.frame e+832) by ring;destruct(negb (_=?0));[|reflexivity].
   apply (WrapperInputs.message _ _ Layout true j J).
Qed.
End Iteration.
