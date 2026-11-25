From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions isa.VectorMoves execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.LinkedRun execution.ScalarBytes execution.ScalarWords execution.InstructionRoute execution.MappedFetch
 execution.MaskedResult memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterLoad.
Import ListNotations. Local Open Scope Z_scope.

Definition ops:=[FromGpr 2 1;AndWord 1 1 2;MaskBytes 0 1;LoadLowQ 1 6 0;AndNotXmm 0 0 1].
Definition store:list line:=[(539,4%nat,VectorMove(LowWord 0 6 0))].
Lemma image:assemble 517 ops=Some(firstn 22 (skipn 517 FilterLoad.text)) /\ linked FilterLoad.text store.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias p ks:=let o:=bias+FilterLoad.site in bind (MaskedResult.execute o ops p ks)
 (fun '(a,k)=>option_map (fun q=>(q,k)) (segment o FilterLoad.text 1 a)).
Definition flag_ptr e:=PrepareOutputs.dest e+64.
Definition clears s (ks:MaskTransfer.bank) j:=ks 1%nat j && Z.testbit (regs s 1%nat) (Z.of_nat j).
Lemma byte_bit w j k : 0<=j -> 0<=k<8 ->
 Z.testbit (word_byte w j) k=Z.testbit w (k+8*j).
Proof. intros J K;unfold word_byte;change 256 with (2^8);rewrite Z.mod_pow2_bits_low,<-Z.shiftr_div_pow2,Z.shiftr_spec by lia;reflexivity. Qed.
Lemma clear_byte f w j : (j<8)%nat -> word64 w ->
 word_byte (word(Z.land (Z.lnot(mask_qword f 0)) w)) (Z.of_nat j)=if f j then 0 else word_byte w (Z.of_nat j).
Proof.
 intros J W;rewrite word_fits by (apply and_word,W).
 assert (M:word_byte (mask_qword f 0) (Z.of_nat j)=if f j then 255 else 0).
 { unfold mask_qword;rewrite read_word_byte by (apply mask_memory || lia);rewrite Z.add_0_l,Nat2Z.id;reflexivity. }
 apply Z.bits_inj;intro i;destruct (Z_lt_ge_dec i 0).
 - rewrite !Z.testbit_neg_r by lia;reflexivity.
 - destruct (Z_lt_ge_dec i 8).
   + rewrite byte_bit,Z.land_spec,Z.lnot_spec,<-(byte_bit (mask_qword f 0) _ i),M by lia;destruct(f j).
     * change 255 with (Z.ones 8);rewrite Z.ones_spec_low,Z.bits_0 by lia;reflexivity.
     * rewrite Z.bits_0,byte_bit by lia;reflexivity.
   + destruct(f j);unfold word_byte;change 256 with (2^8);rewrite !Z.mod_pow2_bits_high,?Z.bits_0 by lia;reflexivity.
Qed.

Record result bias e p q ks:Prop:=Result {
 pc:ip q=bias+FilterLoad.site+543; writes:accounted e (writable e) q; words:well_formed(machine q);
 registers:regs(machine q)=regs(machine p);
 outside:preserved (fun x=>~span (flag_ptr e) 8 x) (mem(machine p)) (mem(machine q));
 flags:forall j,(j<8)%nat -> mem(machine q)(flag_ptr e+Z.of_nat j)=
     if clears (machine p) ks j then 0 else mem(machine p)(flag_ptr e+Z.of_nat j)
}.

Theorem checked bias e p ks : placement e -> loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+FilterLoad.site+517 -> accounted e (writable e) p -> well_formed(machine p) -> regs(machine p) 6%nat=flag_ptr e ->
 exists q bank,execute bias p ks=Some(q,bank) /\ result bias e p q ks.
Proof.
 intros P I PC Acc W SI;set (o:=bias+FilterLoad.site) in *;set (s:=machine p) in *.
 destruct(mapped_now _ _ _ I _ _ _ Acc StrictFilterCall.in_filter) as [Map Sep].
 destruct(proj1(symbols _ _ _ _ I _ _ StrictFilterCall.in_filter)) as [L H].
 set (k2:=set_mask ks 2 16 (fun j=>Z.testbit (regs s 1%nat) (Z.of_nat j))).
 set (k:=set_mask k2 1 16 (fun j=>k2 1%nat j && k2 2%nat j)).
 set (v:=vector_dest s 0 (mask_qword(k 1%nat))).
 set (w:=vector_dest v 1 (fun j=>if (j=?0)%nat then read_word (mem v) (word(regs v 6%nat+0)) else 0)).
 set (t:=vector_dest w 0 (fun j=>if (j<?2)%nat then word(Z.land (Z.lnot(vectors w j 0%nat)) (vectors w j 1%nat)) else 0)).
 assert (Eval:evaluate o s ks ops=Some(t,k)) by reflexivity.
 destruct(mapped_slice o FilterLoad.text e (writable e) p ks 517 22 ops t k L H Map PC Acc W ltac:(change (517+22<551)%nat;lia)
   (proj1 image) Eval) as [a [Sim [At [CPU U]]]].
 pose proof(accounted_after _ _ _ _ U) as Paid;pose proof(registers_after _ _ _ _ U) as G;pose proof(memory_after _ _ _ _ U) as M.
 set (payload:=vectors t 0%nat 0%nat);set (ev:=qword (word(o+539)) (flag_ptr e) payload).
 assert (Fit:word64(flag_ptr e)) by (rewrite <-SI;apply W).
 set (last:=with_words (machine a) (regs(machine a)) (commit (mem(machine a)) ev)).
 assert (One:run 1 (ScalarBytes.fetch o FilterLoad.text) (State(Running 539) (machine a) (carry a))=Some(State(Running 543) last (carry a),[ev])).
 { apply (InstructionRoute.checked _ _ _ (proj2 image));cbn [store follow loc cpu_state cf ScalarBytes.step option_map].
   assert (Addr:word(regs(machine a) 6%nat+0)=flag_ptr e) by (rewrite G;fold s;rewrite SI,Z.add_0_r;apply word_fits,Fit).
   unfold last,ev,payload;rewrite Addr,CPU;reflexivity. }
 assert (Safe:confined (writable e) [ev]) by (constructor;[intros x X;left;change (flag_ptr e<=x<flag_ptr e+8) in X;unfold flag_ptr,PrepareOutputs.dest,Rows.frame,sp,span in *;lia|constructor]).
 destruct(at_segment _ _ a o FilterLoad.text 1 539 _ _ Paid At ltac:(now rewrite M) Sep One Safe) as [Run All].
 do 2 eexists;split;[unfold execute;fold o;rewrite Sim;cbn [bind];now rewrite Run|constructor];[reflexivity|exact All|exact (segment_wf _ _ _ _ _ (words_after _ _ _ _ U) Run)|exact G| |].
 - intros x X;change (commit (mem(machine a)) ev x=mem s x);rewrite M;apply write_outside,X.
 - intros j J;change (commit (mem(machine a)) ev (flag_ptr e+Z.of_nat j)=if clears s ks j then 0 else mem s (flag_ptr e+Z.of_nat j));unfold ev,commit;cbn [address size WriteTrace.payload qword];rewrite write_at by lia.
   unfold payload,t,w,v;change (word_byte (word(Z.land (Z.lnot(mask_qword(k 1%nat) 0)) (read_word (mem s) (word(regs s 6%nat+0))))) (Z.of_nat j)=if clears s ks j then 0 else mem s (flag_ptr e+Z.of_nat j)).
   rewrite SI,Z.add_0_r,(word_fits _ Fit),clear_byte by (exact J || apply read_word_bound,W).
   unfold k,k2,set_mask,put;cbn [Nat.eqb];rewrite (proj2(Nat.ltb_lt j 16) ltac:(lia));cbn [andb];unfold clears.
   destruct(ks 1%nat j && Z.testbit (regs s 1%nat) (Z.of_nat j));[reflexivity|apply read_word_byte;[apply W|lia]].
Qed.
