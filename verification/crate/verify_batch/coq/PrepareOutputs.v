From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.VectorMoves execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.WriteTrace abi.SysV.
From Machine Require execution.MaskedResult.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require PrepareVectors TableUnwind.
Import ListNotations. Local Open Scope Z_scope.

Inductive field:=Pointers | Flags.
Definition off f:=match f with Pointers=>218 | Flags=>242 end.
Definition width f:=match f with Pointers=>7%nat | Flags=>6%nat end.
Definition operand f:=match f with Pointers=>Output 2 13 0 | Flags=>LowWord 0 13 64 end.
Lemma code f : linked PrepareVectors.text [(off f,width f,VectorMove(operand f))].
Proof. destruct f;repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition dest e:=Rows.frame e+768.
Definition event f o e s:=match f with
 | Pointers=>vector (word(o+218)) (dest e) (fun j=>vectors s j 2%nat)
 | Flags=>qword (word(o+242)) (dest e+64) (vectors s 0%nat 0%nat) end.
Definition store bias:=segment (PrepareVectors.origin bias) PrepareVectors.text 1.
Record stored f bias e p q:Prop:=Stored {
 next_pc:ip q=PrepareVectors.origin bias+(off f+Z.of_nat(width f));
 accounted_after:accounted e (writable e) q; valid_words:well_formed(machine q);
 regs_after:regs(machine q)=regs(machine p);
 bytes_after:mem(machine q)=commit (mem(machine p)) (event f (PrepareVectors.origin bias) e (machine p));
 log_after:log q=log p++[event f (PrepareVectors.origin bias) e (machine p)]
}.
Lemma store_checked pol bias e p f : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=PrepareVectors.origin bias+off f -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 13%nat=dest e -> exists q,store bias p=Some q /\ stored f bias e p q.
Proof.
 intros P I PC Acc W D;set (o:=PrepareVectors.origin bias) in *;set (s:=machine p) in *;set (w:=event f o e s).
 destruct(stack_ok _ P) as [[L H] _].
 assert (A:word(regs s 13%nat+0)=dest e /\ word(regs s 13%nat+64)=dest e+64)
  by (rewrite D,Z.add_0_r;split;apply word_fits;unfold dest,Rows.frame,sp,word64 in *;lia).
 set (v:=with_words s (regs s) (commit (mem s) w)).
 assert (R:run 1 (ScalarBytes.fetch o PrepareVectors.text) (State(Running(off f)) s (LinkedRun.carry p))=
   Some(State(Running(off f+Z.of_nat(width f))) v (LinkedRun.carry p),[w])).
 { apply (InstructionRoute.checked _ _ _ (code f));unfold v,w;destruct f;cbn [off width operand follow step loc cf cpu_state option_map event];now rewrite ?(proj1 A),?(proj2 A). }
 assert (Safe:confined (writable e) [w]).
 { constructor;[|constructor];intros x X;left;destruct f;unfold w,event,touches,vector,qword in X;cbn [address size] in X;
   unfold dest,span,Rows.frame,sp in *;lia. }
 destruct(mapped_now _ _ _ I _ _ _ Acc (in_common pol)) as [Map Sep].
 destruct(at_segment _ _ p o _ 1 _ _ _ Acc PC Map Sep R Safe) as [Next Paid].
 eexists;split;[exact Next|constructor];try reflexivity;[exact Paid|exact (segment_wf _ _ _ _ _ W Next)].
Qed.

Definition execute bias p ks:=
 bind (MaskedResult.execute (PrepareVectors.origin bias) PrepareVectors.pointers p ks) (fun '(a,ak)=>
 bind (store bias a) (fun b=>
 bind (MaskedResult.execute (PrepareVectors.origin bias) PrepareVectors.flags b ak) (fun '(c,ck)=>
 option_map (fun q=>(q,ck)) (store bias c)))).
Record result pol bias e caller p q:Prop:=Result {
 pc:ip q=PrepareVectors.origin bias+248;
 writes:accounted e (writable e) q; words:well_formed(machine q);
 registers:regs(machine q)=regs(machine p);
 table_ptr:forall j,(j<8)%nat -> read_word (mem(machine q)) (dest e+8*Z.of_nat j)=
   if Z.testbit (regs(machine caller) 15%nat) (Z.of_nat j)
   then scratch e+PrepareChunk.Caller.table_offset j else regs(machine caller) 12%nat;
 eligibility:forall j,(j<8)%nat -> mem(machine q)(dest e+64+Z.of_nat j)=Z.b2z(Z.testbit (regs(machine caller) 14%nat) (Z.of_nat j));
 surrounding:preserved (fun x=>~span (dest e) 72 x) (mem(machine p)) (mem(machine q));
 parent:TableUnwind.returned pol bias e caller p
}.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked pol bias e before caller p ks : placement e -> loaded pol bias (mem e) (writable e) ->
 EligibleLanes.post pol bias e before caller -> TableUnwind.returned pol bias e caller p ->
 exists q bank,execute bias p ks=Some(q,bank) /\ result pol bias e caller p q.
Proof.
 intros P I E T;pose proof(TableUnwind.registers _ _ _ _ _ T) as G.
 assert (D:regs(machine p) 13%nat=dest e) by (rewrite G by (cbn;tauto);exact (EligibleLanes.prepared_address _ _ _ _ _ E)).
 destruct(PrepareVectors.pointer_values pol bias e p ks P I (TableUnwind.pc _ _ _ _ _ T)
  (TableUnwind.writes _ _ _ _ _ T) (TableUnwind.words _ _ _ _ _ T)
  ltac:(rewrite G by (cbn;tauto);exact (EligibleLanes.scratch_base _ _ _ _ _ E))) as [a [ak [PointerRun [AP [A V]]]]].
 destruct(store_checked pol bias e a Pointers P I AP (MaskedResult.accounted_after _ _ _ _ A) (MaskedResult.words_after _ _ _ _ A)
   ltac:(rewrite (MaskedResult.registers_after _ _ _ _ A);exact D)) as [b [First B]].
 destruct(PrepareVectors.flag_values pol bias e b ak I (next_pc _ _ _ _ _ B) (accounted_after _ _ _ _ _ B) (valid_words _ _ _ _ _ B))
    as [c [ck [FlagsRun [CP [C F]]]]].
 assert (Back:regs(machine c)=regs(machine p)) by
   (now rewrite (MaskedResult.registers_after _ _ _ _ C),(regs_after _ _ _ _ _ B),(MaskedResult.registers_after _ _ _ _ A)).
 destruct(store_checked pol bias e c Flags P I CP (MaskedResult.accounted_after _ _ _ _ C) (MaskedResult.words_after _ _ _ _ C)
    ltac:(now rewrite Back)) as [q [Second Q]].
 exists q,ck;split;[unfold execute;rewrite PointerRun;cbn [bind];rewrite First;cbn [bind];rewrite FlagsRun;cbn [bind];now rewrite Second|constructor].
 - exact (next_pc _ _ _ _ _ Q).
 - exact (accounted_after _ _ _ _ _ Q).
 - exact (valid_words _ _ _ _ _ Q).
 - now rewrite (regs_after _ _ _ _ _ Q),Back.
 - intros j J;rewrite (bytes_after _ _ _ _ _ Q);unfold event,commit;cbn [qword address size payload].
   transitivity (read_word (mem(machine c)) (dest e+8*Z.of_nat j)).
   + apply preserved_read with (outside:=fun x=>~span (dest e+64) 8 x);
     [intros x X;apply write_outside,X|intros n N;change (0<=n<8) in N;unfold span;lia].
   + rewrite (MaskedResult.memory_after _ _ _ _ C),(bytes_after _ _ _ _ _ B).
     unfold event,commit;cbn [vector address size payload];rewrite write_read_vector by (exact J || apply (MaskedResult.words_after _ _ _ _ A),J).
     rewrite V by exact J;rewrite (G 15%nat),(G 12%nat) by (cbn;tauto);reflexivity.
 - intros j J;rewrite (bytes_after _ _ _ _ _ Q);unfold event,commit;cbn [qword address size payload].
   rewrite write_at by lia;rewrite F by exact J;rewrite (regs_after _ _ _ _ _ B),(MaskedResult.registers_after _ _ _ _ A),G by (cbn;tauto);reflexivity.
 - intros x X;rewrite (bytes_after _ _ _ _ _ Q);unfold event,commit;cbn [qword address size payload];rewrite write_outside by (unfold span in X;lia).
   rewrite (MaskedResult.memory_after _ _ _ _ C),(bytes_after _ _ _ _ _ B);unfold event,commit;cbn [vector address size payload].
   rewrite write_outside by (unfold span in X;lia);now rewrite (MaskedResult.memory_after _ _ _ _ A).
 - exact T.
Qed.

Definition observe bias p ks:=bind (TableUnwind.observe bias p ks) (fun '(a,ak)=>execute bias a ak).

Theorem from_eligible pol bias e before p ks : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q bank a,observe bias p ks=Some(q,bank) /\ result pol bias e p a q.
Proof.
 intros P I Al E Live;destruct(TableUnwind.from_eligible _ _ _ _ _ ks P I Al E Live) as [a [ak [Run A]]].
 destruct(checked _ _ _ _ _ _ ak P I E A) as [q [bank [Emit Post]]].
 exists q,bank,a;split;[unfold observe;rewrite Run;exact Emit|exact Post].
Qed.
End Iteration.
