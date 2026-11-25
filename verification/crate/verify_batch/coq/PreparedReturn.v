From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.FlatMemory memory.ByteMemory memory.WriteTrace.
From Machine Require execution.ScalarRefinement.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require PreparedInputs PrepareUnwind PreparedTables.
Import ListNotations. Local Open Scope Z_scope.

Definition suffix:list line:=[(248,3%nat,ZeroUpper);(251,5%nat,OneEax);(256,2%nat,Jump 2)]++skipn 2 PrepareUnwind.common_reject.
Lemma linked_suffix:linked PrepareVectors.text suffix.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (PrepareVectors.origin bias) PrepareVectors.text 10.
Definition destination pol bias entry:=match pol with Zip215=>word(entry+Image.offset Image.Prepared) | Dalek=>bias+PrepareNative.strict+9 end.

Lemma raw o s c top : 112<=top -> top+8<2^64 -> regs s 4%nat=top-104 ->
 exists last,run 10 (ScalarBytes.fetch o PrepareVectors.text) (State(Running 248) s c)=Some(last,[]) /\
 loc last=Returned(word(read_word (mem s) top)) /\ regs(cpu_state last) 4%nat=top+8 /\ regs(cpu_state last) 0%nat=1 /\
 mem(cpu_state last)=mem s /\ regs(cpu_state last) 5%nat=regs s 5%nat /\
 forall i r,nth_error ([3;12;13;14;15]%nat) i=Some r -> regs(cpu_state last) r=read_word (mem s) (top-8*(1+Z.of_nat i)).
Proof.
 intros L H SP;eexists;split;[apply (InstructionRoute.checked _ _ _ linked_suffix);reflexivity|].
 cbn [suffix PrepareUnwind.common_reject skipn app follow step loc cpu_state cf option_map pop caller_step stack_step
      result_regs result_mem apply_stack advance_rsp stack_top effective set set_regs with_words with_zf regs mem put Nat.eqb].
 unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite SP;
 repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64;lia)) end.
 cbn [target_ip result_regs result_mem];repeat split;try lia;try solve [repeat f_equal;ring].
 intros i r Eq;destruct i as [|[|[|[|[|i]]]]];try (injection Eq as <-;f_equal;ring);destruct i;discriminate.
Qed.

Record result pol bias entry e q:Prop:=Result {
 pc:ip q=destination pol bias entry; stack:regs(machine q) 4%nat=common_top pol e+8;
 success:regs(machine q) 0%nat=1; writes:accounted e (writable e) q; words:well_formed(machine q);
 operands:PreparedInputs.operands e (machine q);
 caller:EligibilityFrame.context pol bias entry e q;
 scratch_reg:regs(machine q) 15%nat=Return.scratch e;
 strict_arg:pol=Dalek -> regs(machine q) 3%nat=PrepareOutputs.dest e;
 selected:forall j,(j<8)%nat ->
   let ptr:=read_word (mem(machine q)) (PrepareOutputs.dest e+8*Z.of_nat j) in
   (RootDecision.decodes false e j -> ptr=Return.scratch e+PrepareChunk.Caller.table_offset j) /\
   (~RootDecision.decodes false e j -> ptr=regs e 8%nat);
 output_regs:Prologue.output_registers e (machine q); remaining:regs(machine q) 12%nat=Prologue.rows_left (regs e 6%nat);
 flags:forall j,(j<8)%nat -> let v:=mem(machine q)(PrepareOutputs.dest e+64+Z.of_nat j) in
   (v=0 \/ v=1) /\ (v=1 <-> EligibleLanes.candidate e j);
 decoded_r:forall j,(j<8)%nat -> (Z.testbit (mem(machine q)(Rows.frame e+840)) (Z.of_nat j)=true <-> RootDecision.decodes true e j);
 key_tables:PreparedTables.table e (machine q)
}.

Lemma encodings pol bias entry e q : result pol bias entry e q -> PreparedInputs.encodings e (machine q).
Proof. intro R;exact (PreparedInputs.encoded _ _ (operands _ _ _ _ _ R)). Qed.

Theorem checked pol bias entry e before caller p a : placement e -> loaded pol bias (mem e) (writable e) ->
 EligibleLanes.post pol bias e before caller -> EligibilityFrame.context pol bias entry e caller ->
 DecodedRows.geometry false e (TableRowMeaning.point e (machine caller)) ->
 PreparedInputs.operands e (machine caller) -> PrepareOutputs.result pol bias e caller p a -> exists q,execute bias a=Some q /\ result pol bias entry e q /\
 mem(machine q)=mem(machine a) /\ log q=log a.
Proof.
 intros P I E C Points Enc A;pose proof(PreparedFrame.context _ _ _ _ _ _ _ P A C) as Frame.
 destruct Frame as [Link Outputs Meta [Slots BP] Layout].
 destruct(stack_ok _ P) as [[L H] Al];set (top:=common_top pol e) in *.
 assert (SP:regs(machine a) 4%nat=top-104).
 { rewrite (PrepareOutputs.registers _ _ _ _ _ _ A),(TableUnwind.stack _ _ _ _ _ (PrepareOutputs.parent _ _ _ _ _ _ A));unfold TableEntry.frame,top;ring. }
 destruct(raw (PrepareVectors.origin bias) (machine a) (LinkedRun.carry a) top
    ltac:(unfold top,common_top,Rows.frame,sp in *;destruct pol;lia) ltac:(unfold top,common_top,Rows.frame,sp in *;destruct pol;lia) SP)
    as [last [Run [Back [Stack [AX [M [RBP G]]]]]]].
 pose proof(PrepareOutputs.writes _ _ _ _ _ _ A) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc (in_common pol)) as [Map Sep].
 destruct(at_segment _ _ a _ _ 10 248 _ _ Acc (PrepareOutputs.pc _ _ _ _ _ _ A) Map Sep Run (Forall_nil _)) as [Next Paid].
 eexists;split;[exact Next|split;[constructor|split;[exact M|apply app_nil_r]]].
 - cbn [LinkedRun.finish ip];unfold absolute;rewrite Back;destruct Link as [Root Shim];destruct pol.
   + unfold top,common_top;rewrite Z.sub_0_r,Root;apply ScalarRefinement.word_idempotent.
   + unfold top;rewrite (proj1 Shim),ScalarRefinement.word_idempotent;apply word_fits.
     destruct(proj1(symbols _ _ _ _ I _ _ in_strict)) as [Low High];change (Z.of_nat(length PrepareChunk.StrictBytes.symbol_bytes)) with 37 in High;change (0<=bias+PrepareNative.strict+9<2^64);lia.
 - exact Stack.
 - exact AX.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (PrepareOutputs.words _ _ _ _ _ _ A) Next).
 - eapply PreparedInputs.keep;[|exact Enc]. intros x X;cbn [LinkedRun.finish machine];rewrite M;apply (PreparedInputs.through_tables _ _ _ _ _ _ P A),X.
 - constructor;cbn [LinkedRun.finish machine];[now rewrite M|now rewrite M|now rewrite M|split;[now rewrite M|now rewrite RBP]|now rewrite M].
 - destruct Outputs as [_ [_ [_ [S _]]]];cbn [LinkedRun.finish machine];rewrite (G 4%nat 15%nat eq_refl),<-S;f_equal;ring.
 - destruct Outputs as [_ [_ [_ [_ [D _]]]]];intros Eq;cbn [LinkedRun.finish machine];unfold PrepareOutputs.dest;rewrite (G 0%nat 3%nat eq_refl),<-(D Eq);f_equal;ring.
 - intros j J;cbn [LinkedRun.finish machine];cbv zeta;rewrite M,(PrepareOutputs.table_ptr _ _ _ _ _ _ A j J),(EligibleLanes.identity_address _ _ _ _ _ E).
   pose proof(EligibleLanes.key_bits _ _ _ _ _ E j J) as K;destruct(Z.testbit _ _);intuition discriminate.
 - destruct Outputs as [Count [Out [Left _]]];split;cbn [LinkedRun.finish machine];
     [rewrite (G 2%nat 13%nat eq_refl),<-Count|rewrite (G 3%nat 14%nat eq_refl),<-Out];f_equal;ring.
 - destruct Outputs as [_ [_ [Left _]]];change (regs(cpu_state last) 12%nat=Prologue.rows_left (regs e 6%nat));rewrite (G 1%nat 12%nat eq_refl),<-Left;f_equal;ring.
 - intros j J;cbn [LinkedRun.finish machine];cbv zeta;rewrite M,(PrepareOutputs.eligibility _ _ _ _ _ _ A j J),<-(EligibleLanes.bit _ _ _ _ _ E j J).
   destruct (Z.testbit _ _);cbn;intuition discriminate.
 - intros j J;cbn [LinkedRun.finish machine];rewrite M,(PreparedFrame.sig_byte _ _ _ _ _ _ P A);exact (EligibleLanes.sig_bits _ _ _ _ _ E j J).
 - apply (PreparedTables.meaning _ _ _ Points).
   apply (TableContents.preserve _ _ (machine p));[|exact (TableUnwind.contents _ _ _ _ _ (PrepareOutputs.parent _ _ _ _ _ _ A))].
   intros x X;cbn [LinkedRun.finish machine];rewrite M;apply (PrepareOutputs.surrounding _ _ _ _ _ _ A).
   destruct(scratch_stack _ P);unfold TableEntry.tables,PrepareOutputs.dest,Rows.frame,sp,span in *;lia.
Qed.

Definition observe pol bias e p ks:=bind (PrepareOutputs.observe pol bias e p ks) (fun '(a,ak)=>option_map (fun q=>(q,ak)) (execute bias a)).
Theorem from_eligible pol bias entry e before p ks : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> EligibleLanes.post pol bias e before p -> EligibilityFrame.context pol bias entry e p ->
 DecodedRows.geometry false e (TableRowMeaning.point e (machine p)) ->
 PreparedInputs.operands e (machine p) -> regs(machine p) 14%nat<>0 -> exists q bank,observe pol bias e p ks=Some(q,bank) /\ result pol bias entry e q.
Proof.
 intros P I Al E C Points Enc Live;destruct(PrepareOutputs.from_eligible _ _ _ _ _ ks P I Al E Live) as [a [ak [r [Run A]]]].
 destruct(checked _ _ _ _ _ _ _ _ P I E C Points Enc A) as [q [End [Q _]]];exists q,ak;split;[unfold observe;rewrite Run;cbn [bind];now rewrite End|exact Q].
Qed.
