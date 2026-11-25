From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require execution.ScalarRefinement.
From Ed25519Simd.PrepareChunk Require StrictBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterReturned FilterMeaning.
From Ed25519Simd.VerifyBatch Require ScoreBuffers.
Import ListNotations. Local Open Scope Z_scope.

Definition path:list line:=[(25,2%nat,Zero32 0);(27,5%nat,CompareMemImm (Address 3 None 64) 0);
 (32,3%nat,SetNotEqual 0);(35,1%nat,RestoreG 3);(36,1%nat,ScalarBytes.Ret)].
Lemma code:linked StrictBytes.symbol_bytes path.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (bias+PrepareNative.strict) StrictBytes.symbol_bytes 5.
Definition status e s:=Z.b2z(negb(read_word (mem s) (FilterFlags.flag_ptr e)=?0)).

Lemma raw bias s c top d : regs s 4%nat=top-16 -> regs s 3%nat=d -> 16<=top<2^64 -> word64(d+64) ->
 exists last,run 5 (ScalarBytes.fetch (bias+PrepareNative.strict) StrictBytes.symbol_bytes) (State(Running 25) s c)=Some(last,[]) /\
 loc last=Returned(word(read_word (mem s) (top-8))) /\ regs(cpu_state last) 4%nat=top /\
 regs(cpu_state last) 0%nat=Z.b2z(negb(read_word (mem s) (d+64)=?0)) /\ mem(cpu_state last)=mem s /\
 regs(cpu_state last) 3%nat=read_word(mem s)(top-16) /\
 forall r,r<>0%nat -> r<>3%nat -> r<>4%nat -> regs(cpu_state last) r=regs s r.
Proof.
 intros SP BX T D;eexists;split;[apply (InstructionRoute.checked _ _ _ code);reflexivity|].
 cbn [path follow loc cpu_state cf ScalarBytes.step option_map low_byte flag with_zf set set_regs effective regs mem put Nat.eqb
   pop caller_step stack_step result_regs result_mem target_ip advance_rsp stack_top with_words apply_stack].
 unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite SP,BX,Z.add_0_r,(word_fits _ D).
 repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64;lia)) end.
 replace (top-16+8) with (top-8) by ring;replace (top-8+8) with top by ring.
 destruct (read_word (mem s) (d+64)=?0);cbn;repeat split;intros r A B C;
  destruct r as [|[|[|[|[|r]]]]];congruence.
Qed.

Definition unchanged e x:= ~span (StrictFilterCall.slot e) 8 x /\ FilterScreen.kept e x.
Lemma parent bias e prep p q : StrictFilterCall.entry bias e prep p -> FilterReturned.result bias e p q ->
 preserved (unchanged e) (mem(machine prep)) (mem(machine q)).
Proof.
 intros E F x [S K];rewrite (FilterReturned.frame _ _ _ _ F) by exact K.
 rewrite (StrictFilterCall.memory_after _ _ _ _ E);apply write_outside,S.
Qed.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record result (outer:Z) e p q:Prop:=Result {
 pc:ip q=word(outer+Ed25519Simd.VerifyBatch.Image.offset Ed25519Simd.VerifyBatch.Image.Prepared); writes:accounted e (writable e) q; words:well_formed(machine q);
 stack:regs(machine q) 4%nat=Rows.frame e; ax:regs(machine q) 0%nat=status e (machine q);
 inputs:WrapperInputs.layout e (mem(machine q)); encodings:PreparedInputs.encodings e (machine q);
 scratch_reg:regs(machine q) 15%nat=scratch e; outputs:Prologue.output_registers e (machine q);
 remaining:regs(machine q) 12%nat=BatchWindow.next_count e;
 metadata:BatchWindow.metadata e (mem(machine q)); saved:StageEntry.saved_caller e (machine q);
 filtered:forall j,(j<8)%nat -> let v:=mem(machine q)(FilterFlags.flag_ptr e+Z.of_nat j) in
 (v=0 \/ v=1) /\ (v=1 <-> EligibleLanes.candidate e j /\ FilterScreen.weak e (machine p) j=false);
 decoded_r:forall j,(j<8)%nat -> (Z.testbit (mem(machine q)(Rows.frame e+840)) (Z.of_nat j)=true <-> RootDecision.decodes true e j);
 buffers:ScoreBuffers.data e (machine q);
 next_descriptor:BatchWindow.next_descriptor e (regs(machine q) 3%nat);
 strong_lane:forall j,(j<8)%nat -> (EligibleLanes.candidate e j /\ FilterScreen.weak e (machine p) j=false <-> FilterMeaning.eligible e j)
}.

Theorem checked bias outer e prep p a : placement e -> loaded Dalek bias (mem e) (writable e) ->
 PreparedReturn.result Dalek bias outer e prep -> StrictFilterCall.entry bias e prep p -> FilterReturned.result bias e p a ->
 exists q,execute bias a=Some q /\ result outer e p q.
Proof.
 intros P I Done Entry F;set (t:=Rows.frame e);set (d:=PrepareOutputs.dest e);set (s:=machine a).
 pose proof(parent _ _ _ _ _ Entry F) as M.
 assert (Reg:forall r,r<>1%nat -> r<>4%nat -> r<>7%nat -> r<>6%nat -> regs s r=regs(machine prep) r).
 { intros r C S D SI;unfold s;rewrite (FilterReturned.registers _ _ _ _ F) by assumption;
   apply (StrictFilterCall.caller_registers _ _ _ _ Entry);assumption. }
 pose proof(PreparedReturn.caller _ _ _ _ _ Done) as C;destruct C as [[Link [Shim Future]] _ Meta [Saved BP] Layout].
 assert (Back:read_word (mem s) (t-8)=word(outer+Ed25519Simd.VerifyBatch.Image.offset Ed25519Simd.VerifyBatch.Image.Prepared)).
 { rewrite <-Link;apply preserved_read with (outside:=unchanged e);[exact M|].
   intros k K;change (0<=k<8) in K;unfold unchanged,FilterScreen.kept,FilterRows.slot,FilterFlags.flag_ptr,StrictFilterCall.slot,common_top,PrepareOutputs.dest,span,t;lia. }
 destruct(stack_ok _ P) as [[Low High] _];destruct(raw bias s (LinkedRun.carry a) t d
    ltac:(unfold s;rewrite (FilterReturned.rsp _ _ _ _ F);unfold t,StrictFilterCall.slot,common_top;ring)
    ltac:(rewrite Reg by discriminate;exact (PreparedReturn.strict_arg _ _ _ _ _ Done eq_refl))
    ltac:(unfold t,Rows.frame,sp in *;lia) ltac:(unfold d,PrepareOutputs.dest,Rows.frame,sp,word64 in *;lia))
   as [last [Run [IP [SP [AX [Mem [BX G]]]]]]].
 pose proof(FilterReturned.writes _ _ _ _ F) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc in_strict) as [Map Sep].
 destruct(at_segment _ _ a _ _ 5 25 _ _ Acc (FilterReturned.pc _ _ _ _ F) Map Sep Run (Forall_nil _)) as [End Paid].
 assert (Same:preserved (unchanged e) (mem(machine prep)) (mem(cpu_state last))) by (rewrite Mem;exact M).
 assert (Keep:forall r,r<>0%nat -> r<>1%nat -> r<>3%nat -> r<>4%nat -> r<>6%nat -> r<>7%nat ->
   regs(cpu_state last) r=regs(machine prep) r) by (intros;rewrite G,Reg by assumption;reflexivity).
 eexists;split;[exact End|constructor];cbn [LinkedRun.finish ip machine].
 - unfold absolute;rewrite IP,Back;apply ScalarRefinement.word_idempotent.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (FilterReturned.words _ _ _ _ F) End).
 - exact SP.
 - unfold status;rewrite Mem;exact AX.
 - eapply WrapperInputs.preserve;[|exact Layout];intros x X;apply Same;
   unfold unchanged,FilterScreen.kept,FilterRows.slot,StrictFilterCall.slot,FilterFlags.flag_ptr,common_top,
      PrepareOutputs.dest,WrapperInputs.needed,span in *;lia.
 - eapply PreparedInputs.keep_encodings;[|exact (PreparedReturn.encodings _ _ _ _ _ Done)].
   intros x X;apply Same;destruct(scratch_stack _ P);unfold unchanged,FilterScreen.kept,FilterRows.slot,StrictFilterCall.slot,
    FilterFlags.flag_ptr,common_top,PrepareOutputs.dest,PreparedInputs.prefix,Rows.frame,sp,span in *;lia.
 - rewrite Keep by discriminate;exact (PreparedReturn.scratch_reg _ _ _ _ _ Done).
 - destruct(PreparedReturn.output_regs _ _ _ _ _ Done) as [N Dst];split;rewrite Keep by discriminate;assumption.
 - rewrite Keep by discriminate;exact (PreparedReturn.remaining _ _ _ _ _ Done).
 - eapply IndexStores.metadata_preserved;[|exact Meta];intros x X;apply Same;
   unfold unchanged,FilterScreen.kept,FilterRows.slot,StrictFilterCall.slot,FilterFlags.flag_ptr,common_top,PrepareOutputs.dest,span;lia.
 - split;[intros x X;rewrite Same;[apply Saved,X|]|now rewrite Keep by discriminate].
   unfold unchanged,FilterScreen.kept,FilterRows.slot,StrictFilterCall.slot,FilterFlags.flag_ptr,common_top,PrepareOutputs.dest,Rows.frame,sp,span in *;lia.
 - intros j J;cbv zeta;rewrite Mem;unfold s;rewrite (FilterReturned.flags _ _ _ _ F j J).
   assert (Initial:mem(machine p)(FilterFlags.flag_ptr e+Z.of_nat j)=mem(machine prep)(FilterFlags.flag_ptr e+Z.of_nat j)).
   { rewrite (StrictFilterCall.memory_after _ _ _ _ Entry);apply write_outside.
     change (~span (StrictFilterCall.slot e) 8 (FilterFlags.flag_ptr e+Z.of_nat j));unfold span.
     unfold StrictFilterCall.slot,FilterFlags.flag_ptr,common_top,PrepareOutputs.dest;lia. }
   rewrite Initial;destruct(PreparedReturn.flags _ _ _ _ _ Done j J) as [Bit Can];fold (FilterFlags.flag_ptr e) in Bit,Can.
   destruct(FilterScreen.weak e (machine p) j);intuition discriminate.
 - intros j J;rewrite Same;[exact (PreparedReturn.decoded_r _ _ _ _ _ Done j J)|].
   unfold unchanged,FilterScreen.kept,FilterRows.slot,FilterFlags.flag_ptr,StrictFilterCall.slot,common_top,PrepareOutputs.dest,span;lia.
 - eapply ScoreBuffers.keep;[|exact (ScoreBuffers.from_prepare _ _ _ _ _ Done)];intros x X;apply Same.
   destruct(scratch_stack _ P);unfold ScoreBuffers.region,unchanged,FilterScreen.kept,FilterRows.slot,FilterFlags.flag_ptr,
    StrictFilterCall.slot,common_top,PrepareOutputs.dest,Rows.frame,sp,span,disjoint in *;lia.
 - intro Long;rewrite BX,<-(Future Long);apply preserved_read with (outside:=unchanged e);[exact M|].
   intros k K;change (0<=k<8) in K;unfold unchanged,FilterScreen.kept,FilterRows.slot,FilterFlags.flag_ptr,StrictFilterCall.slot,common_top,PrepareOutputs.dest,span,t;lia.
 - intros j J;exact (FilterMeaning.enabled _ _ _ _ _ _ P Done Entry J).
Qed.

Definition observe bias p ks:=bind (FilterReturned.execute bias p ks) (fun '(a,k)=>option_map (fun q=>(q,k)) (execute bias a)).
Theorem from_entry bias outer e prep p ks : placement e -> loaded Dalek bias (mem e) (writable e) -> Tables.mapped e bias ->
 PreparedReturn.result Dalek bias outer e prep -> StrictFilterCall.entry bias e prep p ->
 exists q k,observe bias p ks=Some(q,k) /\ result outer e p q.
Proof.
 intros P I T Done E;destruct(FilterReturned.checked _ _ _ _ _ ks P I T Done E) as [a [k [Run F]]].
 destruct(checked _ _ _ _ _ _ P I Done E F) as [q [End Q]].
 exists q,k;split;[unfold observe;rewrite Run;cbn [bind];now rewrite End|exact Q].
Qed.

Definition live e s:=exists j,(j<8)%nat /\ EligibleLanes.candidate e j /\ FilterScreen.weak e s j=false.
Lemma decision outer e p q : result outer e p q ->
 (regs(machine q) 0%nat=0 \/ regs(machine q) 0%nat=1) /\
 (regs(machine q) 0%nat=1 <-> live e (machine p)).
Proof.
 intro Q;rewrite (ax _ _ _ _ Q);unfold status;set (m:=mem(machine q));set (a:=FilterFlags.flag_ptr e).
 assert (Zbyte:forall k,0<=k<8 -> word_byte 0 k=0).
 { intros k K;unfold word_byte;rewrite Z.div_0_l;[reflexivity|apply Z.pow_nonzero;lia]. }
 destruct(Z.eqb_spec (read_word m a) 0) as [Zero|Nonzero];cbn;split;try tauto.
 - split;[discriminate|intros [j [J Live]]].
   pose proof(proj2(proj2(filtered _ _ _ _ Q j J)) Live) as One.
   pose proof(read_word_byte m a (Z.of_nat j) (proj2(proj2(words _ _ _ _ Q))) ltac:(lia)) as Byte.
   rewrite Zero,Zbyte in Byte by lia;fold m a in One;lia.
 - split;[intros _|reflexivity].
   destruct(existsb (fun j=>m(a+Z.of_nat j)=?1) (seq 0 8)) eqn:Test.
   + apply existsb_exists in Test as [j [J Yes]];apply in_seq in J;apply Z.eqb_eq in Yes.
     exists j;split;[lia|apply (proj1(proj2(filtered _ _ _ _ Q j ltac:(lia)))),Yes].
   + exfalso;apply Nonzero,read_word_exact;[unfold word64;lia|]. intros k K;rewrite Zbyte by exact K.
     set (j:=Z.to_nat k);assert (J:(j<8)%nat /\ Z.of_nat j=k) by (unfold j;rewrite Z2Nat.id by lia;lia).
     destruct(proj1(filtered _ _ _ _ Q j (proj1 J))) as [Off|On];fold a m in Off || fold a m in On;
       [now rewrite <-(proj2 J)|].
     assert (Found:existsb (fun j=>m(a+Z.of_nat j)=?1) (seq 0 8)=true).
     { apply existsb_exists;exists j;split;[apply in_seq;lia|apply Z.eqb_eq,On]. }
     congruence.
Qed.
End Iteration.
