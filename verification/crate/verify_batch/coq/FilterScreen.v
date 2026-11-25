From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MaskTransfer memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.DalekPostHash Require Keys.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterFirst FilterFlags FilterReturn.
Local Open Scope Z_scope.

Definition weak e s j:=let t:=FilterRows.view e s in DalekPostHash.Keys.first t j && DalekPostHash.Keys.second t j.
Definition kept e x:=~FilterRows.slot e x /\ ~span (FilterFlags.flag_ptr e) 8 x.
Definition execute bias p ks:=bind (FilterFirst.execute bias p ks) (fun '(v,k)=>match v with
 | FilterBranch.Done q=>Some(q,k)
 | FilterBranch.CompareZ q=>bind (FilterPass.execute true bias q k) (fun '(a,b)=>FilterFlags.execute bias a b) end).
Record result bias e p q:Prop:=Result {
 pc:ip q=bias+FilterLoad.site+543; writes:accounted e (writable e) q; words:well_formed(machine q);
 rsp:regs(machine q) 4%nat=StrictFilterCall.slot e-8;
 gpr:forall r,r<>1%nat -> r<>4%nat -> regs(machine q) r=regs(machine p) r;
 frame:preserved (kept e) (mem(machine p)) (mem(machine q));
 flags:forall j,(j<8)%nat -> let a:=FilterFlags.flag_ptr e+Z.of_nat j in
 mem(machine q) a=if weak e (machine p) j then 0 else mem(machine p) a
}.
Lemma flag_outside e j : (j<8)%nat -> ~FilterRows.slot e (FilterFlags.flag_ptr e+Z.of_nat j).
Proof. intros J;unfold FilterRows.slot,StrictFilterCall.slot,common_top,FilterFlags.flag_ptr,PrepareOutputs.dest;lia. Qed.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked bias e prep p ks : placement e -> loaded Dalek bias (mem e) (writable e) ->
 StrictFilterCall.entry bias e prep p -> FilterRows.rows e (machine p) ->
 exists q bank,execute bias p ks=Some(q,bank) /\ result bias e p q.
Proof.
 intros P I E Rows;destruct(FilterFirst.checked _ _ _ _ ks P I E Rows) as [v [k [Run First]]].
 pose proof(FilterFirst.writes _ _ _ _ _ First) as Paid;pose proof(FilterFirst.words _ _ _ _ _ First) as W.
 pose proof(FilterFirst.rsp _ _ _ _ _ First) as SP;pose proof(FilterFirst.gpr _ _ _ _ _ First) as G.
 pose proof(FilterFirst.memory_after _ _ _ _ _ First) as M;pose proof(FilterFirst.mask _ _ _ _ _ First) as K.
 pose proof(FilterFirst.branch _ _ _ _ _ First) as Branch;unfold execute;rewrite Run;destruct v as [b|b];cbn [bind FilterBranch.stopped] in *.
 - destruct Branch as [PC Zero];exists b,k;split;[reflexivity|constructor];try assumption.
   + intros x [X _];now apply M.
   + intros j J;cbv zeta;rewrite M by (apply flag_outside,J).
     pose proof(proj2(kmov_value (k 1%nat)) j ltac:(lia)) as Bit;rewrite Zero,Z.bits_0,K in Bit by exact J;unfold weak;rewrite <-Bit;reflexivity.
 - destruct Branch as [PC CX].
   destruct(FilterPass.checked true bias e b k P I PC Paid W SP (FilterFirst.constants _ _ _ _ _ First)) as [z [kz [Second Z]]].
   assert (SI:regs(machine z) 6%nat=FilterFlags.flag_ptr e) by
     (rewrite (FilterPass.regs_after _ _ _ _ _ _ Z),G by discriminate;exact (StrictFilterCall.flags _ _ _ _ E)).
   destruct(FilterFlags.checked _ _ _ kz P I (FilterPass.pc _ _ _ _ _ _ Z) (FilterPass.writes _ _ _ _ _ _ Z)
       (FilterPass.words _ _ _ _ _ _ Z) SI) as [q [out [End Clear]]].
   exists q,out;split;[rewrite Second;exact End|constructor];[exact (FilterFlags.pc _ _ _ _ _ Clear)|exact (FilterFlags.writes _ _ _ _ _ Clear)|
      exact (FilterFlags.words _ _ _ _ _ Clear)| | | |].
   + now rewrite (FilterFlags.registers _ _ _ _ _ Clear),(FilterPass.regs_after _ _ _ _ _ _ Z).
   + intros r R T;rewrite (FilterFlags.registers _ _ _ _ _ Clear),(FilterPass.regs_after _ _ _ _ _ _ Z);apply G;assumption.
   + intros x [X Y];rewrite (FilterFlags.outside _ _ _ _ _ Clear) by exact Y;rewrite (FilterPass.memory_after _ _ _ _ _ _ Z) by exact X;apply M,X.
   + intros j J;cbv zeta;rewrite (FilterFlags.flags _ _ _ _ _ Clear j J).
     rewrite (FilterPass.memory_after _ _ _ _ _ _ Z),M by (apply flag_outside,J).
     unfold FilterFlags.clears;rewrite (FilterPass.regs_after _ _ _ _ _ _ Z),CX,(proj2(kmov_value _) j ltac:(lia)),K by exact J.
     rewrite (FilterPass.equal_zero _ _ _ _ _ _ Z),(proj2(Nat.ltb_lt j 8) J);cbn [andb].
     rewrite (FilterRows.second e (machine p) (machine b) j Rows (FilterFirst.addresses _ _ _ _ _ First)
       M (FilterFirst.constants _ _ _ _ _ First) (fun i N=>FilterFirst.saved_lo _ _ _ _ _ First j i J N) J).
     unfold weak;now rewrite andb_comm.
Qed.
End Iteration.
