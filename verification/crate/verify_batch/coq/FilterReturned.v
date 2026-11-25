From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterScreen Tables.
Local Open Scope Z_scope.

Definition execute bias p ks:=bind (FilterScreen.execute bias p ks) (fun '(a,k)=>option_map (fun q=>(q,k)) (FilterReturn.execute bias a)).
Record result bias e p q:Prop:=Result {
 pc:ip q=StrictFilterCall.link bias; writes:accounted e (writable e) q; words:well_formed(machine q);
 rsp:regs(machine q) 4%nat=StrictFilterCall.slot e+8;
 registers:forall r,r<>1%nat -> r<>4%nat -> regs(machine q) r=regs(machine p) r;
 frame:preserved (FilterScreen.kept e) (mem(machine p)) (mem(machine q));
 flags:forall j,(j<8)%nat -> let x:=FilterFlags.flag_ptr e+Z.of_nat j in
   mem(machine q) x=if FilterScreen.weak e (machine p) j then 0 else mem(machine p) x
}.
Theorem checked bias outer e prep p ks : placement e -> loaded Dalek bias (mem e) (writable e) -> Tables.mapped e bias ->
 PreparedReturn.result Dalek bias outer e prep -> StrictFilterCall.entry bias e prep p ->
 exists q k,execute bias p ks=Some(q,k) /\ result bias e p q.
Proof.
 intros P I T Prep E;pose proof(FilterRows.readable _ _ _ _ _ P I T Prep E) as Rows.
 destruct(FilterScreen.checked _ _ _ _ ks P I E Rows) as [a [ak [A Screen]]].
 assert (Back:read_word (mem(machine a)) (StrictFilterCall.slot e)=StrictFilterCall.link bias).
 { rewrite <-(StrictFilterCall.back _ _ _ _ E);apply preserved_read with (outside:=FilterScreen.kept e).
   - exact (FilterScreen.frame _ _ _ _ Screen).
   - intros k K;change (0<=k<8) in K;unfold FilterScreen.kept,FilterRows.slot,StrictFilterCall.slot,common_top,FilterFlags.flag_ptr,PrepareOutputs.dest,span;lia. }
 destruct(FilterReturn.checked _ _ _ P I (FilterScreen.pc _ _ _ _ Screen) (FilterScreen.writes _ _ _ _ Screen)
    (FilterScreen.words _ _ _ _ Screen) (FilterScreen.rsp _ _ _ _ Screen) Back) as [q [B End]].
 exists q,ak;split;[unfold execute;rewrite A;cbn [bind];now rewrite B|constructor].
 - exact (FilterReturn.pc _ _ _ _ End).
 - exact (FilterReturn.writes _ _ _ _ End).
 - exact (FilterReturn.words _ _ _ _ End).
 - exact (FilterReturn.stack _ _ _ _ End).
 - intros r R S;rewrite (FilterReturn.kept _ _ _ _ End) by exact S;apply (FilterScreen.gpr _ _ _ _ Screen);assumption.
 - rewrite (FilterReturn.memory_after _ _ _ _ End);exact (FilterScreen.frame _ _ _ _ Screen).
 - intros j J;cbv zeta;rewrite (FilterReturn.memory_after _ _ _ _ End);exact (FilterScreen.flags _ _ _ _ Screen j J).
Qed.
