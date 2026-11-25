From Coq Require Import List ZArith Lia Bool.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.MaskTransfer memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.DalekPostHash Require Keys.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterBranch FilterRows.
Local Open Scope Z_scope.

Definition execute bias p ks:=bind (FilterLoad.execute bias p) (fun a=>bind (FilterPass.execute false bias a ks)
 (fun '(b,k)=>option_map (fun v=>(v,k)) (FilterBranch.execute bias b k))).
Record result bias e p v k:Prop:=Result {
 writes:accounted e (writable e) (FilterBranch.stopped v); words:well_formed(machine(FilterBranch.stopped v));
 rsp:regs(machine(FilterBranch.stopped v)) 4%nat=StrictFilterCall.slot e-8;
 gpr:forall r,r<>1%nat -> r<>4%nat -> regs(machine(FilterBranch.stopped v)) r=regs(machine p) r;
 memory_after:preserved (fun x=>~FilterRows.slot e x) (mem(machine p)) (mem(machine(FilterBranch.stopped v)));
 addresses:FilterRows.addresses e (machine p) (machine(FilterBranch.stopped v));
 constants:FilterCarry.constants(machine(FilterBranch.stopped v));
 saved_lo:forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine(FilterBranch.stopped v)) j (15+i)%nat=
   DalekPostHash.Keys.column (FilterRows.view e (machine p)) j 0 i;
 mask:forall j,(j<8)%nat -> k 1%nat j=DalekPostHash.Keys.first (FilterRows.view e (machine p)) j;
 branch:match v with FilterBranch.Done q=>ip q=bias+FilterLoad.site+543 /\ mask16(k 1%nat)=0
  | FilterBranch.CompareZ q=>ip q=bias+FilterLoad.site+313 /\ regs(machine q) 1%nat=mask16(k 1%nat) end
}.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked bias e prep p ks : placement e -> loaded Dalek bias (mem e) (writable e) ->
 StrictFilterCall.entry bias e prep p -> FilterRows.rows e (machine p) ->
 exists v k,execute bias p ks=Some(v,k) /\ result bias e p v k.
Proof.
 intros P I E Rows;destruct(FilterLoad.checked _ _ _ _ P I E) as [a [A Load]].
 assert (SA:regs(machine a) 4%nat=StrictFilterCall.slot e-8) by (rewrite (FilterLoad.gpr _ _ _ _ Load);reflexivity).
 pose proof(FilterLoad.field_constants _ _ _ _ Load) as CA.
 destruct(FilterPass.checked false bias e a ks P I (FilterLoad.pc _ _ _ _ Load) (FilterLoad.writes _ _ _ _ Load)
  (FilterLoad.words _ _ _ _ Load) SA CA) as [b [k [B Pass]]].
 destruct(FilterBranch.checked _ _ _ k I (FilterPass.pc _ _ _ _ _ _ Pass) (FilterPass.writes _ _ _ _ _ _ Pass)
    (FilterPass.words _ _ _ _ _ _ Pass)) as [v [End [Paid [W [M [Log [Vec Branch]]]]]]].
 assert (Initial:preserved (fun x=>~FilterRows.slot e x) (mem(machine p)) (mem(machine a))) by
   (intros x _;now rewrite (FilterLoad.memory_after _ _ _ _ Load)).
 pose proof(FilterLoad.addresses _ _ _ _ Load) as Ptr.
 assert (G:forall r,r<>1%nat -> regs(machine(FilterBranch.stopped v)) r=regs(machine b) r).
 { destruct v;destruct Branch as [_ [_ Reg]];intros r Different;rewrite Reg;[reflexivity|unfold put;now rewrite (proj2(Nat.eqb_neq 1 r) ltac:(lia))]. }
 exists v,k;split;[unfold execute;rewrite A;cbn [bind];rewrite B;cbn [bind];now rewrite End|constructor].
 - exact Paid.
 - exact W.
 - rewrite G,(FilterPass.regs_after _ _ _ _ _ _ Pass) by discriminate;exact SA.
 - intros r R SP;rewrite G,(FilterPass.regs_after _ _ _ _ _ _ Pass),(FilterLoad.gpr _ _ _ _ Load) by assumption;
   unfold put;now rewrite (proj2(Nat.eqb_neq 4 r) ltac:(lia)).
 - intros x X;rewrite M,(FilterPass.memory_after _ _ _ _ _ _ Pass) by exact X;apply Initial,X.
 - intros j J;rewrite Vec,(FilterPass.high_regs _ _ _ _ _ _ Pass) by lia;exact (Ptr j J).
 - intros i j N;rewrite Vec,(FilterPass.high_regs _ _ _ _ _ _ Pass) by lia;apply CA,N.
 - intros j i J N;rewrite Vec,(FilterPass.saved_lo _ _ _ _ _ _ Pass eq_refl j i J N).
   apply FilterRows.cell;[exact Rows|exact Ptr|exact Initial|exact J|lia|exact N].
 - intros j J;rewrite (FilterPass.equal_zero _ _ _ _ _ _ Pass),(proj2(Nat.ltb_lt j 8) J);cbn [andb].
   apply FilterRows.first;assumption.
 - destruct v;destruct Branch as [Test [PC Reg]];cbn [FilterBranch.stopped] in PC,Reg;split;try assumption;rewrite Reg;reflexivity.
Qed.
End Iteration.
