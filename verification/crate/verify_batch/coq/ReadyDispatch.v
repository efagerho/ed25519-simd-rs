From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics
 execution.MappedFetch memory.MemoryGeometry memory.WriteTrace memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require HashEntry StrictFilterCall.
Local Open Scope Z_scope.

Definition execute pol bias pc text p ks:=match pol with
 | Zip215=>HashEntry.execute bias pc text p ks
 | Dalek=>option_map (fun q=>(q,ks)) (StrictFilterCall.execute bias p) end.
Definition observe pol bias pc text p ks:=bind (PreparedReturn.observe bias p ks)
  (fun '(a,b)=>execute pol bias pc text a b).
Definition site pol:=match pol with Zip215=>HashEntry.callee | Dalek=>DalekPostHash.FilterBytes.address end.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record reached pol bias e q:Prop:=Reached {
 pc:ip q=bias+site pol; writes:accounted e (writable e) q; words:well_formed(machine q);
 flags:forall j,(j<8)%nat -> let v:=mem(machine q)(PrepareOutputs.dest e+64+Z.of_nat j) in
   (v=0 \/ v=1) /\ (v=1 <-> EligibleLanes.candidate e j)
}.
Theorem checked pol bias pc text e p ks : HashEntry.bound pc text -> placement e -> loaded pol bias (mem e) (writable e) ->
 fits64 (bias+pc) (Z.of_nat(length text)) -> mapped (mem e) (bias+pc) text ->
 (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 PreparedReturn.result pol bias (bias+pc) e p -> exists q bank,execute pol bias pc text p ks=Some(q,bank) /\ reached pol bias e q /\
 match pol with Zip215=>HashEntry.entry bias pc e p q | Dalek=>StrictFilterCall.entry bias e p q end.
Proof.
 intros C P I Fit Image Sep Done;destruct pol.
 - assert (PC:ip p=bias+pc+385).
   { rewrite (PreparedReturn.pc _ _ _ _ _ Done);unfold PreparedReturn.destination;change (word(bias+pc+385)=bias+pc+385);apply word_fits;
       destruct C as [_ [_ N]];destruct Fit;unfold word64;lia. }
   destruct(HashEntry.checked Zip215 bias pc text e p ks C P I Fit Image Sep PC (PreparedReturn.success _ _ _ _ _ Done)
      ltac:(rewrite (PreparedReturn.stack _ _ _ _ _ Done);unfold common_top;ring)
      (PreparedReturn.scratch_reg _ _ _ _ _ Done) (PreparedReturn.writes _ _ _ _ _ Done) (PreparedReturn.words _ _ _ _ _ Done)
      (EligibilityFrame.inputs _ _ _ _ _ (PreparedReturn.caller _ _ _ _ _ Done))) as [q [k [Run Q]]].
   exists q,k;split;[exact Run|split;[constructor|exact Q]];[exact (HashEntry.target _ _ _ _ _ Q)|exact (HashEntry.writes _ _ _ _ _ Q)|
        exact (HashEntry.words _ _ _ _ _ Q)|].
   intros j J;cbv zeta;rewrite (HashEntry.other_bytes _ _ _ _ _ Q);[apply (PreparedReturn.flags _ _ _ _ _ Done j J)|unfold PrepareOutputs.dest,span;lia].
 - destruct(StrictFilterCall.checked bias (bias+pc) e p P I Done) as [q [Run Q]].
   exists q,ks;split;[cbn [execute];now rewrite Run|split;[constructor|exact Q]];[exact (StrictFilterCall.pc _ _ _ _ Q)|exact (StrictFilterCall.writes _ _ _ _ Q)|
       exact (StrictFilterCall.words _ _ _ _ Q)|].
   intros j J;cbv zeta;rewrite (StrictFilterCall.memory_after _ _ _ _ Q);unfold StrictFilterCall.event,commit;cbn [qword address size payload].
   rewrite write_outside by (unfold StrictFilterCall.slot,common_top,PrepareOutputs.dest;lia);exact (PreparedReturn.flags _ _ _ _ _ Done j J).
Qed.
End Iteration.
