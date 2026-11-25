From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun abi.SysV memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require HashLayout HashResume NativeHash.
Local Open Scope Z_scope.

(* Live across SHA. The R-validity byte is separate from the eight
   eligibility bytes, which also account for S and the policy's key check. *)
Record inputs pol e s:Prop:=Inputs {
 gprs:Prologue.context_registers e s;
 remaining:regs s 12%nat=Prologue.rows_left (regs e 6%nat);
 metadata:StageEntry.metadata e (mem s); saved:StageEntry.saved_caller e s;
 base:read_word (mem s) (Rows.frame e+944)=regs e 9%nat;
 flags:forall j,(j<8)%nat -> let b:=mem s (Rows.frame e+832+Z.of_nat j) in
   (b=0 \/ b=1) /\ (b=1 <-> HashLayout.eligible pol e j);
 r_valid:forall j,(j<8)%nat -> (Z.testbit (mem s (Rows.frame e+840)) (Z.of_nat j)=true <-> RootDecision.decodes true e j)
}.

Lemma zip bias o e q : PreparedReturn.result Zip215 bias o e q -> inputs Zip215 e (machine q).
Proof.
 intro R;destruct (PreparedReturn.caller _ _ _ _ _ R) as [_ _ Meta Saved Layout];constructor.
 - exact (conj (PreparedReturn.scratch_reg _ _ _ _ _ R) (PreparedReturn.output_regs _ _ _ _ _ R)).
 - exact (PreparedReturn.remaining _ _ _ _ _ R).
 - exact Meta.
 - exact Saved.
 - exact (proj2(WrapperInputs.tables _ _ Layout)).
 - intros j J;destruct(PreparedReturn.flags _ _ _ _ _ R j J) as [Bit On];unfold PrepareOutputs.dest in *;
   replace (Rows.frame e+832) with (Rows.frame e+768+64) by ring;split;[exact Bit|rewrite <-HashLayout.candidate;exact On].
 - exact (PreparedReturn.decoded_r _ _ _ _ _ R).
Qed.
Lemma dalek o e p q : StrictReturn.result o e p q -> inputs Dalek e (machine q).
Proof.
 intro R;constructor.
 - exact (conj (StrictReturn.scratch_reg _ _ _ _ R) (StrictReturn.outputs _ _ _ _ R)).
 - exact (StrictReturn.remaining _ _ _ _ R).
 - exact (StrictReturn.metadata _ _ _ _ R).
 - exact (StrictReturn.saved _ _ _ _ R).
 - exact (proj2(WrapperInputs.tables _ _ (StrictReturn.inputs _ _ _ _ R))).
 - intros j J;destruct(StrictReturn.filtered _ _ _ _ R j J) as [Bit On];unfold FilterFlags.flag_ptr,PrepareOutputs.dest in *;
   replace (Rows.frame e+832) with (Rows.frame e+768+64) by ring;split;[exact Bit|rewrite On;exact (StrictReturn.strong_lane _ _ _ _ R j J)].
 - exact (StrictReturn.decoded_r _ _ _ _ R).
Qed.

Lemma preserve pol e s u : inputs pol e s -> (forall r,In r sysv_saved -> regs u r=regs s r) ->
 preserved (fun x=>Rows.frame e+768<=x<sp e) (mem s) (mem u) -> inputs pol e u.
Proof.
 intros [G Rem Meta [Slots BP] Base Flags Valid] Keep M;destruct G as [Scratch [N Out]];constructor.
 - unfold Prologue.context_registers,Prologue.output_registers;rewrite (Keep 15%nat),(Keep 13%nat),(Keep 14%nat) by (simpl;tauto);auto.
 - rewrite Keep by (simpl;tauto);exact Rem.
 - eapply IndexStores.metadata_preserved;[|exact Meta];intros x X;apply M;unfold Rows.frame,sp in *;lia.
 - split;[intros x X;rewrite M;[apply Slots,X|unfold Rows.frame,sp in *;lia]|rewrite Keep by (simpl;tauto);exact BP].
 - rewrite <-Base;apply preserved_read with (outside:=fun x=>Rows.frame e+768<=x<sp e);[exact M|].
   intros k K;change (0<=k<8) in K;unfold Rows.frame,sp;lia.
 - intros j J;cbv zeta;rewrite M;[exact (Flags j J)|unfold Rows.frame,sp;lia].
 - intros j J;rewrite M;[exact (Valid j J)|unfold Rows.frame,sp;lia].
Qed.
Lemma at_hash pol bias pc e p q : inputs pol e (machine p) -> HashEntry.entry bias pc e p q -> inputs pol e (machine q).
Proof. intros Prep H;eapply preserve;[exact Prep|exact (HashEntry.saved _ _ _ _ _ H)|].
 intros x X;apply (HashEntry.other_bytes _ _ _ _ _ H);unfold span;lia. Qed.
Lemma after_hash pol bias o e q r s : inputs pol e (machine q) -> NativeHash.returned pol bias o e q r ->
 HashResume.compatible r s -> inputs pol e s.
Proof. intros I R C;apply (preserve _ _ _ _ I (HashResume.saved _ _ _ _ _ _ _ R C)).
 intros x X;rewrite (proj1 C);apply (NativeHash.frame _ _ _ _ _ _ R);right;lia. Qed.
