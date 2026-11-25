From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.VectorProcedure execution.QwordBlock execution.InstructionRoute execution.Dependencies.
From Ed25519Simd.KeyTable Require Fields ObjectBytes.
From Ed25519Simd.Decode Require Power Kernels.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct.
Import ListNotations. Local Open Scope Z_scope.

Definition reserved r:=((5<=?r) && (r<?10) || (16<=?r))%nat%bool.
Definition operation f:=match f with Fields.Difference=>Fields.YMinusX | Fields.Sum=>Fields.YPlusX | Fields.Twice=>Fields.TwoZ end.
Definition save_register f:=match f with Fields.Difference=>5 | Fields.Sum=>16 | Fields.Twice=>21 end%nat.
Definition start f:=match f with Fields.Difference=>259 | Fields.Sum=>403 | Fields.Twice=>517 end.
Definition at_linear f:=match f with Fields.Difference=>329 | Fields.Sum=>473 | Fields.Twice=>587 end.
Definition keep f:=map (fun i=>Arithmetic ((save_register f+i)%nat,Instructions.Copy i)) (seq 0 5).
Definition linear f:=flat_map (fun i=>let rhs:=WithMemory (match f with Fields.Difference=>true | _=>false end) i i 12 (64*Z.of_nat i) in
 match f with Fields.Difference=>[Arithmetic(i,Add i (if Nat.eqb i 0 then 30 else 31));rhs]
 | Fields.Sum=>[rhs] | Fields.Twice=>[Arithmetic(i,Add i i)] end) (seq 0 5).

Lemma image f:linked KeyTable.ObjectBytes.symbol_bytes (route (start f) (keep f)) /\ linked KeyTable.ObjectBytes.symbol_bytes (route (at_linear f) (linear f)).
Proof. destruct f;split;apply checks_route;vm_compute;reflexivity. Qed.
Lemma keep_values f load v i : (i<5)%nat -> lane load v (keep f) (save_register f+i)%nat=v i.
Proof. intros N;destruct f;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. Qed.
Lemma keep_other f load v r : (r<save_register f \/ save_register f+5<=r)%nat -> lane load v (keep f) r=v r.
Proof.
 destruct f;cbn [save_register];intro Outside;cbn [keep map seq lane lane_step bits save_register];unfold put;
 repeat match goal with |-context[(?n=?r)%nat]=>rewrite (proj2(Nat.eqb_neq n r) ltac:(lia)) end;reflexivity.
Qed.
Lemma linear_other f load v r : (5<=r)%nat -> lane load v (linear f) r=v r.
Proof.
 intros High;destruct f;cbn [linear flat_map seq app lane lane_step bits];unfold put;
 repeat match goal with |-context[(?n=?r)%nat]=>rewrite (proj2(Nat.eqb_neq n r) ltac:(lia)) end;reflexivity.
Qed.
Definition known i:=((i<?5) || ((28<=?i) && (i<?32)))%nat%bool.
Lemma carry_reads i : (i<5)%nat ->
 agreement (fun _ _=>false) (Kernels.carry DecoderProduct.kernel) known i=true.
Proof. intros N;destruct i as [|[|[|[|[|i]]]]];[vm_compute;reflexivity..|lia]. Qed.
Lemma saved_after load r i : reserved i=true ->
 Instructions.run load (Kernels.carry DecoderProduct.kernel) r i=r i.
Proof.
 intro H;apply untouched;apply forallb_forall;intros op Member.
 assert (C:forallb (fun op=>negb(reserved(fst op))) (Kernels.carry DecoderProduct.kernel)=true) by (vm_compute;reflexivity).
 apply (proj1(forallb_forall _ _) C) in Member;apply Bool.negb_true_iff,Nat.eqb_neq;intros Eq;rewrite Eq,H in Member;discriminate.
Qed.

Definition reference f x y:=Instructions.run no_read (Fields.prefix f) (Power.feed x y).
Lemma prefix_inputs f load v x y :
 (forall i,(i<5)%nat -> v i=x i) -> (f<>Fields.Twice -> forall i,(i<5)%nat -> load 12%nat (64*Z.of_nat i)=y i) ->
 (forall i,(i<4)%nat -> v (28+i)%nat=DecoderFrame.constant i) ->
 forall i,known i=true -> lane load v (linear f) i=reference f x y i.
Proof.
 intros X Y C i K;unfold known in K;apply orb_true_iff in K as [Low|High].
 - pose proof(C 2%nat ltac:(lia)) as C30;change (v 30%nat=DecoderFrame.constant 2) in C30.
   pose proof(C 3%nat ltac:(lia)) as C31;change (v 31%nat=DecoderFrame.constant 3) in C31.
   apply Nat.ltb_lt in Low;destruct i as [|[|[|[|[|i]]]]];try lia;
   destruct f;cbn [linear reference Fields.prefix flat_map seq app lane lane_step Instructions.run bits
   put Nat.eqb Nat.add];rewrite ?C30,?C31;
   repeat match goal with |-context[load 12%nat ?off]=>let i:=eval vm_compute in (Z.to_nat(off/64)) in
    rewrite (Y ltac:(discriminate) i ltac:(lia)) end;
   repeat match goal with |-context[v ?k]=>rewrite (X k ltac:(lia)) end;reflexivity.
 - apply andb_true_iff in High as [Lo Hi];apply Nat.leb_le in Lo;apply Nat.ltb_lt in Hi;rewrite linear_other by lia.
   unfold reference;rewrite untouched.
   + replace i with (28+(i-28))%nat at 1 by lia;rewrite C by lia;assert (i=28%nat \/ i=29%nat \/ i=30%nat \/ i=31%nat) by lia;destruct H as [A|[A|[A|A]]];subst i;reflexivity.
   + apply forallb_forall;intros ins M;assert (Small:forallb (fun ins=>(fst ins<?5)%nat) (Fields.prefix f)=true)
      by (destruct f;vm_compute;reflexivity).
     apply (proj1(forallb_forall _ _) Small) in M;apply Bool.negb_true_iff,Nat.eqb_neq;apply Nat.ltb_lt in M;lia.
Qed.

Theorem column f load v x y :
 (forall i,(i<5)%nat -> v i=x i) -> (f<>Fields.Twice -> forall i,(i<5)%nat -> load 12%nat (64*Z.of_nat i)=y i) ->
 (forall i,(i<4)%nat -> v (28+i)%nat=DecoderFrame.constant i) ->
 forall i,(i<5)%nat -> Instructions.run no_read (Kernels.carry DecoderProduct.kernel) (lane load v (linear f)) i=
 Fields.linear_result DecoderProduct.kernel f x y i.
Proof.
 intros X Y C i N;unfold Fields.linear_result,Fields.linear_code;rewrite run_app.
 apply (agreement_sound (fun _ _=>false) _ known);[discriminate|apply prefix_inputs;assumption|apply carry_reads,N].
Qed.
