From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MappedFetch memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ScorePublish ZipVerdict.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition outputs pol e (m:FlatMemory.bytes):=forall j,(j<Nat.min (BatchWindow.remaining e) 8)%nat ->
 exists valid:bool,m(output e+Z.of_nat(Scatter.position e (BatchWindow.first+j)))=Z.b2z valid /\
 (valid=true <-> signature_accepts pol (read_input (mem e) (regs e 7%nat) (BatchWindow.first+j))).
Definition flags e p j:=mem(machine p)(Rows.frame e+856+Z.of_nat j).
Record verdict pol e p mask:Prop:=Verdict {
 bounded:0<=mask<256;
 binary:forall j,(j<8)%nat -> flags e p j=0 \/ flags e p j=1;
 accepts:forall j,(j<8)%nat -> (flags e p j=1 /\ Z.testbit mask (Z.of_nat j)=true <->
   signature_accepts pol (HashLayout.row e j))
}.

Lemma stored pol e p mask : verdict pol e p mask -> forall m,ScorePublish.stored e p mask m -> outputs pol e m.
Proof.
 intros [B F V] m Writes j J;assert(K:(j<8)%nat) by lia.
 exists ((flags e p j=?1) && Z.testbit mask (Z.of_nat j))%bool;split.
 - rewrite (Writes _ J);apply ScatterValues.bit_value;[apply F,K|exact B].
 - rewrite andb_true_iff,Z.eqb_eq,(V j K);unfold HashLayout.row;rewrite BatchWindow.own_row by lia;reflexivity.
Qed.

Theorem publish pol bias pc dst text e t p mask : Image.matches pc dst text -> StrictDispatch.bound pc text ->
 placement e -> loaded pol bias (mem e) (writable e) -> fits64 (bias+pc) (Z.of_nat(length text)) ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 (0<BatchWindow.remaining e)%nat -> Scatter.indices e -> ScoreTail.entry bias pc e t p mask -> verdict pol e p mask ->
 exists r,ScorePublish.scatter bias pc text p=Some r /\ RejectExecution.post_with (outputs pol e) (bias+pc) e r.
Proof.
 intros Code Bound P I Fit Map Sep N Idx Tail V.
 destruct(ScorePublish.publish_values _ _ _ _ _ _ _ _ _ Code Bound P I Fit Map Sep N Idx Tail) as [r [Run End]].
 exists r;split;[exact Run|exact (RejectExecution.post_map _ _ _ _ _ (stored _ _ _ _ V) End)].
Qed.

Lemma zip bias parent e p: ZipVerdict.result bias parent e p ->
 exists t m,ScoreTail.entry bias parent e t p m /\ verdict Zip215 e p m.
Proof.
 intro V;destruct(ZipVerdict.entry _ _ _ _ V) as [t [m E]];exists t,m;split;[exact E|].
 rewrite <-(proj1(ScoreTail.args _ _ _ _ _ _ E));constructor;
 [exact (ZipVerdict.mask_byte _ _ _ _ V)|exact (ZipVerdict.flag_byte _ _ _ _ V)|exact (ZipVerdict.lane _ _ _ _ V)].
Qed.
End Iteration.
