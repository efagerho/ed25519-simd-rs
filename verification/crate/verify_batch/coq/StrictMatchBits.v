From Coq Require Import ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require StrictCoordinate StrictEquality.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition selected e j A R:=StrictOrderClear.eligible e j /\
 decodes (little_endian(key_bytes(HashLayout.row e j))) A /\ decodes (BatchDecode.original_encoding true e j) R.
Lemma witnesses e j : StrictOrderClear.eligible e j -> exists A R,selected e j A R.
Proof.
 intro On;pose proof On as Full;destruct On as [[[S [D [A [DA Key]]]] Canon] [R [DR Strong]]].
 exists A,R;exact(conj Full (conj DA DR)).
Qed.
Definition passed_y e j:=exists A R,selected e j A R /\ StrictAxis.matches true e j A R.
Definition screened_mask e live:=forall j,(j<8)%nat -> (Z.testbit live (Z.of_nat j)=true <-> StrictOrderClear.eligible e j).
Definition y_mask e m:=forall j,(j<8)%nat -> (Z.testbit m (Z.of_nat j)=true <-> passed_y e j).
Definition verdict e m:=forall j,(j<8)%nat -> (Z.testbit m (Z.of_nat j)=true <-> signature_accepts Dalek (HashLayout.row e j)).

Lemma vertical e live mask:screened_mask e live -> StrictCoordinate.claim true e (fun j=>Z.testbit mask (Z.of_nat j)) ->
 y_mask e (Z.land live mask).
Proof.
 intros S C j J;rewrite Z.land_spec,andb_true_iff,(S j J);split.
 - intros [On Bit];destruct(witnesses _ _ On) as [A [R Sel]];destruct Sel as [Ok [DA DR]].
   exists A,R;split;[exact(conj Ok (conj DA DR))|exact (proj1(C j A R J (proj1(proj1 Ok)) DA DR) Bit)].
 - intros [A [R [[On [DA DR]] Y]]];split;[exact On|exact (proj2(C j A R J (proj1(proj1 On)) DA DR) Y)].
Qed.
Lemma accepted_y e j : byte_memory(mem e) -> signature_accepts Dalek (HashLayout.row e j) -> passed_y e j.
Proof.
 intros B Accept;destruct (witnesses _ _ (StrictAccept.screened _ _ Accept)) as [A [R [On [DA DR]]]].
 exists A,R;split;[exact(conj On (conj DA DR))|exact(proj2(proj2(StrictEquality.coordinates _ _ _ _ B On DA DR) Accept))].
Qed.
Lemma zero e : byte_memory(mem e) -> y_mask e 0 -> verdict e 0.
Proof.
 intros B Y j J;rewrite Z.bits_0;split;[discriminate|intro A;pose proof(proj2(Y j J)(accepted_y e j B A)) as X;now rewrite Z.bits_0 in X].
Qed.
Lemma horizontal e live mask:byte_memory(mem e) -> y_mask e live -> StrictCoordinate.claim false e (fun j=>Z.testbit mask (Z.of_nat j)) ->
 verdict e (Z.land live mask).
Proof.
 intros B Y C j J;rewrite Z.land_spec,andb_true_iff,(Y j J);split.
 - intros [[A [R [[On [DA DR]] Ey]]] Bit];apply (proj1(StrictEquality.coordinates _ _ _ _ B On DA DR));split;[|exact Ey].
   exact (proj1(C j A R J (proj1(proj1 On)) DA DR) Bit).
 - intro Acc;pose proof(accepted_y _ _ B Acc) as YOk;split;[exact YOk|].
   destruct YOk as [A [R [[On [DA DR]] _]]];exact(proj2(C j A R J (proj1(proj1 On)) DA DR)
     (proj1(proj2(StrictEquality.coordinates _ _ _ _ B On DA DR) Acc))).
Qed.
End Iteration.
