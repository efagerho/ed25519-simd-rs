From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.LinkedCalls execution.MachineState execution.WordBounds.
From Ed25519Simd.VerifyBatch Require Import Policy Image Control Prepare Hash Candidate ProductRun Score Scatter.
Import ListNotations. Local Open Scope nat_scope.

Record local_state := Locals { incoming_masks:nat->nat->bool; incoming_tables:nat->data }.
Definition make_chunk e pol bias first n loc :=
 Chunk e first (Nat.min n 8) pol bias (incoming_masks loc) (incoming_tables loc).
Definition spatial c := Prepare.placement c /\ Hash.geometry c /\ Hash.abi c /\
                        buffers c /\ ProductRun.geometry c.
Definition entries e pol bias := forall first n loc, 0<n -> first+n=count e ->
 (forall t,data_words(incoming_tables loc t)) -> spatial (make_chunk e pol bias first n loc).

Inductive called c : list target -> (nat->Z) -> (nat->Z) -> Prop :=
 | rejected out result : ready c=false -> scoring c (fun _=>false) 0%Z out result ->
     called c [Prepare;Scatter] out result
 | checked result keys q m out final : ready c=true ->
     Hash.runs c=Some result -> key_selection c keys ->
     native_product c (Sha512Challenge.Execution.after result) keys q ->
     mask c q=Some m -> scoring c (enabled c) m out final ->
     called c [Prepare;Hash;Score] out final.

Lemma call_correct c out : spatial c -> constants (entry c) -> indices(entry c) ->
 0<live c<=8 -> first c+live c<=count(entry c) ->
 (exists final,called c (expected(ready c)) out final) /\
 forall final,called c (expected(ready c)) out final ->
   prefix (entry c) (mode c) (first c) out ->
   prefix (entry c) (mode c) (first c+live c) final.
Proof.
 intros [P [Geo [Hash [Buffers Space]]]] Tables Indices Live Limit.
 split.
 - destruct(ready c) eqn:On.
   + destruct (Hash.returns _ Hash) as [result [Run [Bytes Dig]]].
     destruct (select_keys c (rows_bytes c (entry_memory _ P))) as [keys Keys].
     destruct (product_exists _ _ _ P On Buffers Tables Keys Space Bytes) as [q Q].
     destruct (score_hash _ _ _ _ P On Geo Buffers Keys Dig Q) as [m [M Bits]].
     destruct (scatter_total c (enabled c) m out Live Limit Indices) as [final F].
     exists final;eapply checked;eassumption.
   + destruct(scatter_total c (fun _=>false) 0%Z out Live Limit Indices) as [final F].
     exists final;apply rejected;assumption.
 - intros final Call Before. destruct Call as [out final Off F|result keys q m out final On Run Keys Q M F].
   + eapply next_prefix;try eassumption. intros j J;cbn. split;[discriminate|].
     intro H;exfalso;exact(prepare_rejected _ P Off j ltac:(lia) H).
   + destruct(Hash.returns _ Hash) as [s [R [_ D]]]. rewrite R in Run;injection Run as <-.
     destruct(score_hash _ _ _ _ P On Geo Buffers Keys D Q) as [v [V Bits]].
     rewrite V in M;injection M as <-. eapply next_prefix;try eassumption. intros;apply Bits;lia.
Qed.

(* The recursive premise starts with the next descriptor and remaining count
   computed by the wrapper trace. The trace must reach the right exit. *)
Inductive batches e pol bias : nat -> nat -> (nat->Z) -> (nat->Z) -> Prop :=
 | done first n out final loc seg :
   0<n -> (forall t,data_words(incoming_tables loc t)) ->
   let c:=make_chunk e pol bias first n loc in
   chunk_trace n (ready c)=Some seg -> lanes seg=live c ->
   called c (calls seg) out final -> resume seg=Epilogue -> remaining seg=0 ->
   batches e pol bias first n out final
 | again first n out mid final loc seg :
   0<n -> (forall t,data_words(incoming_tables loc t)) ->
   let c:=make_chunk e pol bias first n loc in
   chunk_trace n (ready c)=Some seg -> lanes seg=live c ->
   called c (calls seg) out mid -> resume seg=Choose ->
   batches e pol bias (first+lanes seg) (remaining seg) mid final ->
   batches e pol bias first n out final.

Definition zero_loc := Locals (fun _ _=>false) (fun _=>Data (fun _ _=>0%Z) (fun _ _=>0%Z)).
Lemma zero_words t : data_words (incoming_tables zero_loc t).
Proof. split;intros;unfold word64;cbn;lia. Qed.

Section Run.
Variables (e:cpu) (pol:policy) (bias:Z).
Hypothesis Placed:entries e pol bias.
Hypothesis Tables:constants e.
Hypothesis Indices:indices e.
Lemma progress n : forall first out,0<n -> first+n=count e ->
 exists final,batches e pol bias first n out final.
Proof.
 induction n using lt_wf_ind. intros first out N Count.
 set (c:=make_chunk e pol bias first n zero_loc).
 pose proof(Placed first n zero_loc N Count zero_words) as Space.
 assert (L:0<live c<=8) by (unfold c;cbn [make_chunk live];lia).
 assert (End:first+live c<=count e) by (unfold c;cbn [make_chunk live];lia).
 destruct (proj1(call_correct c out Space Tables Indices L End)) as [mid Call].
 pose proof (chunk_trace_correct n (ready c) N) as T.
 destruct (Nat.eqb_spec (n-8) 0).
 - exists mid;eapply done with (loc:=zero_loc);try exact T;cbn;auto;try exact zero_words.
 - destruct (H (n-8) ltac:(lia) (first+Nat.min n 8) mid ltac:(lia) ltac:(lia)) as [final Finish].
   exists final;eapply again with (loc:=zero_loc) (mid:=mid);try exact T;cbn;auto;try exact zero_words.
Qed.

Local Opaque ready.
Lemma sound first n out final : batches e pol bias first n out final -> first+n=count e ->
 prefix e pol first out -> prefix e pol (count e) final.
Proof.
 intro Exec;induction Exec as [first n out final loc seg N W c T Active Call Exit End|
  first n out mid final loc seg N W c T Active Call Exit More IH];intros Count Before;
  rewrite (chunk_trace_correct _ _ N) in T;injection T as <-.
 all: cbn [calls resume remaining lanes] in Call, Active, Exit.
 1: cbn [remaining] in End.
 2: cbn [remaining lanes] in IH.
 - pose proof (proj2(call_correct c out (Placed _ _ _ N Count W) Tables Indices
     ltac:(unfold c;cbn [make_chunk live];lia) ltac:(unfold c;cbn [make_chunk Prepare.first live entry];lia))
      _ Call Before) as After.
   change (prefix e pol (first+Nat.min n 8) final) in After.
   replace (count e) with (first+Nat.min n 8) by lia;exact After.
 - apply IH;[lia|].
   exact (proj2(call_correct c out (Placed _ _ _ N Count W) Tables Indices
     ltac:(unfold c;cbn [make_chunk live];lia) ltac:(unfold c;cbn [make_chunk Prepare.first live entry];lia))
      _ Call Before).
Qed.
End Run.
