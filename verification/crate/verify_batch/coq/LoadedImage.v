From Coq Require Import List ZArith Lia.
From Machine Require Import memory.ByteMemory memory.ByteExecution memory.WriteTrace memory.MemoryGeometry.
From Machine Require execution.MappedFetch.
From Ed25519Simd.SignatureScalar Require ObjectBytes OrderBytes.
From Ed25519Simd.Sha512Challenge Require ObjectBytes LiteralBytes.
From Ed25519Simd.KeyTable Require ObjectBytes.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes.
From Ed25519Simd.Pow2 Require ObjectBytes.
From Ed25519Simd.Scalar Require ObjectBytes.
From Ed25519Simd.Radix16 Require LinkedBytes.
From Ed25519Simd.CachedAdd Require ObjectBytes.
From Ed25519Simd.Double4 Require ObjectBytes.
From Ed25519Simd.LadderStep Require LinkedBytes.
From Ed25519Simd.FullLadder Require LinkedBytes.
From Ed25519Simd.StageRound Require ObjectBytes.
From Ed25519Simd.SmallOrder Require EntryBytes HelperBytes.
From Ed25519Simd.Zip215 Require CandidateBytes DecodedBytes ScatterBytes.
From Ed25519Simd.DalekPostHash Require CandidateBytes DecodedBytes FilterBytes.
From Ed25519Simd.PrepareChunk Require CommonBytes StrictBytes.
From Ed25519Simd.VerifyBatch Require Import Policy BaseTable IdentityTable.
Import ListNotations. Local Open Scope Z_scope.

(* Exact extents from the same linked ELF as the component theorems.
   Internal labels and inline literals belong to the containing extent. *)
Definition common : list (Z*list Z) :=
 [(CommonBytes.address,CommonBytes.symbol_bytes);
  (SignatureScalar.ObjectBytes.address,SignatureScalar.ObjectBytes.symbol_bytes);
  (OrderBytes.address,OrderBytes.symbol_bytes);
  (Sha512Challenge.ObjectBytes.address,Sha512Challenge.ObjectBytes.symbol_bytes);
  (LiteralBytes.address,LiteralBytes.symbol_bytes);
  (Decode.DecoderBytes.address,Decode.DecoderBytes.symbol_bytes);
  (Decode.DecoderBytes.pow_pc,Pow2.ObjectBytes.symbol_bytes);
  (Decode.HelperBytes.address,Decode.HelperBytes.symbol_bytes);
  (KeyTable.ObjectBytes.address,KeyTable.ObjectBytes.symbol_bytes);
  (Radix16.LinkedBytes.wrapper_pc,Radix16.LinkedBytes.symbol_bytes);
  (Radix16.LinkedBytes.reducer_pc,Scalar.ObjectBytes.symbol_bytes);
  (FullLadder.LinkedBytes.entry_pc,FullLadder.LinkedBytes.symbol_bytes);
  (FullLadder.LinkedBytes.stage_pc,StageRound.ObjectBytes.symbol_bytes);
  (LadderStep.LinkedBytes.wrapper_pc,LadderStep.LinkedBytes.symbol_bytes);
  (LadderStep.LinkedBytes.double4_pc,Double4.ObjectBytes.symbol_bytes);
  (LadderStep.LinkedBytes.cached_pc,CachedAdd.ObjectBytes.symbol_bytes);
  (Zip215.ScatterBytes.address,Zip215.ScatterBytes.symbol_bytes)].
Definition children mode := common ++ match mode with
 | Zip215=>[(Zip215.DecodedBytes.address,Zip215.DecodedBytes.symbol_bytes);
            (Zip215.CandidateBytes.address,Zip215.CandidateBytes.symbol_bytes)]
 | Dalek=>[(StrictBytes.address,StrictBytes.symbol_bytes);
           (DalekPostHash.DecodedBytes.address,DalekPostHash.DecodedBytes.symbol_bytes);
           (DalekPostHash.CandidateBytes.address,DalekPostHash.CandidateBytes.symbol_bytes);
           (DalekPostHash.FilterBytes.address,DalekPostHash.FilterBytes.symbol_bytes);
           (SmallOrder.EntryBytes.address,SmallOrder.EntryBytes.symbol_bytes);
           (SmallOrder.HelperBytes.address,SmallOrder.HelperBytes.symbol_bytes)] end.

Definition static_tables : list (Z*Z) := [(BaseTable.address,273*120);(IdentityTable.address,17*160)].
Definition extent bias a n x := bias+a<=x<bias+a+n.
Definition readonly mode bias x :=
 (exists a bs,In (a,bs) (children mode) /\ extent bias a (Z.of_nat(length bs)) x) \/
 (exists a n,In (a,n) static_tables /\ extent bias a n x).
Record loaded mode bias m allowed : Prop := {
 symbols : forall a bs,In (a,bs) (children mode) ->
   fits64 (bias+a) (Z.of_nat(length bs)) /\ MappedFetch.mapped m (bias+a) bs;
 tables_fit : forall a n,In (a,n) static_tables -> fits64 (bias+a) n;
 immutable : forall x,readonly mode bias x -> ~allowed x
}.
Lemma after mode bias m allowed ws : loaded mode bias m allowed -> confined allowed ws ->
 loaded mode bias (replay m ws) allowed.
Proof.
 intros [Map Tab Apart] W;constructor;[|exact Tab|exact Apart].
 intros a bs I;destruct (Map a bs I) as [Range Exact];split;[exact Range|].
 eapply MappedFetch.keep_image;[exact Exact| |exact W];intros x InRange;apply Apart.
 left;exists a,bs;auto.
Qed.
Lemma scatter mode : In (Zip215.ScatterBytes.address,Zip215.ScatterBytes.symbol_bytes) (children mode).
Proof. apply in_or_app;left;unfold common;do 16 right;left;reflexivity. Qed.
