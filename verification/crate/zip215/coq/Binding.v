From Coq Require Import ZArith List Bool.
From Ed25519Simd.Dalek Require ObjectBytes Audit.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes.
From Ed25519Simd.Radix16 Require LinkedBytes.
From Ed25519Simd.FullLadder Require LinkedBytes.
From Ed25519Simd.Torsion Require ObjectBytes.
From Ed25519Simd.Zip215 Require Import Caller.
From Ed25519Simd.Zip215 Require CandidateBytes ScatterBytes DecodedBytes PushBytes CheckRBytes FlushBytes.
Import ListNotations. Open Scope Z_scope.

Definition wrappers := [Candidate;Scatter;Decoded;Push;CheckR;Flush].
Definition pc s := match s with
 | Candidate=>CandidateBytes.address | Scatter=>ScatterBytes.address
 | Decoded=>DecodedBytes.address | Push=>PushBytes.address
 | CheckR=>CheckRBytes.address | Flush=>FlushBytes.address
 | Digest=>Radix16.LinkedBytes.wrapper_pc | Ladder=>FullLadder.LinkedBytes.entry_pc
 | Torsion=>HelperBytes.address | DecodeR=>DecoderBytes.address | Exact=>Dalek.ObjectBytes.address end.
Definition raw s := match s with
 | Candidate=>CandidateBytes.symbol_bytes | Scatter=>ScatterBytes.symbol_bytes
 | Decoded=>DecodedBytes.symbol_bytes | Push=>PushBytes.symbol_bytes
 | CheckR=>CheckRBytes.symbol_bytes | Flush=>FlushBytes.symbol_bytes
 | Digest=>Radix16.LinkedBytes.symbol_bytes | Ladder=>FullLadder.LinkedBytes.symbol_bytes
 | Torsion=>Torsion.ObjectBytes.symbol_bytes | DecodeR=>DecoderBytes.symbol_bytes
 | Exact=>Dalek.ObjectBytes.symbol_bytes end.

Definition linked_image :=
 (forall s, In s wrappers -> image pc s=raw s /\ forallb (fits pc s) (order s)=true) /\
 HelperBytes.symbol_bytes=Torsion.ObjectBytes.symbol_bytes /\
 Dalek.Audit.linked (map (fun s=>Dalek.Audit.span (pc s)(raw s))
   (wrappers++[Digest;Ladder;Torsion;DecodeR;Exact]))=true.
