From Coq Require Import List Bool ZArith.
From Ed25519Simd.Dalek Require ObjectBytes Audit.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes.
From Ed25519Simd.SmallOrder Require EntryBytes HelperBytes.
From Ed25519Simd.Radix16 Require LinkedBytes.
From Ed25519Simd.FullLadder Require LinkedBytes.
From Ed25519Simd.Zip215 Require Caller.
From Ed25519Simd.DalekPostHash Require Import Caller.
From Ed25519Simd.DalekPostHash Require CandidateBytes PushBytes FlushBytes DecodedBytes FilterBytes ScatterBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition wrappers := [Candidate;Push;Flush;Decoded;Filter].
Definition pc s := match s with
 | Candidate=>CandidateBytes.address | Push=>PushBytes.address | Flush=>FlushBytes.address
 | Decoded=>DecodedBytes.address | Filter=>FilterBytes.address | Scatter=>ScatterBytes.address
 | Digest=>Radix16.LinkedBytes.wrapper_pc | Ladder=>FullLadder.LinkedBytes.entry_pc
 | Small=>SmallOrder.EntryBytes.address | Exact=>Dalek.ObjectBytes.address
 | Decoder=>Decode.DecoderBytes.address | Helper=>Decode.HelperBytes.address end.
Definition raw s := match s with
 | Candidate=>CandidateBytes.symbol_bytes | Push=>PushBytes.symbol_bytes | Flush=>FlushBytes.symbol_bytes
 | Decoded=>DecodedBytes.symbol_bytes | Filter=>FilterBytes.symbol_bytes | Scatter=>ScatterBytes.symbol_bytes
 | Digest=>Radix16.LinkedBytes.symbol_bytes | Ladder=>FullLadder.LinkedBytes.symbol_bytes
 | Small=>SmallOrder.EntryBytes.symbol_bytes | Exact=>Dalek.ObjectBytes.symbol_bytes
 | Decoder=>Decode.DecoderBytes.symbol_bytes | Helper=>Decode.HelperBytes.symbol_bytes end.
Definition linked_image :=
 (forall s,In s wrappers -> image pc s=raw s /\ forallb (fits pc s) (order s)=true) /\
 Zip215.Caller.image (fun _=>pc Scatter) Zip215.Caller.Scatter=raw Scatter /\
 pc Helper=SmallOrder.HelperBytes.address /\ raw Helper=SmallOrder.HelperBytes.symbol_bytes /\
 Dalek.Audit.linked (map (fun s=>Dalek.Audit.span (pc s) (raw s))
 (wrappers++[Scatter;Digest;Ladder;Small;Exact;Decoder;Helper]))=true.
