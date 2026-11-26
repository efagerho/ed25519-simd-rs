From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return BatchScalar BatchDecode.
From Ed25519Simd.VerifyBatch Require ChunkScalar RejectExecution RejectedPath EligibleLanes ReadyDispatch NativeHash StrictDispatch.
Local Open Scope Z_scope.

Inductive boundary:=Completed (q:cursor) | MoreChunks (q:cursor)
 | HashReturned (entry:cursor) (result:Sha512Challenge.Execution.observation).
Definition after_reject r:=match r with RejectExecution.BatchReturned q=>Completed q | RejectExecution.NextChunk q=>MoreChunks q end.
Definition hash_return bias q:=option_map (HashReturned q) (NativeHash.execute bias q).
Definition after_filter bias v:=match v with StrictDispatch.Zero r=>Some(after_reject r) | StrictDispatch.HashCall h=>hash_return bias h end.
Definition continue pol bias pc text (q:cursor) ks:=match pol with
 | Zip215=>hash_return bias q
 | Dalek=>bind (StrictReturn.observe bias q ks) (fun '(a,k)=>bind (StrictDispatch.execute bias pc text a k) (after_filter bias)) end.
(* Once the decoder has returned, the first and subsequent windows execute
   exactly the same branches on R14 and the same policy-specific calls. *)
Definition after_eligible pol bias pc text e t :=
 let q:=EligibleLanes.stopped t in
 if regs(machine q) 14%nat=?0 then option_map after_reject (RejectedPath.execute true pol bias pc text q)
 else bind (ReadyDispatch.observe pol bias pc text e q (TableMask.masks t))
           (fun result=>continue pol bias pc text (fst result) (snd result)).
Definition after_decode pol bias pc text e bank d :=
 bind (EligibleLanes.observe pol bias e d bank) (after_eligible pol bias pc text e).
Definition after_scalar pol bias pc text e scalar bank :=
 if regs(machine scalar) 0%nat mod 2^32=?0 then option_map after_reject (RejectedPath.execute false pol bias pc text scalar)
 else bind (BatchDecode.enter bias scalar) (after_decode pol bias pc text e bank).

Definition dispatch pol bias pc text e p masks :=
 bind (ChunkScalar.execute pol bias p masks) (fun '(s,bank)=>after_scalar pol bias pc text e s bank).
Definition run pol bias pc text e c masks :=
 bind (StageEntry.begin (bias+pc) text e c) (fun p=>dispatch pol bias pc text e p masks).
