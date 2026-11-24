From Coq Require Import List ZArith Bool FSets.FMapPositive.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Decode Require DecoderBytes.
From Ed25519Simd.VerifyBatch Require Import DecoderUnpack DecoderSave BatchDecode.
From Ed25519Simd.VerifyBatch Require RejectedBatch.
Local Open Scope Z_scope.

(* Lane zero encodes 2. All other lanes encode p+1 and set the sign bit.
   Start immediately after the word transpose, with all mask bits dirty. *)
Definition code_end:=DecoderBytes.address+Z.of_nat(length DecoderBytes.symbol_bytes).
Definition scratch:=64*(code_end/64+2).
Definition image:=RejectedBatch.install (Z.to_pos DecoderBytes.address) DecoderBytes.symbol_bytes (PositiveMap.empty Z).
Definition memory x:=match PositiveMap.find (Z.to_pos x) image with Some b=>b |None=>0 end.
Definition key j:=if Nat.eqb j 0 then 2 else 2^255+prime+1.
Definition source j (r:nat):=match r with
 | 29%nat=>2^51-1 | 0%nat=>key j mod 2^64 | 4%nat=>key j/2^64 mod 2^64
 | 2%nat=>key j/2^128 mod 2^64 | 6%nat=>key j/2^192 mod 2^64 | _=>0 end.
Definition initial:=CPU (fun r=>if Nat.eqb r 7 then scratch+1024 else scratch) source None memory.
Definition trial:=let p:=Cursor (DecoderBytes.address+355) initial None nil in
 match unpack 0 p (fun _ _=>true) with None=>false | Some (y,_)=>match preserve 0 y with
 | None=>false | Some q=>let s:=machine q in (ip q=?DecoderBytes.address+497) && (regs s 0%nat=?254) &&
 (Nat.eqb (length(log q)) 5) && forallb (fun j=>Radix51.limbs (digits initial s j)=? key j mod 2^255) (seq 0 8)
 end end.
Example signs_and_noncanonical_y : trial=true.
Proof. lazy;reflexivity. Qed.
