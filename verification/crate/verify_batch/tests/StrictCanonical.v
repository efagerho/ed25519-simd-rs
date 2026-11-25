From Coq Require Import List ZArith Bool FSets.FMapPositive.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.FlatMemory memory.ByteMemory.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Decode Require DecoderBytes HelperBytes.
From Ed25519Simd.DalekPostHash Require DecodedBytes.
From Ed25519Simd.VerifyBatch Require StrictRCanonical RejectedBatch.
Import ListNotations. Local Open Scope Z_scope.

Definition entry:=DalekPostHash.DecodedBytes.address.
Definition install base bytes m:=RejectedBatch.install (Z.to_pos base) bytes m.
Definition fragment base off len bytes:=install (base+Z.of_nat off) (firstn len(skipn off bytes)).
Definition image:=fragment entry 67 95 DalekPostHash.DecodedBytes.symbol_bytes
 (fragment Decode.DecoderBytes.address 2952 8 Decode.DecoderBytes.symbol_bytes
 (fragment Decode.HelperBytes.address 3560 8 Decode.HelperBytes.symbol_bytes (PositiveMap.empty Z))).

(* Include a value whose low limb passes the threshold but whose high
   limbs differ from p, alongside encodings immediately either side of p. *)
Definition y j:=match j with O=>prime-1 | S O=>prime | S (S O)=>prime+1
 | S (S (S O))=>radix-1 | _=>2^255-1 end.
Definition point:=2^20.
Definition memory (damaged:bool) x:=if (point+320<=?x)&&(x<?point+640)
 then let offset:=x-(point+320) in
      word_byte (y (Z.to_nat(offset mod 64/8))/radix^(offset/64) mod radix) (offset mod 8)
 else if damaged && (x=?Decode.DecoderBytes.address+0xb88) then 238
 else match PositiveMap.find (Z.to_pos x) image with Some b=>b |None=>0 end.
Definition trial damaged live:=let s:=CPU (fun g=>if Nat.eqb g 3 then point else if Nat.eqb g 12 then live else 0)
 (fun _ _=>2^64-1) None (memory damaged) in
 match StrictRCanonical.execute 0 (Cursor (entry+67) s (Some true) []) (fun _ _=>true) with
 |Some q=>Some (ip q-entry,regs(machine q) 12%nat,length(log q)) |None=>None end.

Example cutoff_and_high_limbs : trial false 255=Some (162,9,0%nat).
Proof. vm_compute;reflexivity. Qed.
Example equality_alone_takes_rejection : trial false 2=Some (554,0,0%nat).
Proof. vm_compute;reflexivity. Qed.

(* Changing the low byte of the linked cutoff from 0xed to 0xee admits p. *)
Example damaged_cutoff_admits_equality : trial true 2=Some (162,2,0%nat).
Proof. vm_compute;reflexivity. Qed.
