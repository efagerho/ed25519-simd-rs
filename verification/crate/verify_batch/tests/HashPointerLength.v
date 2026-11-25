From Coq Require Import List ZArith Bool.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.MaskedResult memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import ZipBytes.
Import ListNotations. Local Open Scope Z_scope.

(* Lane zero has message pointer 73 and length 2. The other lanes are
   disabled, with nonzero values left in their incoming vector registers. *)
Definition base:=65536.
Definition stack:=4096.
Definition image x:=if (base<=?x)&&(x<?base+Z.of_nat(length symbol_bytes)) then nth (Z.to_nat(x-base)) symbol_bytes 0
 else if x=?stack+640 then 73 else if x=?stack+704 then 2 else 0.
Definition initial:=Cursor (base+407) (CPU (fun _=>stack) (fun _ _=>91) None image) None [].
Example damaged_load_gives_the_pointer_as_length :
 match MaskedResult.execute base [ZeroRow 0 1 4 640] initial (fun _ j=>Nat.eqb j 0) with
 | Some(q,_)=>ip q=base+415 /\ vectors(machine q) 0%nat 0%nat=73 /\
     vectors(machine q) 0%nat 0%nat<>read_word image (stack+704) /\ vectors(machine q) 1%nat 0%nat=0
 | None=>False end.
Proof. vm_compute;repeat split;discriminate || reflexivity. Qed.
