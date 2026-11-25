(* Execute the damaged ADD in the linked first staging block. In a nine-row
   batch the next RBX names row seven, whose index has already been used. *)
From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.ScalarBytes execution.MappedFetch
 memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Image ZipBytes.
Local Open Scope Z_scope.

Definition code:=65536.
Definition rows:=4096.
Definition image x:=
 if ((code<=?x)&&(x<?code+Z.of_nat(length symbol_bytes)))%bool then nth (Z.to_nat(x-code)) symbol_bytes 0
 else if ((rows<=?x)&&(x<?rows+360)&&((x-rows) mod 40=?32))%bool then ((x-rows)/40+1) mod 9 else 0.
Definition before_add:=CPU (fun r=>if Nat.eqb r 3 then rows else 0) (fun _ _=>0) None image.

Example repeats_row_seven:
 match MappedFetch.run 1 (MappedFetch.fetch code (length symbol_bytes))
   (State(Running(offset PrepareArgs-7)) before_add None) with
 | Some(t,_)=>let s:=cpu_state t in
   ((regs s 3%nat=?rows+7*40)&&(read_word (mem s) (regs s 3%nat+32)=?8)&&
    (read_word image (rows+8*40+32)=?0))%bool
 | None=>false end=true.
Proof. vm_compute;reflexivity. Qed.
