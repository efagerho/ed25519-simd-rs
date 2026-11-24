(* Execute the damaged transpose from the linked Stage address. Each of the
   forty source qwords carries a distinct tag. Only the shuffle immediate
   changed, so all stores still fit and the preparation call still executes. *)
From Coq Require Import List ZArith Bool.
From Machine Require Import execution.LinkedCalls execution.ScalarBytes execution.MappedFetch
 memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.VerifyBatch Require Import Image ZipBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition code := 65536.
Definition rows := 4096.
Definition stack := 32768.
Definition image x :=
 if (code<=?x)&&(x<?code+Z.of_nat(length symbol_bytes)) then nth (Z.to_nat (x-code)) symbol_bytes 0
 else if (rows<=?x)&&(x<?rows+320)&&((x-rows) mod 8=?0) then 1+(x-rows)/8 else 0.
Definition stage := CPU (fun r=>match r with 3%nat=>rows | 4%nat=>stack | _=>0 end)
 (fun _ _=>0) None image.

Example swapped_pointers_reach_preparation :
 match MappedFetch.run 42 (MappedFetch.fetch code (length symbol_bytes))
    (State (Running (offset Stage)) stage None) with
 | Some (t,_) => let m:=mem(cpu_state t) in
   (regs (cpu_state t) 4%nat=?stack-8) && (read_word m (stack-8)=?code+offset Prepared) &&
   forallb (fun j=>let key:=read_word m (stack+512+8*Z.of_nat j) in
     (key=?read_word image (rows+40*Z.of_nat j+16)) &&
     negb (key=?read_word image (rows+40*Z.of_nat j))) (seq 0 8)
 | None=>false end=true.
Proof. vm_compute;reflexivity. Qed.
