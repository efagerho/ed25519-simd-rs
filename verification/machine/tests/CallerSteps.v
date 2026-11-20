From Coq Require Import ZArith.
From Machine Require Import execution.LinkedCalls execution.WordSemantics memory.ByteMemory.
Local Open Scope Z_scope.

Local Definition entry := CPU (fun r => if Nat.eqb r 12 then 3 else 0)
                              (fun _ _ => 0) None (fun _ => 0).

Example lea_high_base_negative_displacement :
 regs (snd (caller_step 0 0 (LeaSIB 13 12 (-8)) entry)) 13%nat = 2^64-5.
Proof. reflexivity. Qed.

Example backward_relocated_call :
 let '(ip, callee) := caller_step 100 20 (Invoke 4) entry in
 ip = 104 /\ regs callee 4%nat = 2^64-8 /\
 read_word (mem callee) (2^64-8) = 125 /\
 let '(ret, caller) := caller_step 100 4 Return callee in
 ret = 125 /\ regs caller 4%nat = 0.
Proof. repeat split; reflexivity. Qed.
