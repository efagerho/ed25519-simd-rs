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

From Coq Require Import List.
From Machine Require execution.ScalarBytes execution.MappedFetch.
Import ListNotations.

(* 32-bit MOV clears the upper half of the destination. CMP sign-extends
   its byte immediate before comparing the low 32 bits. *)
Example narrow_move_and_compare :
 let code:=[0x41;0x89;0xc5;0x41;0x83;0xfc;0xff] in
 let initial:=CPU (fun r=>if Nat.eqb r 0 then 2^40+7 else 2^64-1) (fun _ _=>0) None (fun _=>0) in
 match MappedFetch.run 2 (ScalarBytes.fetch 0 code)
   (ScalarBytes.State (ScalarBytes.Running 0) initial None) with
 | Some (s,[])=>ScalarBytes.loc s=ScalarBytes.Running 7 /\ regs (ScalarBytes.cpu_state s) 13%nat=7 /\
   flag (ScalarBytes.cpu_state s)=Some true /\ ScalarBytes.cf s=Some false
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

Example signed_add_to_rsi :
 let code:=[0x48;0x81;0xc6;0xff;0xff;0xff;0xff] in
 let initial:=CPU (fun _=>1) (fun _ _=>0) None (fun _=>0) in
 match MappedFetch.run 1 (ScalarBytes.fetch 0 code)
   (ScalarBytes.State (ScalarBytes.Running 0) initial None) with
 | Some (s,[])=>ScalarBytes.loc s=ScalarBytes.Running 7 /\ regs (ScalarBytes.cpu_state s) 6%nat=0 /\
   flag (ScalarBytes.cpu_state s)=Some true /\ ScalarBytes.cf s=Some true
 | _=>False end.
Proof. repeat split;reflexivity. Qed.
