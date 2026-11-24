From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.StoreInstructions abi.TracedCalls memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* An interrupted child may not have a returning execution. Its store to
   the just-pushed return slot must still be visible to its parent. *)
Local Definition entry := CPU (fun r=>if Nat.eqb r 4 then 128 else 0)
 (fun _ _=>0) None (fun _=>0).
Local Definition escape := qword 32 120 5.
Local Definition incomplete : partial_call := fun ip e ws=>
 ip=32 /\ regs e 4%nat=120 /\ ws=[escape].
Example stopped_inside_call :
 let ws:=caller_stores 0 0 (Invoke 32) entry++[escape] in
 prefix (fun _ _ _ _ _=>False) incomplete 0 0 [Invoke 32;Return] entry ws /\
 ~confined (private_frame 64 120 (fun _=>False)) [escape].
Proof.
 split.
 - right;right;left. exists [escape];repeat split;reflexivity.
 - intro C;inversion C as [|w t A R];subst.
   specialize (A 120).
   assert (H:touches escape 120) by (change (120<=120<128);lia).
   destruct (A H) as [B|[]];lia.
Qed.
