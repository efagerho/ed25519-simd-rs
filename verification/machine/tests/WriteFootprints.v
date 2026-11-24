From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.StoreInstructions memory.WriteTrace memory.FlatMemory.
Import ListNotations. Local Open Scope Z_scope.

(* MOV [rsi+r9],r10b. RSI=100, R9=1 points one past a one-byte output.
   The source and destination both contain 7. Check this instruction's own
   encoding and run it without consulting the permission predicate. *)
Local Definition mov := IndexedByte 10 6 9.
Local Definition entry := CPU (fun r=>match r with
 | 6%nat=>100 | 9%nat=>1 | 10%nat=>7 | _=>0 end)
 (fun _ _=>0) None (fun _=>7).
Example same_byte_escape :
 byte_encoding mov = Some [0x46;0x88;0x14;0x0e] /\
 let '(out,ws):=byte_step 32 mov entry in
 (forall a, mem out a=mem entry a) /\
 ~confined (fun x=>100<=x<101) ws.
Proof.
 split;[reflexivity|]. split.
 - intro x;change (write_bytes (fun _=>7) 101 1 (fun _=>7) x=7).
   unfold write_bytes;destruct (_ && _)%bool;reflexivity.
 - intro C;inversion C as [|w t Allowed Rest];subst.
   specialize (Allowed 101). change ((101<=101<102)->100<=101<101) in Allowed;lia.
Qed.

Example masked_boundary :
 confined (fun x=>0<=x<56) (masked_qwords 42 0 (fun j=>Nat.ltb j 7) (fun _=>0)) /\
 ~confined (fun x=>0<=x<56) (masked_qwords 42 0 (fun _=>true) (fun _=>0)).
Proof.
 split.
 - apply Forall_forall. intros w W x X. destruct (proj1 (masked_footprint 42 0 _ (fun _=>0) x)
     (ex_intro _ w (conj W X))) as [j [J [Mask B]]]. apply Nat.ltb_lt in Mask;lia.
 - intro C. assert (H:exists w,In w (masked_qwords 42 0 (fun _=>true) (fun _=>0)) /\ touches w 56).
   { apply masked_footprint. exists 7%nat;repeat split;try reflexivity;lia. }
   destruct H as [w [W X]]. unfold confined in C;rewrite Forall_forall in C. specialize (C w W 56 X);change (0<=56<56) in C;lia.
Qed.

From Machine Require execution.ScalarBytes.
Local Definition ymm_store (aligned:bool) base :=
 let code:= [0xc5;if aligned then 0xfd else 0xfe;0x7f;0x04;0x0b] in
 let s:=CPU (fun r=>if Nat.eqb r 3 then base else 0) (fun _ _=>0) None (fun _=>0) in
 ScalarBytes.fetch 0 code (ScalarBytes.State (ScalarBytes.Running 0) s None).
Example aligned_ymm_store :
 ymm_store true 31=None /\
 (exists s w,ymm_store true 32=Some(s,[w]) /\ address w=32 /\ size w=32%nat) /\
 (exists s w,ymm_store false 31=Some(s,[w]) /\ address w=31 /\ size w=32%nat).
Proof. split;[reflexivity|split];do 2 eexists;repeat split;reflexivity. Qed.
