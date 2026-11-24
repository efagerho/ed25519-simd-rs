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

(* AND RSP,-64 and a negative RIP-relative VPBROADCASTQ at a nonzero PC. *)
Example decoder_frame_and_literal :
 let s:=CPU (fun _=>127) (fun _ _=>11) None (fun x=>if x=?0x1000 then 7 else 0) in
 let start:=ScalarBytes.State (ScalarBytes.Running 0) s None in
 (exists t,ScalarBytes.fetch 0 [0x48;0x83;0xe4;0xc0] start=Some(t,[]) /\
  regs (ScalarBytes.cpu_state t) 4%nat=64 /\ ScalarBytes.cf t=Some false) /\
 (exists t,ScalarBytes.fetch 0x1004 [0x62;0x62;0xfd;0x48;0x59;0x35;0xf2;0xff;0xff;0xff] start=Some(t,[]) /\
  vectors (ScalarBytes.cpu_state t) 7%nat 30%nat=7 /\ vectors (ScalarBytes.cpu_state t) 7%nat 29%nat=11).
Proof. split;eexists;repeat split;reflexivity. Qed.

Example two_table_permutation :
 let s:=CPU (fun _=>0) (fun j r=>if Nat.eqb r 8 then 8+Z.of_nat j else
   if Nat.eqb r 5 then 40+Z.of_nat j else 10+Z.of_nat j) None (fun _=>0) in
 exists t,ScalarBytes.fetch 0 [0x62;0xf2;0xbd;0x48;0x7e;0xc5]
   (ScalarBytes.State (ScalarBytes.Running 0) s None)=Some(t,[]) /\
   vectors (ScalarBytes.cpu_state t) 2%nat 0%nat=42.
Proof. eexists;split;reflexivity. Qed.

Example aligned_zmm_literal :
 let bs:=[0x62;0x71;0xfd;0x48;0x6f;0x05;0xf6;0xff;0xff;0xff] in
 let fetch pc:=ScalarBytes.fetch pc bs (ScalarBytes.State (ScalarBytes.Running 0) entry None) in
 fetch 63=None /\ exists t,fetch 64=Some(t,[]) /\ vectors (ScalarBytes.cpu_state t) 7%nat 8%nat=0x0707070707070707.
Proof. split;[reflexivity|eexists;split;reflexivity]. Qed.

From Machine Require execution.MaskTransfer.
Example sign_mask_clears_upper_bits :
 let s:=CPU (fun _=>0) (fun lane _=>if Nat.eqb lane 7 then 2^63 else 0) None (fun _=>0) in
 let '(t,k):=MaskTransfer.effect s (fun _ _=>true) (MaskTransfer.Signs 2 6) in
 let '(out,_):=MaskTransfer.effect t k (MaskTransfer.ToEax 2) in
 regs out 0%nat=128 /\ k 2%nat 15%nat=false /\ k 1%nat 15%nat=true.
Proof. vm_compute;auto. Qed.

Example aligned_zmm_base_moves :
 let memop pc op base:=ScalarBytes.fetch pc op (ScalarBytes.State (ScalarBytes.Running 0)
    (CPU (fun _=>base) (fun j r=>Z.of_nat (32*j+r)) None (fun _=>1)) None) in
 let store:=[0x62;0xf1;0xfd;0x48;0x7f;0x47;0x05] in
 let load:=[0x62;0xd1;0xfd;0x48;0x6f;0x28] in
 memop 17 store 1=None /\ memop 42 load 1=None /\
 (exists t w,memop 17 store 64=Some(t,[w]) /\ pc w=17 /\ address w=384 /\ size w=64%nat /\
    mem (ScalarBytes.cpu_state t) (384+56)=224) /\
 (exists t,memop 42 load 64=Some(t,[]) /\ vectors (ScalarBytes.cpu_state t) 7%nat 5%nat=0x0101010101010101) /\
 ScalarBytes.decode load=Some(6%nat,ScalarBytes.AlignedRow(VectorMoves.Row false 5 8 0)).
Proof. split;[reflexivity|split;[reflexivity|split;[do 2 eexists;repeat split;reflexivity|]]].
 split;[eexists;split;reflexivity|reflexivity]. Qed.

Example rip_broadcast_subtraction :
 let bytes:=[0x62;0xf1;0xfd;0x58;0xfb;0x2d;0xf6;0xff;0xff;0xff] in
 let s:=CPU (fun _=>0) (fun j _=>Z.of_nat j) None (fun x=>if x=?48 then 1 else 0) in
 exists t,ScalarBytes.fetch 48 bytes (ScalarBytes.State (ScalarBytes.Running 0) s None)=Some(t,[]) /\
 vectors (ScalarBytes.cpu_state t) 0%nat 5%nat=2^64-1 /\
 vectors (ScalarBytes.cpu_state t) 7%nat 5%nat=6.
Proof. eexists;repeat split;reflexivity. Qed.
