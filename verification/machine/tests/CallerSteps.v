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

Example decoder_register_moves :
 ScalarBytes.decode [0x40;0x89;0xdf]=Some(3%nat,ScalarBytes.Copy32 7 3) /\
 ScalarBytes.decode [0x48;0x89;0xdf]=Some(3%nat,ScalarBytes.CopyG 7 3) /\
 ScalarBytes.decode [0x45;0x89;0xe9]=Some(3%nat,ScalarBytes.Copy32 9 13) /\
 ScalarBytes.decode [0x4c;0x89;0xff]=Some(3%nat,ScalarBytes.CopyG 7 15) /\
 ScalarBytes.reg_move 0x48 0x84=None.
Proof. repeat split;reflexivity. Qed.

Example signed_short_jumps :
 ScalarBytes.decode [0xeb;8]=Some(2%nat,ScalarBytes.Jump 8) /\
 ScalarBytes.decode [0xeb;0xfe]=Some(2%nat,ScalarBytes.Jump (-2)).
Proof. split;reflexivity. Qed.

From Coq Require Import Lia.
From Machine Require isa.X86.

Example rip_broadcast_all_registers (r:nat) : (r<32)%nat ->
 ScalarBytes.decode (X86.prefix 2 1 (Z.of_nat r) 0 5 ++
    [0x59;X86.modrm 0 (Z.of_nat r) 5;0xff;0xff;0xff;0xff])=
 Some(10%nat,ScalarBytes.BroadcastRip r (-1)).
Proof. intro R;do 32 (destruct r as [|r];[reflexivity|]);lia. Qed.

Example rip_broadcast_requires_rip :
 ScalarBytes.broadcast_reg 0xf2 0x2c=None /\
 ScalarBytes.broadcast_reg 0xf2 0x6d=None /\
 ScalarBytes.broadcast_reg 0xd2 0x2d=None.
Proof. repeat split;reflexivity. Qed.

From Machine Require execution.MaskedResult.
Module M:=MaskedResult.
Example predicated_encodings :
 M.encode 0 (M.Invert 4 4)=[0xc5;0xf8;0x44;0xe4] /\
 M.encode 0 (M.Exclusive 3 3 4)=[0xc5;0xe4;0x47;0xdc] /\
 M.encode 0 (M.FromGpr 4 9)=[0xc4;0xc1;0x78;0x92;0xe1] /\
 M.encode 0 (M.TestBroadcast 3 20 1710)=[0x62;0xf2;0xdd;0x50;0x27;0x1d;0xa4;6;0;0] /\
 M.encode 0 (M.LoadRow 0 4 7 960)=[0x62;0xf1;0xfd;0x4c;0x6f;0x47;0x0f] /\
 M.encode 0 (M.Subtract 0 3 20 0)=[0x62;0xf1;0xdd;0x43;0xfb;0xc0].
Proof. repeat split;reflexivity. Qed.

Example masked_load_alternating :
 let s:=CPU (fun _=>0) (fun _ _=>99) None (fun a=>if a mod 8=?0 then a/8 else 0) in
 let ks:=fun (_ j:nat)=>Nat.odd j in
 match M.step 0 s ks (M.LoadRow 0 4 7 0) with
 | Some(t,_)=>vectors t 0%nat 0%nat=99 /\ vectors t 1%nat 0%nat=1 /\ vectors t 2%nat 0%nat=99
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

Example predicate_word_width :
 match M.step 0 entry (fun _ _=>false) (M.Invert 4 4) with
 | Some(_,mask)=>mask 4%nat 15%nat=true /\ mask 4%nat 16%nat=false
 | _=>False end.
Proof. split;reflexivity. Qed.

Example decoder_mask_packing_and_epilogue :
 let code:=[0xc1;0xe0;8;0x44;0x09;0xe8;0xc5;0xf8;0x77] in
 let s:=CPU (fun r=>if (r=?0)%nat then 2^40+0x81 else 0x42) (fun _ _=>55) (Some true) (fun _=>0) in
 match MappedFetch.run 3 (ScalarBytes.fetch 0 code) (ScalarBytes.State (ScalarBytes.Running 0) s None) with
 | Some(t,[])=>let v:=ScalarBytes.cpu_state t in regs v 0%nat=0x8142 /\ flag v=Some false /\ ScalarBytes.cf t=Some false /\
   vectors v 1%nat 15%nat=55 /\ vectors v 2%nat 15%nat=0 /\ vectors v 2%nat 16%nat=55
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

From Machine Require execution.PreservedRegister.

Example preserved_register_at_instruction_boundaries :
 let epilogue:=[0x41;0x5d;0xc3] in
 PreservedRegister.checks_at 5 epilogue 0 2=true /\
 PreservedRegister.checks_at 5 epilogue 1 2=false /\
 PreservedRegister.checks_at 5 ([0xeb;1]++epilogue) 0 2=false.
Proof. repeat split;reflexivity. Qed.

Example eligibility_byte_store :
 let code:=[0x44;0x0f;0xb6;0xf8;0xc1;0xe8;8;0x41;0x88;0x45;0x48;0x45;0x21;0xfe;0x41;0x21;0xc6] in
 let s:=CPU (fun r=>if (r=?0)%nat then 2^40+0x81c3 else if (r=?13)%nat then 256 else 2^35+0xb1)
    (fun _ _=>0) None (fun _=>19) in
 match MappedFetch.run 5 (ScalarBytes.fetch 100 code) (ScalarBytes.State (ScalarBytes.Running 0) s None) with
 | Some(t,[w])=>let v:=ScalarBytes.cpu_state t in
   regs v 0%nat=0x81 /\ regs v 15%nat=0xc3 /\ regs v 14%nat=0x81 /\ flag v=Some false /\
   WriteTrace.pc w=107 /\ WriteTrace.address w=328 /\ WriteTrace.size w=1%nat /\ mem v 328=129 /\ mem v 329=19
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

Example counted_table_stores :
 let code:=[0x89;0xd1;0xff;0xc9;0x48;0xc7;0x40;0xf8;0xff;0xff;0xff;0xff] in
 let s:=CPU (fun r=>if (r=?0)%nat then 224 else 2^40+1) (fun _ _=>0) (Some false) (fun _=>7) in
 match MappedFetch.run 3 (ScalarBytes.fetch 1000 code) (ScalarBytes.State (ScalarBytes.Running 0) s (Some true)) with
 | Some(t,[w])=>let v:=ScalarBytes.cpu_state t in
   regs v 1%nat=0 /\ flag v=Some true /\ ScalarBytes.cf t=Some true /\
   WriteTrace.pc w=1004 /\ WriteTrace.address w=216 /\ read_word (mem v) 216=2^64-1 /\ mem v 224=7
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

Example memory_source_add_sub :
 let s:=CPU (fun _=>128) (fun _ _=>0) None (fun x=>if x=?200 then 7 else 0) in
 let test opcode expected:=match ScalarBytes.fetch 0 [0x62;0xd1;0xf5;0x48;opcode;0x4c;0x24;1]
    (ScalarBytes.State (ScalarBytes.Running 0) s (Some true)) with
  | Some(t,[]) =>vectors(ScalarBytes.cpu_state t) 1%nat 1%nat=expected /\
     vectors(ScalarBytes.cpu_state t) 0%nat 1%nat=0 /\ ScalarBytes.cf t=Some true
  | _=>False end in test 0xfb (2^64-7) /\ test 0xd4 7.
Proof. vm_compute;auto. Qed.

Example extended_shuffle_and_extract :
 let s:=CPU (fun r=>if Nat.eqb r 13 then 192 else 0) (fun j r=>100*Z.of_nat r+Z.of_nat j) None (fun _=>255) in
 ScalarBytes.decode [0x62;0x31;0xfd;0x40;0x6d;0xd9]=
 Some(6%nat,ScalarBytes.VectorMove(VectorMoves.Input (IndexedLoad.UnpackWords true 11 16 17))) /\
 match ScalarBytes.fetch 700 [0x62;0x53;0xfd;0x48;0x3b;0x55;4;1] (ScalarBytes.State(ScalarBytes.Running 0) s None) with
 | Some(t,[w])=>WriteTrace.pc w=700 /\ WriteTrace.address w=320 /\ WriteTrace.size w=32%nat /\
    read_word (mem(ScalarBytes.cpu_state t)) 320=1004 /\ read_word (mem(ScalarBytes.cpu_state t)) 344=1007 /\
    mem(ScalarBytes.cpu_state t) 352=255
 | _=>False end.
Proof. vm_compute;auto 7. Qed.

Example cached_add_affine_argument :
 let s:=CPU (fun _=>2^48+3) (fun _ _=>0) (Some true) (fun _=>0) in
 match ScalarBytes.fetch 0 [0xb9;0x01;0x02;0x03;0x80] (ScalarBytes.State (ScalarBytes.Running 0) s (Some false)) with
 | Some(t,[])=>let v:=ScalarBytes.cpu_state t in regs v 1%nat=0x80030201 /\ regs v 2%nat=2^48+3 /\
    ScalarBytes.loc t=ScalarBytes.Running 5 /\ flag v=Some true /\ ScalarBytes.cf t=Some false
 | _=>False end.
Proof. repeat split;reflexivity. Qed.
