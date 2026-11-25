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

From Machine Require execution.MaskedResult.

Example masked_byte_order :
 let bit:=fun j=>orb (orb (Nat.eqb j 0) (Nat.eqb j 7)) (orb (Nat.eqb j 9) (Nat.eqb j 63)) in
 MaskedResult.mask_qword bit 0=0xff000000000000ff /\
 MaskedResult.abs_qword (MaskedResult.mask_qword bit 1)=0x100 /\
 MaskedResult.abs_qword (MaskedResult.mask_qword bit 7)=0x0100000000000000 /\
 MaskedResult.abs_qword 0x81807fff000102a0=0x7f807f0100010260.
Proof. repeat split;reflexivity. Qed.

Example store_low_xmm_qword :
 let s:=CPU (fun r=>if Nat.eqb r 13 then 1000 else 16)
   (fun j r=>0xfedcba9876543200+16*Z.of_nat r+Z.of_nat j) None (fun _=>91) in
 match ScalarBytes.fetch 270 [0xc4;0x41;0x79;0xd6;0x55;0xf8]
   (ScalarBytes.State (ScalarBytes.Running 0) s (Some true)) with
 | Some(t,[w])=>WriteTrace.pc w=270 /\ WriteTrace.address w=992 /\ WriteTrace.size w=8%nat /\
   read_word (mem(ScalarBytes.cpu_state t)) 992=0xfedcba98765432a0 /\
   mem(ScalarBytes.cpu_state t) 991=91 /\ mem(ScalarBytes.cpu_state t) 1000=91 /\
   ScalarBytes.cf t=Some true
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

Example masked_length_load :
 let s:=CPU (fun _=>512) (fun _ _=>17) (Some true)
    (fun x=>if x=?520 then 255 else if x=?522 then 1 else if x=?576 then 127 else if x=?592 then 33 else 0) in
 let ops:=[MaskedResult.WidenBytes 0 4 8;MaskedResult.TestQ 2 0 0;MaskedResult.ZeroRow 0 2 4 64] in
 match MaskedResult.evaluate 0 s (fun _ _=>true) ops with
 | Some(t,k)=>vectors t 0%nat 0%nat=127 /\ vectors t 1%nat 0%nat=0 /\ vectors t 2%nat 0%nat=33 /\
   k 2%nat 7%nat=false /\ k 2%nat 8%nat=false /\ flag t=Some true /\ mem t 576=127
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

Example base_lea_forms :
 ScalarBytes.decode [0x4c;0x8d;0x84;0x24;0xc0;2;0;0]=Some(8%nat,ScalarBytes.LeaG 8 (ScalarBytes.Address 4 None 704)) /\
 ScalarBytes.decode [0x48;0x8d;0x73;0xc0]=Some(4%nat,ScalarBytes.LeaG 6 (ScalarBytes.Address 3 None (-64))) /\
 ScalarBytes.decode [0x48;0x8d;0x73]=None.
Proof. repeat split;reflexivity. Qed.

Example gather_encodings :
 MaskedResult.assemble 0 [MaskedResult.GatherQ 15 3 20 (-32);MaskedResult.GatherQ 27 7 14 0x1234;MaskedResult.XnorWord 6 2 7]=
 Some [0x62;0x72;0xfd;0x43;0x91;0x3c;0x25;0xe0;0xff;0xff;0xff;
       0x62;0x22;0xfd;0x4f;0x91;0x1c;0x35;0x34;0x12;0;0;0xc5;0xec;0x46;0xf7] /\
 MaskedResult.assemble 0 [MaskedResult.GatherQ 20 3 20 0]=None /\
 MaskedResult.assemble 0 [MaskedResult.GatherQ 0 0 20 0]=None /\
 MaskedResult.assemble 0 [MaskedResult.GatherQ 1 3 20 (2^31)]=None.
Proof. repeat split;reflexivity. Qed.

Example gather_merges_inactive_lanes_and_clears_mask :
 let s:=CPU (fun _=>0) (fun j r=>if Nat.eqb r 20 then 32+16*Z.of_nat j else 77) None
    (fun x=>if x=?0 then 17 else if x=?33 then 1 else 0) in
 let k:=fun r j=>if Nat.eqb r 3 then Nat.even j else true in
 match MaskedResult.evaluate 0 s k [MaskedResult.GatherQ 15 3 20 (-32);MaskedResult.XnorWord 6 3 2] with
 | Some(t,b)=>vectors t 0%nat 15%nat=17 /\ vectors t 1%nat 15%nat=77 /\ vectors t 2%nat 15%nat=256 /\
   vectors t 2%nat 20%nat=64 /\ b 3%nat 0%nat=false /\ b 3%nat 15%nat=false /\
   b 6%nat 0%nat=false /\ b 2%nat 8%nat=true
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

From Machine Require execution.PredicateFlags.
Example kortest_word_flags :
 let code:=[0xc5;0xf8;0x98;0xd2] in
 let s:=CPU (fun _=>0) (fun _ _=>0) None (fun x=>nth (Z.to_nat(x-900)) code 0) in
 let p:=LinkedRun.Cursor 900 s None [] in
 let flags b:=option_map (fun q=>(flag(LinkedRun.machine q),LinkedRun.carry q))
    (PredicateFlags.test 2 p (fun _=>b)) in
 flags (fun _=>false)=Some(Some true,Some false) /\
 flags (fun j=>Nat.eqb j 15)=Some(Some false,Some false) /\
 flags (fun j=>(j<?16)%nat)=Some(Some false,Some true) /\
 flags (fun j=>Nat.eqb j 16)=Some(Some true,Some false).
Proof. repeat split;reflexivity. Qed.

Example xmm_filter_forms :
 MaskedResult.assemble 0 [MaskedResult.AndWord 1 1 2;MaskedResult.LoadLowQ 1 6 0;MaskedResult.AndNotXmm 0 0 1]=
 Some [0xc5;0xf4;0x41;0xca;0xc5;0xfa;0x7e;0x0e;0xc5;0xf9;0xdf;0xc1] /\
 let s:=CPU (fun _=>272) (fun j r=>if Nat.eqb r 0 then 0xff00 else 99+Z.of_nat j) None (fun _=>255) in
 match MaskedResult.evaluate 0 s (fun r j=>if Nat.eqb r 1 then Nat.even j else (j<?2)%nat)
    [MaskedResult.AndWord 1 1 2;MaskedResult.LoadLowQ 1 6 0;MaskedResult.AndNotXmm 0 0 1] with
 | Some(t,k)=>vectors t 0%nat 0%nat=0xffffffffffff00ff /\ vectors t 1%nat 1%nat=0 /\
    vectors t 1%nat 0%nat=0 /\ vectors t 2%nat 0%nat=0 /\ k 1%nat 0%nat=true /\ k 1%nat 1%nat=false /\ k 2%nat 1%nat=true
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

Example strict_status_uses_the_whole_qword :
 let s:=CPU (fun r=>if Nat.eqb r 3 then 1024 else 0x12345678ff) (fun _ _=>0) (Some true)
      (fun x=>if x=?1023 then 1 else 0) in
 let code:=[0x48;0x83;0x7b;0xf8;0;0x0f;0x95;0xc0] in
 match MappedFetch.run 2 (ScalarBytes.fetch 100 code) (ScalarBytes.State(ScalarBytes.Running 0) s (Some true)) with
 | Some(t,[])=>regs(ScalarBytes.cpu_state t) 0%nat=0x1234567801 /\
     flag(ScalarBytes.cpu_state t)=Some false /\ ScalarBytes.cf t=Some false
 | _=>False end /\
 ScalarBytes.decode [0x48;0x83;0x7b;0xfe;0xff]=Some(5%nat,ScalarBytes.CompareMemImm(ScalarBytes.Address 3 None (-2)) (-1)) /\
 ScalarBytes.decode [0x0f;0x95;0xc4]=None /\ ScalarBytes.decode [0x48;0x83;0x7b;0x40]=None.
Proof. repeat split;reflexivity. Qed.

Example scorer_memory_operands :
 let code:=[0x48;0x8b;0x84;0x24;0;1;0;0;0x48;0x89;0x47;0xf8;
            0x0f;0xb6;0x57;0xf9;0x48;0x8b;0x47;0xf8] in
 let s:=CPU (fun r=>if Nat.eqb r 4 then 256 else if Nat.eqb r 7 then 72 else 2^64-1)
            (fun _ _=>0) None (fun x=>if x=?513 then 255 else 0) in
 match MappedFetch.run 4 (ScalarBytes.fetch 1000 code) (ScalarBytes.State(ScalarBytes.Running 0) s None) with
 | Some(t,[w])=>ScalarBytes.loc t=ScalarBytes.Running 20 /\ regs(ScalarBytes.cpu_state t) 2%nat=255 /\
   regs(ScalarBytes.cpu_state t) 0%nat=65280 /\ WriteTrace.address w=64 /\ WriteTrace.size w=8%nat
 | _=>False end.
Proof. repeat split;reflexivity. Qed.

Example scorer_registers_and_candidate_pointer_loads :
 let s:=CPU (fun r=>if Nat.eqb r 2 then 0x10258 else if Nat.eqb r 7 then 0x19 else if Nat.eqb r 4 then 80 else 2^64-1)
            (fun _ _=>0) None (fun _=>0) in
 let code:=[0x44;0x0f;0xb6;0xe2;0x48;0x89;0x3c;0x24;0x49;0x8b;0x74;0x24;0xf8;
            0x49;0x8b;0x54;0x24;0xf8;0x49;0x8b;0x4c;0x24;0xf8;0x41;0xb9;1;0;0;0;0x41;0x21;0xc4] in
 match MappedFetch.run 7 (ScalarBytes.fetch 1024 code) (ScalarBytes.State(ScalarBytes.Running 0) s None) with
 | Some(t,[w])=>let g:=regs(ScalarBytes.cpu_state t) in ScalarBytes.loc t=ScalarBytes.Running 32 /\
     g 6%nat=25 /\ g 2%nat=25 /\ g 1%nat=25 /\ g 9%nat=1 /\ g 12%nat=88 /\ WriteTrace.address w=80
 | _=>False end.
Proof. repeat split;reflexivity. Qed.
