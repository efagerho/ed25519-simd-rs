From Coq Require Import List Bool ZArith Strings.String.
From Machine Require Import Blocks IntelSyntax tests.model.Oracle.
Import ListNotations.
Open Scope Z_scope.

Local Notation "'.Lmiddle'" := (0xa2%Z) (in custom intel_label at level 0).
Local Notation "'.Lleaf'" := (0xa8%Z) (in custom intel_label at level 0).
Definition aligned_probe := assemble [
 ScalarBlock 0 [] ends[ push rbp ];
 ScalarBlock 1 ops[
   mov rbp, rsp; and rsp, -64; sub rsp, 1280; mov rsi, rsp; mov r9, rsp; mov rcx, rdx;
   mov rax, 0; vpbroadcastq zmm24, rax;
   mov rax, 1; vpbroadcastq zmm25, rax;
   mov rax, 1367801; vpbroadcastq zmm26, rax;
   mov rax, 2147483647; vpbroadcastq zmm27, rax;
   movabs rax, 0xfedcba9876543210; vpbroadcastq zmm20, rax;
   vmovdqu64 zmmword ptr [rsi + 640], zmm20;
   vmovdqu64 zmmword ptr [rsi], zmm20;
   vmovdqu64 zmmword ptr [r9 + 640], zmm20;
   mov rax, rcx; vpbroadcastq zmm22, rax;
   vmovdqu64 zmmword ptr [r9], zmm22;
   lea r8, [rsi]; vmovdqu64 zmm23, zmmword ptr [r8];
   lea r8, [rsi + 640]; vmovdqu64 zmm21, zmmword ptr [r8]
 ] ends[ call .Lmiddle ];
 ScalarBlock 0x9a ops[ mov rsp, rbp ] ends[ pop rbp ];
 ScalarBlock 0x9e ops[ vzeroupper ] ends[ ret ];
 ScalarBlock 0xa2 [] ends[ call .Lleaf ];
 ScalarBlock 0xa7 [] ends[ ret ];
 ScalarBlock 0xa8 ops[ vmovdqu64 zmmword ptr [rdi], zmm21 ] ends[ ret ]].
Example aligned_valid : valid_program aligned_probe=true.
Proof. vm_compute; reflexivity. Qed.

Definition aligned_layout : layout := fun r cell =>
 if Nat.eqb r 0 then
   if (0 <=? cell) && (cell <? 20) then WriteVector
   else if cell =? -1 then ReturnWords 192
   else if cell =? 20 then ReturnWords 255 else Unmapped
 else if Nat.eqb r 1 && (cell =? 0) then WriteVector else Unmapped.
Definition padding seed := 16*(seed mod 4).
Definition entry seed := Control (At 0)
 (fun r => match r with
 | 2%nat => Int seed
 | 4%nat => Ptr (0%nat,1288+padding seed) | 5%nat => Int seed
 | 7%nat => Ptr (1%nat,0) | _ => Unknown end)
 None (fun a => if ptr_eq a (0%nat,1288+padding seed) then Some Caller else None).
Definition initial_data seed := Data (initial_zmm seed)
 (fun a j => initial_word seed
   ((if Nat.eqb (fst a) 0 then 264 else 448) + snd a/8 + Z.of_nat j)).
Definition aligned_result seed :=
 match path 8 aligned_probe aligned_layout (entry seed) with
 | Some (c,es) =>
   match rip c, gpr c 5%nat, gpr c 4%nat, gpr c 6%nat, gpr c 8%nat,
     return_memory c (0%nat,1280+padding seed),
     return_memory c (0%nat,-8), return_memory c (0%nat,-16) with
   | Caller, Int bp, Ptr (O,sp), Ptr (O,si), Ptr (O,r8), Saved, Some (At a), Some (At b) =>
     match Saved with
     | Some (SavedWord saved) =>
       let d:=effects aligned_probe es (initial_data seed) in
       [seed;bp;sp;si;r8;saved;a;b] ++
       flat_map (fun r => map (fun j=>zmm d j r) (seq 0 8)) (seq 0 32) ++
       flat_map (fun i=>map (memory d (0%nat,64*Z.of_nat i)) (seq 0 8)) (seq 0 20) ++
       map (memory d (1%nat,0)) (seq 0 8)
     | _ => [] end
   | _,_,_,_,_,_,_,_ => [] end
 | None => [] end.
Definition seeds := [0;1;2;3;2^52-1;2^52;2^63;2^64-1].
Definition aligned_report inputs := String.concat "|"%string
 (numbers (image aligned_probe) :: map (fun seed=>numbers (aligned_result seed)) inputs).

Example immediate32_domain :
 valid_op aligned_probe(MovRaxImm32 0)=true /\
 valid_op aligned_probe(MovRaxImm32 2147483647)=true /\
 valid_op aligned_probe(MovRaxImm32 (-1))=false /\
 valid_op aligned_probe(MovRaxImm32 2147483648)=false.
Proof. vm_compute;repeat split;reflexivity. Qed.
