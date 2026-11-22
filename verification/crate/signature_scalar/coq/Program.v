From Coq Require Import List ZArith.
From Machine Require Import isa.IndexedLoad execution.IndexedLoads execution.MaskedWords
 execution.LinkedCalls execution.MaskTrace execution.Packed.
From Ed25519Simd Require Import Radix16Output.
Import ListNotations. Local Open Scope nat_scope.

Definition direct r d := Addr r false (Z.of_nat d).
Definition pair d lo hi :=
 [LoadG 0 (direct 6 (8*lo)); LoadG 1 (direct 6 (8*hi));
  LoadY d (direct 0 0); InsertY d d (direct 1 0) true].
Definition inputs := pair 0 0 2 ++ pair 1 1 3 ++ pair 2 4 6 ++ pair 3 5 7 ++
 [UnpackWords false 4 0 1; UnpackWords false 5 2 3;
  UnpackWords true 6 0 1; UnpackWords true 7 2 3;
  ShuffleWords 8 4 5 136; ShuffleWords 9 6 7 136;
  ShuffleWords 10 4 5 221; ShuffleWords 11 6 7 221].

Definition compare_order (t:Z) :=
 [Compare true 1 0 8 (Rip t); Compare false 1 1 9 (Rip (t+8));
  Compare true 2 0 9 (Rip (t+8)); Union 1 1 2; MaskedWords.Xor 4 4 4;
  Compare false 1 1 10 (Reg 4); Compare false 1 1 11 (Rip (t+24));
  Compare true 2 0 11 (Rip (t+24)); Union 1 1 2].
Definition bias_words :=
 [MoveImm true 0x8888888888888888; Splat 4; MoveImm false 1; Splat 5] ++
 map (fun i=>MaskedWords.Add i 0 (8+i) 4) (seq 0 4) ++
 flat_map (fun i=>[Compare true 2 0 i (Reg (8+i)); MaskedWords.Add (S i) 2 (S i) 5]) (seq 0 3) ++
 map (fun i=>Blend i 1 4 i) (seq 0 4).
Definition result_mask := 1.
Definition load_bytes := flat_map IndexedLoad.encode inputs.
Definition image_for pc ops := option_map (fun mid=>load_bytes ++ mid ++ flat_map Packed.encode write_digits ++
 MaskTrace.encoding (KmovEax result_mask) ++ Packed.encode Upper ++ LinkedCalls.encoding 0 LinkedCalls.Return)
 (MaskedWords.assemble (pc+Z.of_nat(length load_bytes)) ops).
Definition image pc t := image_for pc (compare_order t++bias_words).
Definition loaded := IndexedLoads.execute inputs.
Definition lanes t slide s ks := MaskedWords.execute (compare_order t++bias_words) slide (loaded s) ks.
Definition prepared t slide s ks :=
 let v:=lanes t slide s ks in let st:=loaded s in
 CPU (Packed.update (LinkedCalls.regs st) 0 (rax (v 0))) (fun j=>MaskedWords.zmm (v j)) (flag st) (mem st).
Definition mask16 (f:nat->bool) := mask_word 16 (fun j=>Z.b2z (f j)).
Definition body t slide s ks :=
 let rows:=Packed.execute 8 write_digits (prepared t slide s ks) in
 let eax:=mask16 (fun j=>mask (lanes t slide s ks j) result_mask) in
 Packed.execute 8 [Upper] (set rows 0 eax).
Definition run pc n t slide s ks :=
 caller_step slide (pc+n-1) LinkedCalls.Return (body t slide s ks).
