From Coq Require Import ZArith Lia List.
From Machine Require Import execution.LinkedCalls memory.MemoryGeometry execution.WordBounds.
From Ed25519Simd.Scalar Require ObjectBytes.
From Ed25519Simd.Radix16 Require Import LinkedBytes Audit Object.
Import ListNotations. Local Open Scope Z_scope.

Definition witness input_off output_off pad := CPU
 (fun r=>match r with 4%nat=>0x10008+16*pad | 7%nat=>0x20000+output_off | 6%nat=>0x30000+input_off | _=>2^64-1 end)
 (fun _ _=>2^64-1) None (fun _=>255).
Local Definition slide := 2^32-wrapper_pc.
Example entries_exist input_off output_off pad :
 0<=input_off<64 -> 0<=output_off<64 -> 0<=pad<4 ->
 let s:=witness input_off output_off pad in well_formed s /\
 placement (regs s 4%nat) (regs s 7%nat) (regs s 6%nat)
  (slide+wrapper_pc) (size symbol_bytes) (slide+reducer_pc) (size Ed25519Simd.Scalar.ObjectBytes.symbol_bytes).
Proof.
 intros I O P s; split.
 - split; [intro r;unfold s,witness;cbn [regs];unfold word64;
    do 8 (destruct r as [|r];[lia|]);lia|]. split; [intros;unfold word64;change (0<=2^64-1<2^64);lia|intro x;change (0<=255<256);lia].
 - constructor; try (unfold fits64,FlatMemory.disjoint,s,witness;cbn [regs];lia).
   + change ((0x10008+16*pad) mod 16=8);rewrite Z.mul_comm,Z.mod_add by lia;reflexivity.
   + intros a len [H|[H|[]]];inversion H;subst;unfold fits64,FlatMemory.disjoint;
     cbn [s witness regs]; unfold slide;
     let t:=eval vm_compute in (2^32-wrapper_pc+reducer_pc) in change (2^32-wrapper_pc+reducer_pc) with t;
     repeat match goal with |- context [size ?b] => let n:=eval vm_compute in (size b) in change (size b) with n end;
     change (2^32-wrapper_pc+wrapper_pc) with 4294967296; intuition lia.
Qed.
