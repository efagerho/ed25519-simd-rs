From Coq Require Import List ZArith.
From Machine Require Import execution.MaskedWords execution.LinkedCalls execution.Packed memory.ByteMemory.
From Curve25519 Require Import Scalar SignedRadix16.
From Ed25519Simd Require Import Radix16Output.
From Ed25519Simd.SignatureScalar Require Import Program Audit Arithmetic Execution MutantCode MutantOrder.
Import ListNotations. Local Open Scope Z_scope.

Local Notation ro := MutantOrder.address.
Local Notation pc := MutantCode.address.
(* A damaged carry uses K3 (initially clear) instead of K2. A damaged
   blend takes rejected word zero from itself instead of the bias. *)
Definition alter i := match mutation,i with
 | 1%nat, MaskedWords.Add 1 2 1 5 => MaskedWords.Add 1 3 1 5
 | 2%nat, Blend 0 1 4 0 => Blend 0 1 0 0
 | _,_=>i end.
Definition damaged := map alter (compare_order ro++bias_words).
Example matches_mutated_elf : image_for pc damaged=Some MutantCode.symbol_bytes.
Proof. vm_compute;reflexivity. Qed.

Definition input := if Nat.eqb mutation 1 then 0x7777777777777778 else L.
Definition state := fold_left (MaskedWords.step true (fun a=>literal_word MutantOrder.symbol_bytes (a-ro))) damaged
 (Lane (fun r=>chunk input (r-8)%nat) (fun _=>false) 0).
Definition rows := Packed.execute 8 write_digits
 (CPU (fun _=>0) (fun _=>MaskedWords.zmm state) None (fun _=>0)).
Example wrong_observation : match mutation with
 | O => input=L /\ mask state result_mask=true
 | S O => signed_byte (mem rows 16)<>digit input 16
 | _ => input=L /\ mem rows 0<>0
 end.
Proof. vm_compute;intuition discriminate. Qed.

Theorem mutated_public_contract_fails :
 ~signature_scalar_contract pc MutantCode.symbol_bytes ro MutantOrder.symbol_bytes.
Proof.
 intro C.
 lazymatch eval compute in mutation with
 | O => destruct (linked_order _ _ _ _ C) as [_ H];vm_compute in H;discriminate
 | _ => destruct (linked_code _ _ _ _ C) as [H _];
   apply (f_equal (option_map (fun xs=>nth changed_offset xs 0))) in H;
   vm_compute in H;discriminate
 end.
Qed.
