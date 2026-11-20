From Curve25519 Require Import SignedRadix16.
From Coq Require Import List ZArith Lia.
From Machine Require Import execution.Packed execution.LinkedCalls memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.Scalar Require ObjectBytes.
From Ed25519Simd.Radix16 Require Import LinkedBytes Program Audit MutantBytes.
Import ListNotations. Local Open Scope Z_scope.

Fixpoint corrupt (code:list op) : list op := match code with
| []=>[]
| ShiftQ false 6 0 52 :: rest => if Nat.eqb mutation 0 then ShiftQ false 6 0 53 :: rest
                                else ShiftQ false 6 0 52 :: corrupt rest
| Shuffle 2 0 1 0x88 :: rest => if Nat.eqb mutation 1 then Shuffle 2 0 1 0x89 :: rest
                                else Shuffle 2 0 1 0x88 :: corrupt rest
| h::rest=>h::corrupt rest end.
Definition damaged := corrupt tail.
Definition dest := if Nat.eqb mutation 2 then reducer_pc+1 else reducer_pc.
Example mutated_listing_matches :
 option_map (fun p=>p++flat_map encode damaged++encoding 0 Return)
   (assemble wrapper_pc [Save 7;Invoke dest;Restore 7]) = Some MutantBytes.symbol_bytes.
Proof. vm_compute;reflexivity. Qed.

(* Canonical reducer outputs. Lane 0 generates a carry across bit 64,
   and lane 2 has a different first digit. *)
Definition limbs (i:Z) := if i=?0 then 2^52-1 else if i=?8 then 0x777 else if i=?2 then 2 else 0.
Definition sample := CPU (fun _=>0) (fun _ _=>0) None
 (fun addr=>word_byte (limbs (addr/8)) (addr mod 8)).
Definition wrong_digit k := signed_byte (mem (execute 8 damaged sample) (Z.of_nat k))
                            <> digit (2^52-1+2^52*0x777) k.
Example observable_failure :
 match mutation with O=>wrong_digit 16 | S O=>wrong_digit 0 | _=>dest<>reducer_pc end.
Proof. vm_compute;discriminate. Qed.

Theorem mutated_public_contract_fails :
 ~ digest_contract wrapper_pc MutantBytes.symbol_bytes reducer_pc Ed25519Simd.Scalar.ObjectBytes.symbol_bytes.
Proof. intro C;destruct (wrapper_binding _ _ _ _ C) as [Match _];vm_compute in Match;discriminate. Qed.
