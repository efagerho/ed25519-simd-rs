From Coq Require Import List ZArith Lia.
From Curve25519 Require Import Field Radix51 Edwards Torsion.
From Machine Require Import execution.MaskTrace.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.SmallOrder Require Import Program EntryBytes HelperBytes Audit.
Import ListNotations. Local Open Scope Z_scope.

(* Negative control, compiled only for mutated ELFs. Each listing must bind
   successfully. The actual execution must contradict the public contract. *)
Example mutant_binding :
  bytes code = EntryBytes.symbol_bytes /\ well_formed code = true /\
  bytes helper = HelperBytes.symbol_bytes /\ well_formed helper = true.
Proof. vm_compute; repeat split. Qed.

(* All lanes have Y=2^52-1 and X=iY mod p, so the fourth root sets bit 0. *)
Local Definition y := 2^52-1.
Local Definition rows := Eval vm_compute in
  map (fun j=>((sqrt_m1*y mod prime) / radix^(Z.of_nat j)) mod radix) (seq 0 5) ++ [y;0;0;0;0].
Local Definition point k := nth (k/8)%nat rows 0 mod 2^52.
Local Lemma limbs_bounded : bounded point.
Proof.
  intros i j _ _. apply Z.mod_pos_bound; lia.
Qed.
Local Lemma root : torsion_roots (cx (point_values point O)) (cy (point_values point O)).
Proof. right; right; right; vm_compute; reflexivity. Qed.

Example mutant_violates_contract :
  ~ small_order_contract EntryBytes.address EntryBytes.symbol_bytes HelperBytes.address HelperBytes.symbol_bytes.
Proof.
  intros [_ _ _ Run].
  destruct (Run O point (fun _ _=>0) ltac:(lia) limbs_bounded) as [mask [Exec [_ Bits]]].
  pose proof (proj2 (proj1 (Bits O ltac:(lia))) root) as SetBit.
  assert (Miss : match result (run_at EntryBytes.address HelperBytes.address O)
                        (inputs point) (fun _ _=>0) with
                 | Some m => Z.testbit m 0 | None => false end = false)
    by (vm_compute; reflexivity).
  rewrite Exec in Miss. change (Z.testbit mask 0=true) in SetBit. congruence.
Qed.
