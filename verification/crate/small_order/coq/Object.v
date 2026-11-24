From Coq Require Import ZArith Lia.
From Curve25519 Require Import Edwards Radix51 Torsion SmallOrderFilter group.Cofactor.
From Machine Require Import execution.MaskTrace execution.CircuitFacts.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.field51 Require Import RootMasks.
From Ed25519Simd.SmallOrder Require Import Program EntryBytes HelperBytes Audit Schedule Filter Exact.
Local Open Scope Z_scope.

Local Lemma candidates_cover p j : (j<8)%nat -> bounded p ->
 torsion_roots (cx (point_values p j)) (cy (point_values p j)) ->
 small_order_candidate (fun i=>cell p i j) (fun i=>cell p (5+i)%nat j).
Proof.
 intros J B. apply small_order_filter_sound; intros i I; unfold split;
  [specialize (B i j ltac:(lia) J) | specialize (B (5+i)%nat j ltac:(lia) J)]; lia.
Qed.

Local Lemma group_meaning mask j q :
 (Z.testbit mask (Z.of_nat j)=true <-> torsion_roots (cx q) (cy q)) ->
 lane_result mask j q.
Proof. intro Bits. split; [exact Bits|]. intros P Q. rewrite Bits. now apply projective_small_order. Qed.

Local Lemma exits gs a full b input initial :
 result (Branch gs a 0 (Exit gs (Lit 0)) (Exit full b)) input initial =
 Some (if mask_value gs a input initial =? 0 then 0 else mask_value full b input initial).
Proof. cbn [result]. destruct (mask_value gs a input initial =? 0); reflexivity. Qed.

Local Opaque run_at result short long.
Theorem assembled_small_order_correct :
 small_order_contract EntryBytes.address EntryBytes.symbol_bytes HelperBytes.address HelperBytes.symbol_bytes.
Proof.
 constructor.
 - vm_compute; split; reflexivity.
 - vm_compute; split; reflexivity.
 - vm_compute; intuition discriminate.
 - intros pad P input initial;apply all_branch_writes;destruct pad as [|[|[|[|pad]]]];try lia;vm_compute;reflexivity.
 - intros pad p initial Pad B. rewrite (paths_checked pad Pad), exits.
   eexists; split; [reflexivity|].
   destruct (Z.eqb_spec (mask_value short (Wire 17) (inputs p) initial) 0) as [NoneSet|_].
   + split; [lia|]. intros j J. apply group_meaning. rewrite Z.testbit_0_l.
     pose proof (filter_lane p initial) as C.
     destruct (mask_word_bits 8 _ (fun i _=>proj1(C i))) as [_ Bits].
     unfold mask_value in NoneSet. rewrite NoneSet in Bits.
     specialize (Bits j J). rewrite Z.testbit_0_l in Bits.
     pose proof (proj2 (C j)) as Lane.
     split; [discriminate|]. intro Root. apply (proj2 Bits), (proj2 Lane).
     exact (candidates_cover p j J B Root).
   + pose proof (exact_lane p initial) as F.
     destruct (mask_word_bits 8 _ (fun j J=>proj1(F j J B))) as [Range Bits].
     split; [exact Range|]. intros j J. apply group_meaning.
     unfold mask_value. rewrite Bits by exact J. exact (proj2(F j J B)).
Qed.
