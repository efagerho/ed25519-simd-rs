From Coq Require Import List ZArith Lia Ring.
Import ListNotations. Open Scope Z_scope.

Definition radix := 2^51.
Definition split := 2^52.
Definition limbs (get : nat -> Z) :=
  get 0%nat + radix * (get 1%nat + radix * (get 2%nat +
    radix * (get 3%nat + radix * get 4%nat))).
(* Public input/output bounds; independent of the assembly listing and its proof. *)
(* radix = 2^51; split = 2^52. Bounds here are inclusive. *)
Definition loose_bound i := if Nat.eqb (i mod 5) 0 then 2^60-1 else split-1.
Definition square_bound i := if Nat.odd (i mod 5) then split-1 else radix-1.
Definition output_bound i := if Nat.eqb (i mod 5) 1 then split-1 else radix-1.
Definition ready_bound := radix+2^20.
Definition field_bound (b : nat -> Z) (x : nat -> Z) :=
 forall i, (i<5)%nat -> 0 <= x i <= b i.
Definition loose x :=
 field_bound loose_bound x /\ x 1%nat + x 0%nat / radix < split.
Definition ready x := field_bound (fun _ => ready_bound) x.
Definition squared x := field_bound square_bound x.
Definition reduced x := field_bound output_bound x.
Definition split_field x := field_bound (fun _ => split-1) x.

(* A radix-51 column collects at most five low IFMA halves and twice
   five high halves. Folding one more column by 19 scales that bound by 20. *)
Definition folded_column_bound := 300 * split - 1.
Definition folded_columns := field_bound (fun _ => folded_column_bound).

Lemma ready_split x : ready x -> split_field x.
Proof. intros B i I;specialize(B i I);unfold ready_bound,radix,split in *;lia. Qed.
Lemma ready_loose x : ready x -> loose x.
Proof.
 intro B;split.
 - intros i I;specialize(B i I);unfold loose_bound;destruct(Nat.eqb _ _);unfold ready_bound,radix,split in *;lia.
 - pose proof(B 0%nat ltac:(lia));pose proof(B 1%nat ltac:(lia)).
   assert (x 0%nat/radix<2) by (apply Z.div_lt_upper_bound;unfold ready_bound,radix in *;lia).
   unfold ready_bound,radix,split in *;lia.
Qed.
Lemma reduced_loose x : reduced x -> loose x.
Proof.
 intro B;split.
 - intros i I;specialize(B i I);unfold loose_bound,output_bound in *;
   destruct(Nat.eqb (i mod 5) 0);destruct(Nat.eqb (i mod 5) 1);unfold radix,split in *;lia.
 - pose proof(B 0%nat ltac:(lia)) as A;pose proof(B 1%nat ltac:(lia)) as C.
   change (0<=x 0%nat<=radix-1) in A;change(0<=x 1%nat<=split-1)in C.
   rewrite Z.div_small by lia;lia.
Qed.
Lemma squared_split x : squared x -> split_field x.
Proof. intros B i I;specialize(B i I);unfold square_bound in B;
 destruct(Nat.odd(i mod 5));unfold radix,split in *;lia. Qed.
Lemma field_bound_ext b x y : (forall i,(i<5)%nat -> x i=y i) -> field_bound b x -> field_bound b y.
Proof. intros E B i I;rewrite <-E by exact I;apply B;exact I. Qed.
Lemma loose_ext x y : (forall i,(i<5)%nat -> x i=y i) -> loose x -> loose y.
Proof. intros E [B L];split;[eapply field_bound_ext;eauto|rewrite <-!E by lia;exact L]. Qed.
Lemma limbs_ext x y : (forall i,(i<5)%nat -> x i=y i) -> limbs x=limbs y.
Proof. intro E;unfold limbs;repeat rewrite E by lia;reflexivity. Qed.
