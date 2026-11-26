From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure
 execution.ScalarBytes execution.MappedFetch execution.WordBounds memory.MemoryGeometry.
From Ed25519Simd.Decode Require Kernels Program DecoderBytes HelperBytes.
From Ed25519Simd.Decode Require DecoderKernel FieldLiterals.
Import ListNotations. Local Open Scope Z_scope.
Module K:=DecoderKernel.
Definition section b := match b with K.Seed | K.Convolve | K.Fold=>HelperBytes.address | _=>DecoderBytes.address end.
Definition native bias b := segment (bias+section b) (K.image b) (length(K.body b)).
Definition columns bias := then_run (native bias K.Seed)
 (then_run (wrapped (bias+HelperBytes.address) HelperBytes.symbol_bytes
         (bias+HelperBytes.address) HelperBytes.symbol_bytes (native bias K.Convolve)) (native bias K.Fold)).
Definition product bias := then_run
 (wrapped (bias+DecoderBytes.address) DecoderBytes.symbol_bytes
     (bias+HelperBytes.address) HelperBytes.symbol_bytes (columns bias)) (native bias K.Carry).

Section Linked.
Variables (bias:Z) (root:cpu) (allowed:Z->Prop) (area:stack_area).
Hypothesis stack:stack_ok area allowed.
Hypothesis placed:forall b,available root allowed (bias+section b) (K.image b).
Hypothesis address_fits:forall b off,0<=off<Z.of_nat(length(K.image b)) -> word64(bias+section b+off).
Local Notation spec := (contract root allowed area).
Local Notation h := (bias+HelperBytes.address).
Local Notation d := (bias+DecoderBytes.address).
Lemma calc b : spec (bias+section b+K.start b) (bias+section b+K.stop b) 0 (K.body b) (native bias b).
Proof. apply block;[apply placed|apply K.bytes|destruct b;vm_compute;reflexivity]. Qed.
Lemma after_seed : spec (h+0xbfc) (h+0xca3) 8 (K.body K.Convolve++K.body K.Fold)
 (then_run (wrapped h HelperBytes.symbol_bytes h HelperBytes.symbol_bytes (native bias K.Convolve)) (native bias K.Fold)).
Proof.
 eapply (compose _ _ _ _ (h+0xc01) _ 8 0);[|exact (calc K.Fold)].
 apply (invoke _ _ _ _ _ 0xbfc (0xcb0-0xc01) _ _ 0xddc 0).
 - apply stack.
 - lia.
 - exact (placed K.Convolve).
 - exact (placed K.Convolve).
 - lia.
 - vm_compute;reflexivity.
 - lia.
 - vm_compute;reflexivity.
 - replace (h+(0xbfc+5)+(0xcb0-0xc01)) with (h+0xcb0) by ring;apply (address_fits K.Convolve);vm_compute;split;discriminate || reflexivity.
 - exact (address_fits K.Convolve 0xc01 ltac:(vm_compute;split;discriminate || reflexivity)).
 - replace (h+(0xbfc+5)+(0xcb0-0xc01)) with (h+0xcb0) by ring;exact (calc K.Convolve).
Qed.
Lemma check_columns : spec (h+0xb90) (h+0xca3) 8
 (K.body K.Seed++(K.body K.Convolve++K.body K.Fold)) (columns bias).
Proof.
 exact (compose _ _ _ _ (h+0xbfc) _ 0 8 _ _ _ _ (calc K.Seed) after_seed).

Qed.

Lemma check_product : spec (d+0xa79) (d+0xadd) 16 (Kernels.product Ed25519Simd.Decode.Program.code) (product bias).
Proof.
 set (col:=K.body K.Seed++(K.body K.Convolve++K.body K.Fold)).
 assert (C:spec (d+0xa79) (d+0xa7e) 16 col
    (wrapped d DecoderBytes.symbol_bytes h HelperBytes.symbol_bytes (columns bias))).
 { apply (invoke _ _ _ _ _ 0xa79 ((HelperBytes.address+0xb90)-(DecoderBytes.address+0xa7e)) _ _ 0xca3 8).
   - apply stack.
   - lia.
   - exact (placed K.Carry).
   - exact (placed K.Fold).
   - lia.
   - vm_compute;reflexivity.
   - lia.
   - vm_compute;reflexivity.
   - replace (d+(0xa79+5)+(HelperBytes.address+0xb90-(DecoderBytes.address+0xa7e))) with (h+0xb90) by ring.
     exact (address_fits K.Seed 0xb90 ltac:(vm_compute;split;discriminate || reflexivity)).
   - exact (address_fits K.Carry 0xa7e ltac:(vm_compute;split;discriminate || reflexivity)).
   - replace (d+(0xa79+5)+(HelperBytes.address+0xb90-(DecoderBytes.address+0xa7e))) with (h+0xb90) by ring;apply check_columns. }
 assert (R:=compose _ _ _ _ _ _ _ _ _ _ _ _ C (calc K.Carry)).
 unfold col in R;rewrite <-!app_assoc in R;exact R.
Qed.
End Linked.

From Ed25519Simd.Decode Require Power.
From Curve25519 Require Import Radix51 Field.
From Machine Require Import isa.Instructions.
Definition kernel:=Ed25519Simd.Decode.Program.code.
Lemma multiplication : Kernels.verified kernel Kernels.Multiply=true /\ Kernels.kernel_frame kernel Kernels.Multiply.
Proof. split;[vm_compute;reflexivity|apply Kernels.frame_ok;vm_compute;reflexivity]. Qed.

Lemma lane_product r x y :
 (forall i,(i<5)%nat -> r i=x i /\ r (5+i)%nat=y i) ->
 (forall i,(i<4)%nat -> r (28+i)%nat=FieldLiterals.constant i) ->
 forall i,(i<5)%nat -> Instructions.run no_read (Kernels.product kernel) r i=
   Power.apply_kernel kernel Kernels.Multiply x y i.
Proof.
 intros Inputs Constants;destruct multiplication as [_ Frame].
 assert (Live:forall i,Kernels.live Kernels.Multiply i=true -> r i=Power.feed x y i).
 { intros i On;destruct (Nat.lt_ge_cases i 10) as [L|H].
   - pose proof (Inputs 0%nat ltac:(lia)) as [A F0];pose proof (Inputs 1%nat ltac:(lia)) as [B F1];
     pose proof (Inputs 2%nat ltac:(lia)) as [C F2];pose proof (Inputs 3%nat ltac:(lia)) as [D F3];
     pose proof (Inputs 4%nat ltac:(lia)) as [E F4].
     do 10 (destruct i as [|i];[assumption|]);lia.
   - unfold Kernels.live in On;rewrite (proj2 (Nat.ltb_ge _ _) H) in On;cbn in On.
     do 28 (destruct i as [|i];[discriminate|]).
     do 4 (destruct i as [|i];[first [exact (Constants 0%nat ltac:(lia))|exact (Constants 1%nat ltac:(lia))|
        exact (Constants 2%nat ltac:(lia))|exact (Constants 3%nat ltac:(lia))]|]);discriminate. }
 destruct (Frame no_read no_read _ _ Live) as [Same _].
 exact Same.
Qed.

Lemma lane_square r y :
 split_field y -> (forall i,(i<5)%nat -> r i=y i /\ r (5+i)%nat=y i) ->
 (forall i,(i<4)%nat -> r (28+i)%nat=FieldLiterals.constant i) ->
 let out:=Instructions.run no_read (Kernels.product kernel) r in
 field_bound (Kernels.out_bound Kernels.Multiply) out /\
 represents (limbs out) (limbs y*limbs y) /\ 2<=out 0%nat.
Proof.
 intros Y Inputs Constants out.
 pose proof (Power.apply_ok _ Kernels.Multiply _ _ (proj1 multiplication) Y Y) as [Bounds [Value Positive]].
 assert (E:forall i,(i<5)%nat -> out i=Power.apply_kernel kernel Kernels.Multiply y y i)
   by exact (lane_product _ _ _ Inputs Constants).
 split;[intros i I;rewrite E by exact I;apply Bounds,I|split].
 - erewrite limbs_ext;[exact Value|exact E].
 - rewrite E by lia;apply Positive;reflexivity.
Qed.
