From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.VectorProcedure
 execution.ScalarBytes execution.MappedFetch execution.WordBounds memory.MemoryGeometry.
From Ed25519Simd.Decode Require Kernels Program DecoderBytes HelperBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode.
From Ed25519Simd.VerifyBatch Require DecoderKernel.
Import ListNotations. Local Open Scope Z_scope.
Module K:=DecoderKernel.
Definition section b := match b with K.Seed | K.Convolve | K.Fold=>HelperBytes.address | _=>DecoderBytes.address end.
Definition native bias b := segment (bias+section b) (K.image b) (length(K.body b)).
Definition area e := Area (sp e-16384) (sp e).
Definition columns bias := then_run (native bias K.Seed)
 (then_run (wrapped (bias+HelperBytes.address) HelperBytes.symbol_bytes
         (bias+HelperBytes.address) HelperBytes.symbol_bytes (native bias K.Convolve)) (native bias K.Fold)).
Definition product bias := then_run
 (wrapped (bias+DecoderBytes.address) DecoderBytes.symbol_bytes
     (bias+HelperBytes.address) HelperBytes.symbol_bytes (columns bias)) (native bias K.Carry).

Section Linked.
Variables (pol:policy) (bias:Z) (e:cpu).
Hypothesis P:placement e.
Hypothesis Loaded:loaded pol bias (mem e) (writable e).
Local Notation spec := (contract e (writable e) (area e)).
Local Notation h := (bias+HelperBytes.address).
Local Notation d := (bias+DecoderBytes.address).
Lemma stack : VectorProcedure.stack_ok (area e) (writable e).
Proof.
 destruct(Return.stack_ok _ P) as [[L H] _];unfold VectorProcedure.stack_ok,area;cbn [bottom ceiling].
 split;[exact L|split;[lia|intros x X;left;unfold span,region,area in *;cbn [bottom ceiling] in *;lia]].
Qed.
Lemma placed b : available e (writable e) (bias+section b) (K.image b).
Proof.
 assert (S:forall a t,In (a,t) (children pol) -> available e (writable e) (bias+a) t).
 { intros a t I;split;[exact (proj2(symbols _ _ _ _ Loaded _ _ I))|].
   intros x X;apply (immutable _ _ _ _ Loaded);left;exists a,t;auto. }
 destruct b;apply S;apply helper_in || apply decode_in.
Qed.
Lemma calc b : spec (bias+section b+K.start b) (bias+section b+K.stop b) 0 (K.body b) (native bias b).
Proof. apply block;[apply placed|apply K.bytes|destruct b;vm_compute;reflexivity]. Qed.
Lemma address_fits b off : 0<=off<Z.of_nat(length (K.image b)) -> word64(bias+section b+off).
Proof.
 assert (S:In(section b,K.image b)(children pol)) by (destruct b;apply helper_in || apply decode_in).
 destruct(proj1(symbols _ _ _ _ Loaded _ _ S));unfold word64;lia.
Qed.
Lemma check_columns : spec (h+0xb90) (h+0xca3) 8
 (K.body K.Seed++(K.body K.Convolve++K.body K.Fold)) (columns bias).
Proof.
 eapply (compose _ _ _ _ (h+0xbfc) _ 0 8);[exact (calc K.Seed)|].
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

Lemma lane_square r y :
 split_field y -> (forall i,(i<5)%nat -> r i=y i /\ r (5+i)%nat=y i) ->
 (forall i,(i<4)%nat -> r (28+i)%nat=DecoderFrame.constant i) ->
 let out:=Instructions.run no_read (Kernels.product kernel) r in
 field_bound (Kernels.out_bound Kernels.Multiply) out /\
 represents (limbs out) (limbs y*limbs y) /\ 2<=out 0%nat.
Proof.
 intros Y Inputs Constants out;destruct multiplication as [Checked Frame].
 pose proof (Power.apply_ok _ Kernels.Multiply _ _ Checked Y Y) as [Bounds [Value Positive]].
 assert (Live:forall i,Kernels.live Kernels.Multiply i=true -> r i=Power.feed y y i).
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
 assert (E:forall i,(i<5)%nat -> out i=Power.apply_kernel kernel Kernels.Multiply y y i) by exact Same.
 split;[intros i I;rewrite E by exact I;apply Bounds,I|split].
 - erewrite limbs_ext;[exact Value|exact E].
 - rewrite E by lia;apply Positive;reflexivity.
Qed.
