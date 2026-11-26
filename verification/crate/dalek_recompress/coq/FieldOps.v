From Coq Require Import ZArith List Bool Lia Field.
From Machine Require Import isa.Instructions.
From ProofArithmetic Require Import Interval.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField Decompression.
From Ed25519Simd Require Import FieldKernel FieldSymbolic.
From Ed25519Simd.Decode Require Import Kernels Power.
From Curve25519 Require Import Radix51Digits.
From Ed25519Simd.Decode Require Import Decode Scale Unpack.
Import ListNotations. Local Open Scope Z_scope.

(* The five memory-source subtractions consume Y[i] at offset 320+64*i.
   Forwarding each load to its destination's old value lets the ordinary
   register instruction interpreter check the fused convolution. *)
Definition seed_operands (i:nat) := ((10+i)%nat, if Nat.eqb i 0 then 30%nat else 31%nat).
Definition seeds : list instruction := map (fun i=>let '(dst,bias):=seed_operands i in
 (dst, Sub bias dst)) (seq 0 5).
Definition fused k := seeds ++ skipn 5 (seed_columns k) ++ convolve k ++ fold_columns k ++ Kernels.carry k.
Definition fused_live i := Nat.ltb i 15 || live Multiply i.
Definition inputs a z y i := if Nat.ltb i 10 then feed a z i
 else if Nat.ltb i 15 then y (i-10)%nat else feed a z i.
Definition symbolic i := match constant i with Some n=>I (C n) n n
 | None=>I (V i) 0 (if Nat.ltb i 15 then split-1 else 2^64-1) end.
Definition difference := minus (Times (packE V 0) (packE V 5)) (packE V 10).
Definition checked k := Nat.eqb (length(loads_of(fused k))) 0 &&
 check_kernel (fused k) symbolic [] no_load [0%nat] (fun _=>radix+2^16) (fun _=>difference) &&
 (2 <=? lower(arun [] no_load (fused k) symbolic 0%nat)).
Definition subtract_product k a z y := run (fun _ _=>0) (fused k) (inputs a z y).
Lemma fused_ok k a z y : checked k=true -> split_field a -> split_field z -> split_field y ->
 let out:=subtract_product k a z y in
 bounded out /\ 2<=out 0%nat /\ value out=(value a*value z-value y)%fp.
Proof.
 intros H A Zr Y out. unfold checked in H. apply andb_true_iff in H as [H L].
 apply andb_true_iff in H as [N K]. apply Nat.eqb_eq,length_zero_iff_nil in N.
 set (r:=inputs a z y). assert (Init:forall i,models r (symbolic i) (r i)).
 { intros i. destruct (lt_dec i 32); [do 32 (destruct i as [|i]; [split;[reflexivity|first [apply A;lia|apply Zr;lia|apply Y;lia|cbn;lia]]|]);lia|].
   assert (Cst:constant i=None) by (do 32 (destruct i;[lia|]);reflexivity).
   unfold symbolic;rewrite Cst;split;[reflexivity|]. unfold r,inputs,feed;rewrite Cst.
   assert (F:forall j,(j<=15)%nat -> Nat.ltb i j=false) by (intros;apply Nat.ltb_ge;lia).
   cbn [lower upper];rewrite !F by lia;cbn;lia. }
 assert (Mem:forall b d,In (b,d) (loads_of(fused k))->models r (no_load b d) 0) by (rewrite N;contradiction).
 destruct(kernel_correct _ _ _ _ _ _ _ K r (fun _ _=>0) r eq_refl (Forall_nil _) Mem Init
   0%nat (or_introl eq_refl)) as [B V].
 split;[intros i I;specialize(B i I);change (0<=out i<=radix+2^16) in B;lia|].
 split.
 - apply Z.leb_le in L. apply andb_true_iff in K as [Legal _].
   destruct(run_ok r [] _ (fun _ _=>0) _ _ r (Forall_nil _) Mem eq_refl Init Legal 0%nat) as [_ R].
   change (2<=run (fun _ _=>0) (fused k) r 0%nat);lia.
 - apply congruent_value in V. unfold value. rewrite <-residue_mul,<-residue_sub.
   change (residue (pack out)=residue (pack a*pack z+ -1*pack y)) in V.
   replace (pack a*pack z-pack y) with (pack a*pack z+ -1*pack y) by ring;exact V.
Qed.

Definition inverse_chain := [
 Save Root;Product Root;Save A;Squares 2;Product Root;Save B;Product A;Save Root;
 Squares 1;Product B;Save A;Squares 5;Product A;Save A;Squares 10;Product A;
 Save B;Squares 20;Product B;Squares 10;Product A;Save A;Squares 50;Product A;
 Save B;Squares 100;Product B;Squares 50;Product A;Squares 5;Product Root].
Definition inverse k h := current(evaluate (apply_kernel k ChainMultiply)
 (fun a=>apply_kernel k Square a a) h (fun _=>0) inverse_chain).
Lemma inverse_ok k h : verified k ChainMultiply=true -> verified k Square=true ->
 split_field h -> value h<>0%fp -> split_field(inverse k h) /\ value(inverse k h)=(1/value h)%fp.
Proof.
 intros M S H NZ. assert (E:current(evaluate times twice start None inverse_chain)=Some(true,prime-2)) by reflexivity.
 destruct(chain_power k h _ _ E M S H) as [B P]. split;[apply squared_split,B|].
 apply congruent_value in P. unfold value at 1. rewrite <-power_inverse by exact NZ.
 unfold value. rewrite <-pow_value by (unfold prime;lia). exact P.
Qed.
