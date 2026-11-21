From Coq Require Import ZArith Znumtheory Lia.
From Machine Require Import isa.X86 isa.Arithmetic isa.Logic isa.Shift isa.IFMA.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Import Limbs.
Local Open Scope Z_scope.

Definition scale_input h i := if Nat.eqb i 0 then vpsubq (h i) 1 else h i.
Definition low h i := vpandq (vpmullq (scale_input h i) 121666) (radix-1).
Definition high h i := madd52 true 0 (scale_input h i) (vpaddq 121666 121666).
Definition scaled h i := match i with
 | O=>madd52 false (low h i) (high h 4%nat) 19
 | S j=>vpaddq (low h i) (high h j) end.
Definition difference h i := vpsubq
 (vpaddq (h i) ((radix-if Nat.eqb i 0 then 19 else 1)*1024)) (scaled h i).
Definition reduced d i := let hi j:=vpsrlq (d j) 51 in let lo:=vpandq (d i) (radix-1) in
 match i with O=>madd52 false lo (hi 4%nat) 19 | S j=>vpaddq lo (hi j) end.

Local Lemma word_exact n : 0<=n<2^64 -> low64 n=n.
Proof. intro B;unfold low64;rewrite Z.land_ones,Z.mod_small by lia;reflexivity. Qed.
Local Lemma word_low n : vpandq (low64 n) (radix-1)=n mod radix.
Proof.
 unfold vpandq,low64. change (radix-1) with (Z.ones 51). rewrite !Z.land_ones by lia.
 apply eq_sym,Zmod_div_mod;unfold radix;first [lia|exists 8192;reflexivity].
Qed.
Local Lemma halves h i : bounded h -> 2<=h 0%nat -> (i<5)%nat ->
 low h i=scaled_digit h i mod radix /\ high h i=scaled_digit h i/radix.
Proof.
 intros B L I. specialize(B i I).
 set (n:=h i-if Nat.eqb i 0 then 1 else 0).
 assert (N:0<=n<=radix+2^22) by (unfold n;destruct(Nat.eqb_spec i 0);subst;lia).
 assert (A:scale_input h i=n).
 { unfold scale_input,n,vpsubq. destruct(Nat.eqb_spec i 0);[subst;apply word_exact|];
   unfold radix in *;lia. }
 unfold low,high,scaled_digit;fold n;rewrite A. split.
 - unfold vpmullq;rewrite word_low;f_equal;ring.
 - change (vpaddq 121666 121666) with 243332. unfold madd52. rewrite !Z.land_ones by lia.
   rewrite (Z.mod_small n) by (unfold radix in *;lia).
   change (243332 mod 2^52) with 243332. rewrite Z.shiftr_div_pow2 by lia.
   replace (n*243332) with ((121666*n)*2) by ring.
   change (2^52) with (radix*2). rewrite Z.div_mul_cancel_r by (unfold radix;lia).
   rewrite Z.add_0_l. apply word_exact. split;[apply Z.div_pos|apply Z.div_lt_upper_bound];unfold radix in *;lia.
Qed.
Local Lemma folded lo hi : 0<=lo<radix -> 0<=hi<=121667 ->
 madd52 false lo hi 19=lo+19*hi.
Proof.
 intros L H;unfold madd52. rewrite !Z.land_ones by lia. rewrite (Z.mod_small hi) by lia.
 change (19 mod 2^52) with 19. rewrite (Z.mod_small (hi*19)) by lia.
 rewrite word_exact by (unfold radix in *;lia). ring.
Qed.
Lemma scale_native h : bounded h -> 2<=h 0%nat -> forall i,(i<5)%nat ->
 scaled h i=u_digits h i /\ difference h i=biased_digit h i /\
 reduced (difference h) i=v_digits h i.
Proof.
 intros H L. pose proof (halves h) as Halves.
 assert (Hi:forall i,(i<5)%nat -> 0<=scaled_digit h i/radix<=121667).
 { intros i I; specialize(H i I);unfold scaled_digit. destruct (Nat.eqb_spec i 0);subst;
   split;[apply Z.div_pos|apply Z.div_le_upper_bound|apply Z.div_pos|apply Z.div_le_upper_bound];unfold radix in *;lia. }
 assert (Lo:forall n, 0<=n mod radix<radix) by (intro;apply Z.mod_pos_bound;unfold radix;lia).
 assert (U:forall i,(i<5)%nat->scaled h i=u_digits h i).
 { intros i I;unfold u_digits;rewrite finite_at by exact I. unfold scaled,carry. rewrite (proj1 (Halves i H L I)).
   destruct i as [|j].
   - rewrite (proj2(Halves 4%nat H L ltac:(lia)));apply folded;auto.
   - rewrite (proj2(Halves j H L ltac:(lia)));unfold vpaddq;apply word_exact.
     specialize(Lo (scaled_digit h (S j)));specialize(Hi j ltac:(lia));unfold radix in *;lia. }
 destruct (scaled_bounds _ H L) as [BU _].
 assert (D:forall i,(i<5)%nat->difference h i=biased_digit h i).
 { intros i I;specialize(H i I);specialize(BU i I);unfold difference,biased_digit,vpaddq,vpsubq.
   rewrite U by auto. destruct(Nat.eqb i 0);rewrite (word_exact (h i+_)) by (unfold radix in *;lia);rewrite word_exact by (unfold radix in *;lia);ring. }
 assert (BD:forall i,(i<5)%nat -> 0<=biased_digit h i<=1025*radix+2^22).
 { intros i I;specialize(H i I);specialize(BU i I);unfold biased_digit;
   destruct(Nat.eqb i 0);unfold radix in *;lia. }
 assert (C:forall i,(i<5)%nat->0<=biased_digit h i/radix<=1026).
 { intros i I;specialize(BD i I);split;[apply Z.div_pos|apply Z.div_le_upper_bound];unfold radix in *;lia. }
 intros i I;split;[auto|]. split;[auto|].
 unfold v_digits;rewrite finite_at by exact I. unfold reduced,carry,vpandq,vpsrlq. rewrite D by auto. change (radix-1) with (Z.ones 51).
 rewrite Z.land_ones by lia. change (2^51) with radix. destruct i as [|j];
 rewrite D,Z.shiftr_div_pow2 by lia;change (2^Z.of_nat 51) with radix.
 - apply folded;auto. specialize(C 4%nat ltac:(lia));lia.
 - unfold vpaddq;apply word_exact. specialize(Lo (biased_digit h (S j))); specialize(C j ltac:(lia));unfold radix in *;lia.
Qed.

Lemma scaled_fields h : bounded h -> 2<=h 0%nat ->
 finite(scaled h)=u_digits h /\ finite(reduced(difference h))=v_digits h.
Proof.
 intros B L;split; apply finite_eq;intros i I;
 destruct(scale_native _ B L i I) as [U [_ V]]; unfold u_digits,v_digits in U,V;
 rewrite !finite_at in U,V by exact I; assumption.
Qed.

Definition parity_after h :=
 let advance:=fun c i=>vpsrlq (vpaddq (h i) c) 51 in
 let c:=advance 19 0%nat in let c:=advance c 1%nat in let c:=advance c 2%nat in
 negb (Z.land (vpxorq (h 0%nat) (advance (advance c 3%nat) 4%nat)) 1 =? 0).
Lemma parity_after_ok h : bounded h -> parity_after h=canonical_odd h.
Proof.
 intro B. assert (Step:forall d c, 0<=d<=radix+2^22 -> 0<=c<=19 ->
   vpsrlq (vpaddq d c) 51=(d+c)/radix /\ 0<=(d+c)/radix<=19).
 { intros d c D C. unfold vpaddq,vpsrlq. rewrite word_exact by (unfold radix in *;lia).
   rewrite Z.shiftr_div_pow2 by lia. split;[reflexivity|].
   split;[apply Z.div_pos|apply Z.div_le_upper_bound];unfold radix in *;lia. }
 unfold parity_after,canonical_odd,parity_carry.
 destruct (Step _ 19 (B 0%nat ltac:(lia)) ltac:(lia)) as [A CA].
 destruct (Step _ _ (B 1%nat ltac:(lia)) CA) as [D CD].
 destruct (Step _ _ (B 2%nat ltac:(lia)) CD) as [E CE].
 destruct (Step _ _ (B 3%nat ltac:(lia)) CE) as [F CF].
 destruct (Step _ _ (B 4%nat ltac:(lia)) CF) as [G CG].
 rewrite A,D,E,F,G. unfold vpxorq. match goal with |- context[Z.lxor ?x ?y] => generalize (Z.lxor x y);intro n end.
 change 1 with (Z.ones 1). rewrite Z.land_ones by lia.
 change (2^1) with 2. rewrite Zmod_odd;destruct (Z.odd n);reflexivity.
Qed.

Definition native_neg h := finite(fun i=>vpsubq
 (if Nat.eqb i 0 then 2*(radix-19) else vpaddq (radix-1) (radix-1)) (h i)).
Lemma native_neg_ok h : bounded h -> native_neg h=finite(neg_digits h).
Proof.
 intro B;apply finite_eq;intros i I. specialize(B i I);unfold neg_digits,vpsubq.
 destruct (Nat.eqb i 0);[|change (vpaddq (radix-1) (radix-1)) with (2*(radix-1))];
 apply word_exact;unfold radix in *;lia.
Qed.
