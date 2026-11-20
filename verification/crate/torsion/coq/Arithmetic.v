From Coq Require Import List ZArith Bool Lia Ring Znumtheory.
From ProofArithmetic Require Import Interval Polynomial.
From Machine Require Import isa.Instructions execution.MaskTrace execution.CircuitFacts.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd.Torsion Require Import Zero.
Import ListNotations. Local Open Scope Z_scope.

(* Keep a signed integer representative across word adds, subtracts and low
   multiplies. This preserves cancellation in the fused determinant. A shift
   explicitly reads the unsigned word, and IFMA reads its two low 52 bits. *)
Definition W := 2^64.
Definition triple {A} (a b c:A) (i:nat) := match i with O=>a|S O=>b|_=>c end.
Definition shape g := match g with
 | AddQ a b | SubQ a b | MulQ a b | AndQ a b | EqQ a b | OrK a b=>triple a b (Lit 0)
 | ShiftQ a _=>triple a (Lit 0) (Lit 0) | MaddQ _ a b c=>triple a b c end.
Definition formula g := match g with
 | AddQ _ _=>Some(Plus (V 0)(V 1)) | SubQ _ _=>Some(Plus (V 0)(Times (C (-1))(V 1)))
 | MulQ _ _=>Some(Times (V 0)(V 1))
 | AndQ _ (Lit k)=>if k=?radix-1 then Some(Rem (V 0) radix) else None
 | ShiftQ _ n=>Some(Quot (Rem (V 0) W) (2^Z.of_nat n))
 | MaddQ high _ _ _=>let prod:=Times (Rem (V 1) split) (Rem (V 2) split) in
     Some(Plus (V 0) (if high then Quot prod split else Rem prod split))
 | _=>None end.
Definition word_models env a z := lower a<=val env (term a)<=upper a /\
                                   val env (term a) mod W = z.
Local Lemma split_word x : (x mod W) mod split = x mod split.
Proof. symmetry; apply Zmod_div_mod; [unfold split;lia|unfold W;lia|exists 4096;reflexivity]. Qed.
Lemma formula_sound g e v r :
 formula g=Some e -> (forall j,r j mod W=v (shape g j)) ->
 (forall n,v (Lit n)=n) -> val r e mod W = denote v g.
Proof.
 intros Form R L. pose proof(R 0%nat) as A;pose proof(R 1%nat) as B;pose proof(R 2%nat) as D.
 destruct g; cbn [formula] in Form; try discriminate.
 all: try (injection Form as <-; cbn [shape triple] in A,B,D;
  cbn [denote val]; unfold Arithmetic.vpaddq,Arithmetic.vpsubq,Arithmetic.vpmullq,X86.low64;
  rewrite Z.land_ones by lia; change (2^64) with W;
  rewrite <-A,<-B; first [apply Zplus_mod | apply Zmult_mod |
    replace (r 0%nat + -1*r 1%nat) with (r 0%nat-r 1%nat) by ring; apply Zminus_mod]).
 - destruct b; try discriminate. destruct (n=?radix-1) eqn:E; try discriminate.
   apply Z.eqb_eq in E; subst n. injection Form as <-. cbn [val].
   cbn [shape triple] in A. cbn [denote]; unfold Logic.vpandq. rewrite L,<-A.
   change (radix-1) with (Z.ones 51). rewrite Z.land_ones by lia.
   change (2^51) with radix. rewrite <- (Zmod_div_mod radix W (r 0%nat)) by
    (first [unfold radix,W;lia|exists 8192;reflexivity]).
   apply Z.mod_small. pose proof (Z.mod_pos_bound (r 0%nat) radix ltac:(unfold radix;lia)).
   unfold W,radix in *;lia.
 - injection Form as <-. cbn [val denote]. cbn [shape triple] in A.
   unfold Shift.vpsrlq; rewrite Z.shiftr_div_pow2 by lia. rewrite <- A.
   apply Z.mod_small. pose proof (Z.mod_pos_bound (r 0%nat) W ltac:(unfold W;lia)).
   assert (0<2^Z.of_nat n) by (apply Z.pow_pos_nonneg;lia).
   split; [apply Z.div_pos;lia|apply Z.div_lt_upper_bound;nia].
 - injection Form as <-. cbn [shape triple] in A,B,D. cbn [denote]. unfold IFMA.madd52,X86.low64.
   rewrite <-A,<-B,<-D. repeat rewrite Z.land_ones by lia.
   change (2^52) with split. rewrite !split_word.
   destruct high; cbn [val]; try rewrite Z.shiftr_div_pow2 by lia;
     try rewrite Z.land_ones by lia; symmetry; apply Zplus_mod_idemp_l.
Qed.
Lemma formula_legal g e : formula g=Some e -> Expressions.legal e=true.
Proof.
 destruct g; cbn [formula]; try (intros [= <-]; reflexivity); try discriminate.
 - destruct b; try discriminate; destruct (_=?_); intros [= <-]; reflexivity.
 - intros [= <-]. cbn [Expressions.legal]. apply Bool.andb_true_iff; split; [reflexivity|].
   apply Z.ltb_lt,Z.pow_pos_nonneg;lia.
 - destruct high; intros [= <-]; reflexivity.
Qed.

Definition atom a := match a with
 | Lit z=>C z | Wire i=>V (64+i) | Input b i=>V ((if Nat.eqb b 7 then 0 else 32)+i)
 | _=>C 0 end.
Definition input_used b i := (Nat.eqb b 7 || (Nat.eqb b 6 && (Nat.ltb i 10 || Nat.leb 15 i))) && Nat.ltb i 20.
Definition supported_arg a := match a with Lit n=>(0<=?n)&&(n<?W) | Wire _=>true
 | Input b i=>input_used b i | _=>false end.
Definition source_ok env v :=
 (forall a, supported_arg a=true -> val env (atom a)=v a) /\
 (forall b i, input_used b i=true -> 0<=v(Input b i)<split) /\
 (forall n,v(Lit n)=n).
Definition abstract_arg (w:nat->option interval) a := match a with
 | Wire i=>w i
 | Input _ _=>if supported_arg a then Some(I (atom a) 0 (split-1)) else None
 | Lit n=>if supported_arg a then Some(I (C n) n n) else None | _=>None end.
Definition state_ok env v w := forall i s,w i=Some s -> word_models env s (v(Wire i)).
Lemma arg_ok env v w : source_ok env v -> state_ok env v w -> forall a s,
 abstract_arg w a=Some s -> word_models env s (v a).
Proof.
 intros [Src [Bounds L]] Reg a s. destruct a; cbn [abstract_arg]; try discriminate; auto.
 - destruct (supported_arg (Lit n)) eqn:OK; try discriminate; intros [= <-].
   cbn [supported_arg] in OK; apply Bool.andb_true_iff in OK as [A B].
   apply Z.leb_le in A; apply Z.ltb_lt in B; unfold word_models;cbn [lower upper I term enclosure lower_bound upper_bound val].
   rewrite L,Z.mod_small by lia;lia.
 - destruct (supported_arg (Input base row)) eqn:OK; try discriminate; intros [= <-].
   pose proof (Src _ OK) as E. specialize (Bounds _ _ OK); unfold word_models;cbn [lower upper I term enclosure lower_bound upper_bound].
   cbn [atom] in E. rewrite E,Z.mod_small by (unfold split,W in *;lia); unfold split in *;lia.
Qed.
Definition abstract_gate w g := match formula g,
  abstract_arg w (shape g 0%nat),abstract_arg w (shape g 1%nat),abstract_arg w (shape g 2%nat) with
 | Some e,Some a,Some b,Some c=>Some(abstract (triple a b c) e) | _,_,_,_=>None end.
Lemma gate_ok env v w g s : source_ok env v -> state_ok env v w ->
 abstract_gate w g=Some s -> word_models env s (denote v g).
Proof.
 intros Src Reg. unfold abstract_gate.
 destruct (formula g) as [e|] eqn:F; try discriminate.
 destruct (abstract_arg w (shape g 0%nat)) as [a|] eqn:A;try discriminate.
 destruct (abstract_arg w (shape g 1%nat)) as [b|] eqn:B;try discriminate.
 destruct (abstract_arg w (shape g 2%nat)) as [c|] eqn:Cc;try discriminate.
 intros [= <-]. apply (arg_ok _ _ _ Src Reg) in A,B,Cc.
 set (s:=triple a b c). set (r:=fun i=>val env (term(s i))).
 assert (R : forall i, word_models env (s i) (v(shape g i))).
 { intros [|[|i]]; [exact A|exact B|].
   change (word_models env c (v(shape g (S(S i))))). destruct g; exact Cc. }
 assert (M : forall i,models env (s i) (r i)) by (intro i; split; [reflexivity|exact (proj1(R i))]).
 destruct (abstract_ok env s r e M (formula_legal _ _ F)) as [Eq Bound].
 unfold word_models; fold s; rewrite Eq; split; [exact Bound|].
 apply formula_sound; [exact F|intro i;exact(proj2(R i))|exact(proj2(proj2 Src))].
Qed.
