From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import isa.Instructions.
From Ed25519Simd.Pow2 Require Import Pow2Caller.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import Wide51.
From Curve25519 Require Import FieldPolynomial.
From Ed25519Simd.Pow2 Require Import Lane Pow2Spec.
Import ListNotations.
Open Scope Z_scope.

Inductive shape := Raw | SquareShape | ProductShape.
Definition limit b := match b with Raw => fun _:nat => imax
                                | SquareShape => smax | ProductShape => omax end.
Definition accepts a b :=
 forallb (fun i=>limit a i <=? limit b i) (seq 0 10).
Definition bounded b (x:field) := forall i, (i<10)%nat -> 0<=x i<=limit b i.
Lemma widen a b x : accepts a b = true -> bounded a x -> bounded b x.
Proof. unfold accepts,bounded; rewrite forallb_forall; intros H B i I.
 specialize (H i ltac:(apply in_seq;lia)); apply Z.leb_le in H; specialize (B i I);lia. Qed.
Definition meta := (shape*Z)%type.
Definition related root (m:meta) x :=
 0 <= snd m /\ bounded (fst m) x /\
 forall i, i=0%nat \/ i=5%nat -> represents (pack x i) (pack root i ^ snd m).

Lemma feed_ok (sq:bool) x y :
 bounded (if sq then SquareShape else Raw) x -> bounded Raw y ->
 forall i, models (feed x y) (initial sq i) (feed x y i).
Proof.
 intros X Y i. unfold initial.
 destruct (Nat.eqb i 28) eqn:E; [apply Nat.eqb_eq in E;subst;split;[reflexivity|vm_compute;easy]|].
 destruct (Nat.eqb i 29) eqn:F; [apply Nat.eqb_eq in F;subst;split;[reflexivity|vm_compute;easy]|].
 unfold models. cbn [term val maximum]. split;[reflexivity|].
 unfold feed; rewrite E,F. destruct (Nat.ltb i 10) eqn:A.
 - apply Nat.ltb_lt in A. specialize (X i A). destruct sq; exact X.
 - destruct (Nat.leb 32 i && Nat.ltb i 42) eqn:H.
   + apply Bool.andb_true_iff in H as [L U]; apply Nat.leb_le in L;apply Nat.ltb_lt in U.
     apply Y;lia.
   + pose proof (Z.mod_pos_bound (x i) (2^64) ltac:(vm_compute;reflexivity));lia.
Qed.

Lemma feed_left x y i : (i=0%nat \/ i=5%nat) -> pack (feed x y) i = pack x i.
Proof. intros [-> | ->]; reflexivity. Qed.
Lemma feed_right x y i : (i=0%nat \/ i=5%nat) -> pack (feed x y) (32+i)%nat = pack y i.
Proof. intros [-> | ->]; reflexivity. Qed.
Definition apply_code sq code (x y:field) := run_kernel code (feed x (if sq:bool then x else y)).
Lemma call_ok sq code root a b x y :
 check_kernel sq code=true -> related root a x -> related root b y ->
 accepts (fst a) (if sq then SquareShape else Raw)=true ->
 accepts (if sq then fst a else fst b) Raw=true ->
 related root (if sq then SquareShape else ProductShape, snd a + (if sq then snd a else snd b))
              (apply_code sq code x y).
Proof.
 intros K [A [X Rx]] [B [Y Ry]] U W. unfold apply_code.
 destruct sq; cbn [fst snd] in *.
 - specialize (kernel_correct _ _ K _ (feed_ok true x x (widen _ _ _ U X) (widen _ _ _ W X))) as [H T].
   split; [cbn;lia|]. split; [exact H|]. intros i I; specialize (T i I).
   rewrite (feed_left _ _ i I) in T. eapply ctrans; [exact T|].
   cbn [snd]. rewrite Z.pow_add_r by lia. apply ctimes; auto.
 - specialize (kernel_correct _ _ K _ (feed_ok false x y (widen _ _ _ U X) (widen _ _ _ W Y))) as [H T].
   split; [cbn;lia|]. split; [exact H|]. intros i I; specialize (T i I).
   rewrite (feed_left _ _ i I), (feed_right _ _ i I) in T. eapply ctrans; [exact T|].
   cbn [snd]. rewrite Z.pow_add_r by lia. apply ctimes; auto.
Qed.

Definition analysis := (meta * (nat -> option meta))%type.
Definition analyze1 op (st:analysis) : option analysis :=
 let '(m,s):=st in match op with
 | Store j=>Some (m,put s j (Some m))
 | Square=>if accepts (fst m) SquareShape && accepts (fst m) Raw
           then Some ((SquareShape, snd m + snd m),s) else None
 | Product j=>match s j with
   | Some n=>if accepts (fst m) Raw && accepts (fst n) Raw
             then Some ((ProductShape,snd m+snd n),s) else None
   | None=>None end end.
Fixpoint analyze ops st := match ops with
 | []=>Some st | op::xs=>match analyze1 op st with Some s=>analyze xs s | None=>None end end.
Definition invariant root (c:analysis) (s:machine) :=
 related root (fst c) (fst s) /\
 forall j n, snd c j = Some n -> related root n (snd s j).
Lemma step_ok sq mul root op st m next :
 check_kernel true sq=true -> check_kernel false mul=true ->
 invariant root m st -> analyze1 op m=Some next -> invariant root next (advance sq mul op st).
Proof.
 destruct st as [x mem], m as [a slots]. intros Q M [R S].
 destruct op as [j|j|]; cbn [advance analyze1 fst snd] in *.
 - intros [= <-]. split; [exact R|]. intros k n. cbn; unfold put.
   destruct (Nat.eqb j k); [intros [= <-];exact R|auto].
 - destruct (slots j) as [b|] eqn:J; [|discriminate].
   destruct (accepts (fst a) Raw && accepts (fst b) Raw) eqn:G; [|discriminate].
   intros [= <-]. apply Bool.andb_true_iff in G as [G H]. split; [|exact S].
   apply (call_ok false mul root a b x (mem j)); auto.
 - destruct (accepts (fst a) SquareShape && accepts (fst a) Raw) eqn:G; [|discriminate].
   intros [= <-]. apply Bool.andb_true_iff in G as [G H]. split; [|exact S].
   apply (call_ok true sq root a a x x); auto.
Qed.
Lemma trace_ok sq mul root ops c s last :
 check_kernel true sq=true -> check_kernel false mul=true ->
 invariant root c s -> analyze ops c=Some last ->
 invariant root last (fold_left (fun st op=>advance sq mul op st) ops s).
Proof.
 intros Q M. revert c s; induction ops as [|op xs IH]; intros c s H T.
 - inversion T;subst;auto.
 - cbn [analyze] in T. destruct (analyze1 op c) eqn:E; [|discriminate].
   cbn [fold_left]. eapply IH; eauto using step_ok.
Qed.
Definition initial_meta : analysis := ((Raw,1),fun _=>None).
Definition check_chain c :=
 match analyze c initial_meta with
 | Some (m,_)=> Z.eqb (snd m) exponent && accepts (fst m) ProductShape
 | None=>false end.
Theorem pow2_correct sq mul c :
 check_kernel true sq=true -> check_kernel false mul=true -> check_chain c=true ->
 forall x scratch, bounded Raw x ->
 let out:=execute sq mul c x scratch in
 bounded ProductShape out /\
 forall i, i=0%nat \/ i=5%nat -> pack out i mod prime = (pack x i ^ exponent) mod prime.
Proof.
 intros Q M T x scratch B. unfold check_chain in T.
 destruct (analyze c initial_meta) as [[m slots]|] eqn:E; [|discriminate].
 apply Bool.andb_true_iff in T as [P U]. apply Z.eqb_eq in P.
 assert (I:invariant x initial_meta (x,scratch)).
 { split; [|intros j n;discriminate]. split; [cbn;lia|]. split; [exact B|].
   cbn [fst snd]. intros. rewrite Z.pow_1_r. apply crefl. }
 destruct (trace_ok sq mul x _ _ _ _ Q M I E) as [[_ [R H]] _].
 split; [eapply widen; eauto|]. intros j J. specialize (H j J).
 change (represents (pack (execute sq mul c x scratch) j) (pack x j ^ snd m)) in H.
 destruct H as [k ->]. rewrite P, Z.mod_add by (vm_compute;discriminate). reflexivity.
Qed.
