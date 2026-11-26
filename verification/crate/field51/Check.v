From Coq Require Import List ZArith Lia Bool Ring.
From ProofArithmetic Require Import Interval Polynomial.
From Curve25519 Require Import Field Radix51.
From Machine Require Import isa.Instructions execution.MaskTrace execution.CircuitFacts.
From Ed25519Simd.field51 Require Import Arithmetic.
From Curve25519 Require Import Radix51Zero.
Import ListNotations. Local Open Scope Z_scope.

Definition slot (base i:nat) := (base + match i with O=>4 | S j=>j end)%nat.
Definition var i := V (64+i).
Definition pack_expr a b c d e := Plus a (Times (C radix) (Plus b (Times (C radix)
   (Plus c (Times (C radix) (Plus d (Times (C radix) e))))))).
Definition pack_f {A} (pack:A->A->A->A->A->A) (f:nat->A) :=
 pack (f 0%nat) (f 1%nat) (f 2%nat) (f 3%nat) (f 4%nat).
Definition field_expr base := pack_f pack_expr (fun j=>var(slot base j)).
Definition input_expr base row := pack_f pack_expr (fun j=>atom(Input base (row+j))).
Definition minus a b := Plus a (Times (C (-1)) b).
Definition limit := radix+2^17.
Inductive positive_witness := NoLower | FirstPositive | FromCarry (raw0 raw1 raw4:nat).
Record cut := Cut { base:nat; target:expr; witness:positive_witness }.
Definition needs_positive w := match w with NoLower=>false | _=>true end.
Definition claim env c :=
 let p:=val env (field_expr (base c)) in
 represents p (val env (target c)) /\
 (forall j,(j<5)%nat -> 0<=env (64+slot(base c) j)%nat<=limit) /\
 (needs_positive (witness c)=true -> 0<p).
Definition defined (w:nat->option interval) j := match w j with Some a=>a | None=>I (C 0) 1 0 end.
Definition safe_cell (w:nat->option interval) i := match w i with Some a=>(0<=?lower a)&&(upper a<=?limit) | None=>false end.
Definition positive_check w c :=
 let a j:=defined w (slot(base c) j) in
 match witness c with
 | NoLower=>true | FirstPositive=>0<?lower(a 0%nat)
 | FromCarry i j k=>match w i,w j,w k with Some u,Some v,Some t=>
     (0<?lower u)&&(0<=?lower t) &&
     equal_expr (Plus(term(a 0%nat))(Times(C radix)(term(a 1%nat))))
       (Plus(term u)(Plus (Times(C 19)(Quot(term t)radix)) (Times(C radix)(Rem(term v)radix))))
    |_,_,_=>false end end.
Definition field_check w c :=
 forallb (fun j=>safe_cell w (slot(base c) j)) (seq 0 5) &&
 congruent prime (pack_f pack_expr (fun j=>term(defined w (slot(base c) j)))) (target c) &&
 positive_check w c.

Definition forget w i := match w i with None=>w | Some a=>
 put w i (Some(I (var i) (lower a) (upper a))) end.
Definition reset w c := fold_left forget (map (slot(base c)) (seq 0 5)) w.

Section Inputs.
Variable input_used : nat -> nat -> bool.

Local Lemma cells_ok env v w c : source_ok input_used env v -> state_ok env v w ->
 forallb (fun j=>safe_cell w (slot(base c) j)) (seq 0 5)=true ->
 forall j, (j<5)%nat -> let i:=slot(base c) j in let a:=defined w i in
 val env (term a)=env (64+i)%nat /\ 0<=lower a<=val env (term a) /\
 val env (term a)<=upper a<=limit.
Proof.
 intros [S _] R H j J i a. apply forallb_forall with (x:=j) in H; [|apply in_seq;lia].
 fold i in H. unfold safe_cell in H. destruct(w i) as [t|] eqn:T;try discriminate.
 unfold a,defined;rewrite T. apply andb_true_iff in H as [L U].
 apply Z.leb_le in L,U. specialize(R _ _ T). destruct R as [B E].
 rewrite Z.mod_small in E by (unfold limit,radix,W in *;lia).
 pose proof (S (Wire i) eq_refl) as V. change (env (64+i)%nat=v(Wire i)) in V.
 split; [congruence|lia].
Qed.

Lemma field_check_ok env v w c : source_ok input_used env v -> state_ok env v w ->
 field_check w c=true -> claim env c.
Proof.
 intros S R H;unfold field_check in H;apply andb_true_iff in H as [H P].
 apply andb_true_iff in H as [Digits RingId]. pose proof (cells_ok _ _ _ _ S R Digits) as B. cbv zeta in B.
 apply (congruent_ok prime env) in RingId; [|unfold prime;lia].
 set (p:=val env (field_expr(base c))).
 assert (Eq : val env (pack_f pack_expr (fun j=>term(defined w (slot(base c) j)))) = p).
 { unfold p, field_expr,pack_f,pack_expr,var;cbn [val].
   now rewrite !(fun j H=>proj1 (B j H)) by lia. }
 unfold claim;fold p. split; [rewrite <- Eq;exact RingId|].
 split; [intros j J; specialize (B j J);lia|].
 pose proof (B 0%nat ltac:(lia)) as B0;pose proof (B 1%nat ltac:(lia)) as B1.
 pose proof (B 2%nat ltac:(lia)) as B2;pose proof (B 3%nat ltac:(lia)) as B3;
 pose proof (B 4%nat ltac:(lia)) as B4.
 unfold positive_check in P;destruct(witness c) as [| |i j k];try discriminate;intros _.
 - apply Z.ltb_lt in P. unfold p,field_expr,pack_f,pack_expr,var;cbn [val];unfold radix;lia.
 - destruct(w i) as [u|] eqn:U, (w j) as [y|] eqn:Y, (w k) as [t|] eqn:T;try discriminate.
   apply andb_true_iff in P as [L E]. apply andb_true_iff in L as [L K];apply Z.ltb_lt in L;apply Z.leb_le in K.
   apply (equal_expr_sound env) in E. cbn [val] in E.
   destruct(R _ _ U) as [Bu _];destruct(R _ _ T) as [Bt _].
   pose proof (Z.div_pos (val env(term t)) radix ltac:(lia) ltac:(unfold radix;lia)).
   pose proof (Z.mod_pos_bound (val env(term y)) radix ltac:(unfold radix;lia)).
   unfold p,field_expr,pack_f,pack_expr,var;cbn [val];unfold radix in *;lia.
Qed.

Lemma forget_ok env v w i : source_ok input_used env v -> state_ok env v w ->
 (forall a,w i=Some a -> 0<=lower a /\upper a<W) -> state_ok env v (forget w i).
Proof.
 intros [S _] R Safe;unfold forget. destruct(w i) as [a|] eqn:A;[|exact R].
 intros j t;unfold put; destruct(Nat.eqb_spec i j); [subst j|apply R].
 intros [= <-]. specialize (Safe _ eq_refl). destruct (R _ _ A) as [B E].
 rewrite Z.mod_small in E by lia. pose proof (S (Wire i) eq_refl) as F.
 change (env (64+i)%nat=v(Wire i)) in F.
 unfold word_models;change (lower a<=env (64+i)%nat<=upper a /\ env (64+i)%nat mod W=v(Wire i)).
 rewrite F,<-E,Z.mod_small by lia;auto.
Qed.
Lemma reset_ok env v w c : source_ok input_used env v -> state_ok env v w -> field_check w c=true ->
 state_ok env v (reset w c).
Proof.
 intros S R H. unfold field_check in H;repeat rewrite andb_true_iff in H.
 destruct H as [[Digits _] _]. unfold reset.
 assert (Safe : forall i, In i (map (slot(base c)) (seq 0 5)) -> safe_cell w i=true).
 { intros i I;apply in_map_iff in I as [j [<- J]]. now apply forallb_forall with (x:=j) in Digits. }
 clear Digits. remember (map (slot(base c)) (seq 0 5)) as xs. clear Heqxs.
 revert w R Safe. induction xs as [|i xs IH];intros w R H;cbn [fold_left];[exact R|].
 assert (SafeI:=H i (or_introl eq_refl)). apply IH.
 - apply forget_ok;auto. intros a A; unfold safe_cell in SafeI;rewrite A in SafeI.
   apply andb_true_iff in SafeI as [L U];apply Z.leb_le in L,U;unfold limit,radix,W in *;lia.
 - intros j J. specialize(H j (or_intror J)). unfold forget;destruct(w i) as [a|] eqn:E; [|exact H].
   unfold safe_cell,put;destruct(Nat.eqb_spec i j); [subst; unfold safe_cell in H;rewrite E in H;exact H|exact H].
Qed.

Fixpoint advance n gs w := match gs with []=>w | g::t=>
 advance (S n) t (put w n (abstract_gate input_used w g)) end.
Lemma advance_ok env v gs n w : source_ok input_used env v -> state_ok env v w ->
 satisfies v n gs -> state_ok env v (advance n gs w).
Proof.
 intro S0;revert n w;induction gs as [|g gs IH];intros n w R G;[exact R|].
 apply IH.
 - intros i a; unfold put;destruct(Nat.eqb_spec n i);[subst i|apply R].
   intro A;pose proof (G 0%nat g eq_refl) as V;rewrite Nat.add_0_r in V.
   rewrite V;eapply gate_ok;eassumption.
 - intros i h H. replace (S n+i)%nat with (n+S i)%nat by lia. apply G;exact H.
Qed.

Definition stage := (nat*cut)%type.
Fixpoint verify (plan:list stage) gs n w := match plan with []=>true
 | (len,c)::t=>let prefix:=firstn len gs in let next:=advance n prefix w in
 field_check next c && verify t (skipn len gs) (n+length prefix)%nat (reset next c) end.
Theorem verify_sound plan gs n w env v : source_ok input_used env v -> state_ok env v w ->
 satisfies v n gs -> verify plan gs n w=true -> Forall (fun st=>claim env (snd st)) plan.
Proof.
 intro Src;revert gs n w;induction plan as [|[len c] rest IH];intros gs n w R G H;[constructor|].
 cbn [verify] in H;apply andb_true_iff in H as [F Next].
 set (prefix:=firstn len gs) in *. set (suffix:=skipn len gs) in *.
 assert (Both:gs=prefix++suffix) by (symmetry;apply firstn_skipn).
 rewrite Both in G. assert (A:state_ok env v (advance n prefix w)).
 { apply advance_ok;auto. intros i h E. apply G. rewrite nth_error_app1; [exact E|].
   apply nth_error_Some;congruence. }
 constructor;[eapply field_check_ok;eassumption|]. eapply IH;[eapply reset_ok;eassumption| |exact Next].
 intros i h E. replace (n+length prefix+i)%nat with (n+(length prefix+i))%nat by lia.
 apply G. rewrite nth_error_app2 by lia. now replace (length prefix+i-length prefix)%nat with i by lia.
Qed.
End Inputs.
