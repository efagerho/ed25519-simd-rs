From Coq Require Import List ZArith Bool Lia Ring.
From Machine Require Import Instructions.
Require Import FieldSpec Polynomial Interval ScalarSpec.
Import ListNotations. Open Scope Z_scope.

(* This checker reuses the existing proved interval and polynomial engines.
   Masks are checked at each instruction; no special mask register is trusted. *)
Definition rhs dst op := match op with
 | Copy a=>V a | Load _ _ | Xor _ _ | MaddMem _ _ _ _=>C 0
 | Add a b=>Rem(Plus(V a)(V b))W
 | Sub a b=>Rem(Plus(V a)(Times(C(-1))(V b)))W
 | Mul a b=>Rem(Times(V a)(V b))W
 | Shl a n=>Rem(Times(V a)(C(2^Z.of_nat n)))W
 | Shr a n=>Quot(V a)(2^Z.of_nat n)
 | And a _=>Rem(V a)B
 | Madd high a b=>let p:=Times(Rem(V a)B)(Rem(V b)B)in
   Rem(Plus(V dst)(if high then Quot p B else Rem p B))W end.
Definition step loads s dst op := match op with
 | Load b d=>loads b d | _=>abstract s(rhs dst op) end.
Definition singleton a n := (lower a=?n)&&(upper a=?n).
Definition supported s op := match op with
 | Xor a b=>Nat.eqb a b | And _ b=>singleton(s b)(B-1)
 | MaddMem _ _ _ _=>false | _=>true end.
Definition legal_step s (i:instruction) := encodable i && supported s(snd i) && legal(rhs(fst i)(snd i)).
Fixpoint arun loads code s := match code with []=>s | (d,op)::tail=>
 arun loads tail(put s d(step loads s d op)) end.
Fixpoint check loads code s := match code with []=>true | (d,op)::tail=>
 legal_step s(d,op) && check loads tail(put s d(step loads s d op)) end.
Definition loads_of (code:list instruction) := flat_map(fun i=>match snd i with Load b d=>[(b,d)] | _=>[] end)code.
Lemma singleton_sound env (s:nat->interval) (r:nat->Z) b n : (forall i,models env(s i)(r i)) ->
 singleton(s b)n=true ->r b=n.
Proof. intros H E;unfold singleton in E;rewrite andb_true_iff,!Z.eqb_eq in E.
 destruct(H b)as[_ Bound];destruct E;lia. Qed.
Lemma rhs_ok env s load r d op : (forall i,models env(s i)(r i)) ->supported s op=true ->
 bits load r d op=match op with Load b disp=>load b disp | _=>val r(rhs d op) end.
Proof.
 intros M Form;destruct op;cbn [supported] in Form;try discriminate.
 - reflexivity.
 - reflexivity.
 - apply Nat.eqb_eq in Form;subst;apply Z.lxor_nilpotent.
 - cbn [bits rhs val];unfold Arithmetic.vpaddq,X86.low64,W;now rewrite Z.land_ones by lia.
 - cbn [bits rhs val];unfold Arithmetic.vpsubq,X86.low64,W;rewrite Z.land_ones by lia;f_equal;ring.
 - cbn [bits rhs val];unfold Arithmetic.vpmullq,X86.low64,W;now rewrite Z.land_ones by lia.
 - cbn [bits rhs val];unfold Shift.vpsllq,X86.low64,W.
   rewrite Z.land_ones,Z.shiftl_mul_pow2 by lia;reflexivity.
 - cbn [bits rhs val];unfold Shift.vpsrlq;now rewrite Z.shiftr_div_pow2 by lia.
 - pose proof(singleton_sound env s r b (B-1) M Form)as Mask.
   cbn [bits rhs val];unfold Logic.vpandq;rewrite Mask.
   change(Z.land(r a)(Z.ones 52)=r a mod 2^52);apply Z.land_ones;lia.
 - cbn [bits rhs val];unfold IFMA.madd52,X86.low64,B,W.
   repeat rewrite Z.land_ones by lia;destruct high;
   try rewrite Z.shiftr_div_pow2 by lia;reflexivity.
Qed.
Theorem run_ok env loads load code s r :
 (forall b d,In(b,d)(loads_of code)->models env(loads b d)(load b d)) ->
 (forall i,models env(s i)(r i)) ->check loads code s=true ->
 forall i,models env(arun loads code s i)(run load code r i).
Proof.
 revert s r;induction code as[|[d op]tail IH];intros s r Mem Reg Check;[exact Reg|].
 cbn [check] in Check;apply andb_true_iff in Check as[Head Tail].
 unfold legal_step in Head;cbn [fst snd] in Head.
 repeat rewrite andb_true_iff in Head;destruct Head as[[Enc Form]Legal].
 cbn [arun run];apply IH;[| |exact Tail].
 - intros b disp I;apply Mem;unfold loads_of in *;cbn;apply in_or_app;now right.
 - intro i;unfold put;destruct(Nat.eqb d i);[|apply Reg].
   rewrite(rhs_ok env s load r d op Reg Form).
   destruct op;cbn [step];try(apply abstract_ok;assumption).
   apply Mem;now left.
Qed.

Definition exact_zero (p:polynomial) := forallb(fun t=>Z.eqb(snd t)0)p.
Lemma exact_zero_sound env p : exact_zero p=true ->polyval env p=0.
Proof. induction p as[|[m c]tail IH];cbn [exact_zero forallb polyval];[auto|].
 rewrite andb_true_iff;intros[C T];apply Z.eqb_eq in C;cbn in C;subst c;rewrite(IH T);ring. Qed.
Definition equal_expr a b := exact_zero(norm(Plus a(Times(C(-1))b))).
Lemma equal_expr_sound env a b : equal_expr a b=true ->val env a=val env b.
Proof. intro E;apply(exact_zero_sound env)in E;rewrite norm_ok in E;cbn [val]in E;lia. Qed.
Fixpoint numberE base (xs:list expr) := match xs with []=>C 0 | x::tail=>Plus x(Times(C base)(numberE base tail))end.
Lemma numberE_sound env base xs : val env(numberE base xs)=number base(map(val env)xs).
Proof. induction xs;cbn;congruence. Qed.
