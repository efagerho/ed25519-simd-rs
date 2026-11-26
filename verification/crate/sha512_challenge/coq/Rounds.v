From Coq Require Import List NArith ZArith Lia.
From Machine Require Import isa.X86 isa.Arithmetic isa.Shift.
From SHA512 Require Import Spec.
From SHA512 Require Import Compression.
Import ListNotations.
Local Open Scope nat_scope.

(* Unmasked EVEX.512 qword instructions in the compression loop. A K load
   broadcasts one qword from R10 + 8*slot. The other operands are registers. *)
Inductive logic := Parity | Choose | Majority.
Definition immediate op : Z :=
  match op with Parity => 0x96 | Choose => 0xca | Majority => 0xe8 end.
Definition truth op x y z := match op with
  | Parity => xorb (xorb x y) z | Choose => if x then y else z
  | Majority => xorb (xorb (andb x y) (andb x z)) (andb y z) end.
Lemma immediate_correct op x y z :
  truth op x y z = Z.testbit (immediate op) (4*Z.b2z x + 2*Z.b2z y + Z.b2z z).
Proof. destruct op, x, y, z; reflexivity. Qed.

Lemma ternary_bit op x y z i : (i < 64)%N ->
  N.testbit (match op with Parity => xor3 | Choose => ch | Majority => maj end x y z) i =
  Z.testbit (immediate op) (4*Z.b2z (N.testbit x i) + 2*Z.b2z (N.testbit y i) + Z.b2z (N.testbit z i)).
Proof.
  intro I. rewrite <- immediate_correct. destruct op; unfold truth, ch, maj, xor3;
    rewrite ?N.lxor_spec, ?N.land_spec, ?N.lnot_spec_low by auto;
    destruct (N.testbit x i), (N.testbit y i), (N.testbit z i); reflexivity.
Qed.

Inductive op :=
| Add (dst a b : nat) | AddK (dst a slot : nat) | Copy (dst a : nat)
| Ror (dst a n : nat) | Shr (dst a n : nat) | Tern (f : logic) (dst a b : nat).

Definition encode ins : list Z := match ins with
  | Add d a b => encode_vpaddq d a b
  | AddK d a i =>
      evex 1 1 (Z.of_nat d) (Z.of_nat a) 10 true ++
      if Nat.eqb i 0 then [0xd4; modrm 0 (Z.of_nat d) 10]%Z
      else [0xd4; modrm 1 (Z.of_nat d) 10; Z.of_nat i]%Z
  | Copy d a => rr 1 1 0x6f d 0 a
  | Shr d a n => encode_vpsrlq d a n
  | Ror d a n => rr 1 1 0x72 0 d a ++ [Z.of_nat n]
  | Tern f d a b => rr 3 1 0x25 d a b ++ [immediate f]
  end.

(* Symbolic execution keeps the register routing decidable without evaluating
   SHA-512 on concrete test messages. Inputs and K slots are independent. *)
Inductive term :=
| Reg (r:nat) | K (i:nat) | Plus (x y:term) | Rotate (x:term) (n:nat)
| Shift (x:term) (n:nat) | Xor3 (x y z:term) | Ch (x y z:term) | Maj (x y z:term).
Scheme Equality for term.
Fixpoint value (regs k:nat->N) e := match e with
| Reg r => regs r | K i => k i | Plus x y => add64 (value regs k x) (value regs k y)
| Rotate x n => rotate_right (value regs k x) (N.of_nat n)
| Shift x n => N.shiftr (value regs k x) (N.of_nat n)
| Xor3 x y z => xor3 (value regs k x) (value regs k y) (value regs k z)
| Ch x y z => ch (value regs k x) (value regs k y) (value regs k z)
| Maj x y z => maj (value regs k x) (value regs k y) (value regs k z) end.
Definition write_reg (regs : nat -> term) d x i := if Nat.eqb i d then x else regs i.
Definition step (regs : nat -> term) ins := match ins with
  | Add d a b => write_reg regs d (Plus (regs a) (regs b))
  | AddK d a i => write_reg regs d (Plus (regs a) (K i))
  | Copy d a => write_reg regs d (regs a)
  | Ror d a n => write_reg regs d (Rotate (regs a) n)
  | Shr d a n => write_reg regs d (Shift (regs a) n)
  | Tern f d a b => write_reg regs d
      (match f with Parity => Xor3 | Choose => Ch | Majority => Maj end (regs d) (regs a) (regs b))
  end.
Definition coord i j := 16 + (j + 16 - i) mod 8.
Definition view t regs := State (regs (coord (t mod 16) 0)) (regs (coord (t mod 16) 1))
  (regs (coord (t mod 16) 2)) (regs (coord (t mod 16) 3)) (regs (coord (t mod 16) 4)) (regs (coord (t mod 16) 5))
  (regs (coord (t mod 16) 6)) (regs (coord (t mod 16) 7)).
Definition expansion i :=
  let j := (i+1) mod 16 in let k := (i+14) mod 16 in
  [Ror 24 j 1; Ror 25 j 8; Shr 26 j 7; Ror 27 k 19; Ror 28 k 61; Shr 29 k 6;
   Tern Parity 24 25 26; Tern Parity 27 28 29; Add 24 24 i; Add 27 27 ((i+9) mod 16);
   Add i 24 27].
Definition program expanding i :=
  let r := coord i in
  [AddK 24 i i; Ror 25 (r 4) 14; Ror 26 (r 4) 18; Ror 27 (r 4) 41;
   Copy 28 (r 4); Tern Choose 28 (r 5) (r 6);
   Ror 29 (r 0) 28; Ror 30 (r 0) 34; Ror 31 (r 0) 39; Tern Parity 25 26 27;
   Add (r 7) (r 7) 24; Add (r 3) (r 3) (r 7); Copy 24 (r 0);
   Tern Majority 24 (r 1) (r 2); Tern Parity 29 30 31;
   Add (r 3) (r 3) 28; Add 28 28 (r 7); Add (r 3) (r 3) 25;
   Add (r 7) 28 25; Add (r 7) (r 7) 24; Add (r 7) (r 7) 29] ++
   if expanding : bool then expansion i else [].

Definition trace expanding i := fold_left step (program expanding i) Reg.
Definition execute expanding t k regs r := value regs k (trace expanding (t mod 16) r).

Definition expected expanding i r :=
  let c := fun j => Reg (coord i j) in
  let rot3 x u v w := Xor3 (Rotate x u) (Rotate x v) (Rotate x w) in
  let s1 := rot3 (c 4) 14 18 41 in let s0 := rot3 (c 0) 28 34 39 in
  let hkw := Plus (c 7) (Plus (Reg i) (K i)) in
  let ch := Ch (c 4) (c 5) (c 6) in let maj := Maj (c 0) (c 1) (c 2) in
  let w j := Reg ((i+j) mod 16) in
  let sigma x u v w := Xor3 (Rotate x u) (Rotate x v) (Shift x w) in
  if r <? 16 then
    if (expanding && (r =? i))%bool then
      Plus (Plus (sigma (w 1) 1 8 7) (Reg i)) (Plus (sigma (w 14) 19 61 6) (w 9))
    else Reg r
  else nth (r-16)
    [Plus (Plus (Plus (Plus ch hkw) s1) maj) s0; c 0; c 1; c 2;
     Plus (Plus (Plus (c 3) hkw) ch) s1; c 4; c 5; c 6] (Reg r).

Definition physical i r := if r <? 16 then r else coord (S i mod 16) (r-16).
Local Lemma checked expanding i r : i < 16 -> r < 24 ->
  trace expanding i (physical i r) = expected expanding i r.
Proof.
  assert (C : forallb (fun ex => forallb (fun i => forallb (fun r =>
    term_beq (trace ex i (physical i r)) (expected ex i r)) (seq 0 24))
    (seq 0 16)) [true;false] = true) by (vm_compute; reflexivity).
  intros I R. apply internal_term_dec_bl. rewrite forallb_forall in C.
  specialize (C expanding ltac:(destruct expanding; simpl; auto)).
  rewrite forallb_forall in C. specialize (C i ltac:(apply in_seq; lia)).
  rewrite forallb_forall in C. apply C. apply in_seq; lia.
Qed.

Local Lemma succ_slot t : S t mod 16 = S (t mod 16) mod 16.
Proof. replace (S t) with (t+1) by lia. replace (S (t mod 16)) with (t mod 16+1) by lia. now rewrite Nat.add_mod_idemp_l by lia. Qed.

Lemma round_state expanding t k regs :
  view (S t) (execute expanding t k regs) =
  scheduled_round (view t regs) (k (t mod 16), regs (t mod 16)).
Proof.
  unfold view, execute. rewrite succ_slot. set (i:=t mod 16).
  assert (I : i < 16) by (apply Nat.mod_upper_bound; lia).
  repeat match goal with |- context [trace expanding i (coord (S i mod 16) ?j)] =>
    let r := eval compute in (16+j) in
    change (coord (S i mod 16) j) with (physical i r);
    rewrite (checked expanding i r I ltac:(lia))
  end. reflexivity.
Qed.

Lemma round_ring expanding t k regs j : j < 16 ->
  execute expanding t k regs j =
  if expanding then replace_slot regs t (next_word regs t) j else regs j.
Proof.
  intro J. unfold execute. set (i:=t mod 16).
  assert (I : i < 16) by (apply Nat.mod_upper_bound; lia).
  assert (B : (j <? 16) = true) by (apply Nat.ltb_lt; lia).
  pose proof (checked expanding i j I ltac:(lia)) as C.
  unfold physical in C. rewrite B in C. rewrite C. unfold expected. rewrite B.
  unfold replace_slot, next_word, slot.
  rewrite <- (Nat.add_mod_idemp_l t 1 16), <- (Nat.add_mod_idemp_l t 14 16),
          <- (Nat.add_mod_idemp_l t 9 16) by lia.
  fold i. destruct expanding, (j =? i); reflexivity.
Qed.
