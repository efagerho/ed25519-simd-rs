From Coq Require Import ZArith List Bool Strings.String Numbers.DecimalString.
From Machine Require Import isa.Instructions.
Import ListNotations.
Open Scope Z_scope.

(* One instruction can change only its named destination, for any input state. *)
Lemma preserved load dst op regs other : dst <> other ->
  run load [(dst, op)] regs other = regs other.
Proof. intro H. cbn [run]. unfold put. apply Nat.eqb_neq in H. now rewrite H. Qed.

Definition initial (overrides : list (nat * list Z)) lane reg :=
  match find (fun pair => Nat.eqb (fst pair) reg) overrides with
  | Some (_, lanes) => nth lane lanes 0
  | None => Z.of_nat (8 * reg + lane)
  end.

Definition numbers (values : list Z) :=
  String.concat " " (map (fun x => NilZero.string_of_int (Z.to_int x)) values).

Definition probe_seeds := [0;1;2;2^52-1;2^52;2^63;2^64-1].
Definition initial_word seed i := (seed + 0x0101010101010101 * i) mod 2^64.
Definition initial_zmm seed (lane reg : nat) := initial_word seed (Z.of_nat (8*reg+lane)).

Definition prediction (i : instruction) overrides (base : nat) disp memory :=
  let load lane b d := if Nat.eqb b base && Z.eqb d disp then nth lane memory 0 else 0 in
  let output lane := run (load lane) [i] (initial overrides lane) (fst i) in
  if encodable i then String.append (numbers (encode i))
    (String.append "|" (numbers (map output (seq 0 8)))) else "invalid"%string.
