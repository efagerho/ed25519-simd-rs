From Coq Require Import ZArith List Bool.
Import ListNotations. Open Scope Z_scope.

(* Quotients are atoms in ring identities, with their actual integer meaning.
   Rem is expanded by Euclidean division even when the dividend is symbolic. *)
Inductive expr :=
| C (z:Z) | V (i:nat) | Plus (x y:expr) | Times (x y:expr)
| Quot (x:expr) (d:Z) | Rem (x:expr) (d:Z).
Fixpoint val (env:nat -> Z) (e:expr) : Z :=
  match e with
  | C z => z | V i => env i | Plus x y => val env x + val env y
  | Times x y => val env x * val env y
  | Quot x d => val env x / d | Rem x d => val env x mod d end.
Definition expr_dec (a b:expr) : {a=b}+{a<>b}.
Proof. decide equality; first [apply Z.eq_dec | apply Nat.eq_dec]. Defined.

Fixpoint legal e := match e with
 | V _ | C _ => true
 | Plus a b | Times a b => legal a && legal b
 | Rem a d | Quot a d => legal a && (0 <? d) end.
