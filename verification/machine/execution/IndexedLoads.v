From Coq Require Import List ZArith Bool.
From Machine Require Import isa.IndexedLoad execution.LinkedCalls execution.WordSemantics
  memory.ByteMemory execution.Packed.
Import ListNotations. Local Open Scope Z_scope.

(* A straight-line register/load block has no stores. Every dereference
   therefore observes the block's incoming flat byte memory. The access log
   records the full hardware operand width, even for unused vector lanes. *)
Inductive term :=
| K (n:Z) | G (r:nat) | V (r j:nat)
| Plus (a b:term) | Times (a b:term) | W64 (a:term) | W32 (a:term)
| Band (a b:term) | Bxor (a b:term) | Bor (a b:term) | Right (a:term) (n:nat)
| Read (width:nat) (addr:term).
Scheme Equality for term.
Fixpoint eval (s:cpu) e := match e with
| K n => n | G r => regs s r | V r j => vectors s j r
| Plus a b => eval s a + eval s b | Times a b => eval s a * eval s b
| W64 a => word (eval s a) | W32 a => eval s a mod 2^32
| Band a b => Z.land (eval s a) (eval s b) | Bxor a b => Z.lxor (eval s a) (eval s b)
| Bor a b => Z.lor (eval s a) (eval s b) | Right a n => Z.shiftr (eval s a) (Z.of_nat n)
| Read n a => read_le n (mem s) (eval s a) end.

Inductive zflag := Incoming | Undefined | IsZero (e:term).
Record symbolic := State {
  gp : nat -> term; vec : nat -> nat -> term; zf : zflag;
  loads : list (term * nat)
}.
Definition initial := State G V Incoming [].
Definition effective g a := W64 (Plus (if indexed a then Plus (g (base a)) (g 0%nat)
                                      else g (base a)) (K (displacement a))).
(* Construct the symbolic result and the access log from the same effective
   address. A half-vector read contributes one 32-byte operand even if a
   later permutation discards some qwords. *)
Definition step s op :=
  let g := gp s in let v := vec s in let f := zf s in
  let setg d t flag := State (Packed.update g d t) v flag (loads s) in
  let set32 d t := let w := W32 t in setg d w (IsZero w) in
  let setv d row := State g (Packed.update v d row) f (loads s) in
  let read_operand a width (build : term -> symbolic) :=
    let addr := effective g a in
    let result := build addr in
    State (gp result) (vec result) (zf result) ((addr,width) :: loads s) in
  let at_lane addr j := Read 8 (Plus addr (K (8*Z.of_nat j))) in
  match op with
  | LeaTwice d i => setg d (W64 (Plus (g d) (Times (K 2) (g i)))) f
  | MovZX two a =>
      let n := if two then 2%nat else 1%nat in
      read_operand a n (fun addr => setg 0%nat (Read n addr) f)
  | CopyEaxToR11d => setg 11%nat (W32 (g 0%nat)) f
  | ShrR11d n => set32 11%nat (Right (W32 (g 11%nat)) n)
  | And32 d n => set32 d (Band (g d) (K n))
  | XorEax n => set32 0%nat (Bxor (g 0%nat) (K n))
  | OrEaxR11d => set32 0%nat (Bor (g 0%nat) (g 11%nat))
  | ImulEax n => setg 0%nat (W32 (Times (g 0%nat) (K n))) Undefined
  | AddRax a => read_operand a 8%nat (fun addr =>
      let t := W64 (Plus (g 0%nat) (Read 8 addr)) in setg 0%nat t (IsZero t))
  | LoadY d a => read_operand a 32%nat (fun addr =>
      setv d (fun j => if (j <? 4)%nat then at_lane addr j else K 0))
  | LoadZ d a => read_operand a 64%nat (fun addr => setv d (at_lane addr))
  | InsertY d r a upper => read_operand a 32%nat (fun addr => setv d (fun j =>
      if Bool.eqb (4 <=? j)%nat upper then at_lane addr (j mod 4)%nat else v r j))
  end.
Definition summary code := fold_left step code initial.
Definition execute code s :=
  let t:=summary code in
  CPU (fun r=>eval s (gp t r)) (fun j r=>eval s (vec t r j))
      (match zf t with Incoming=>flag s | Undefined=>None | IsZero e=>Some (eval s e =? 0) end)
      (mem s).
