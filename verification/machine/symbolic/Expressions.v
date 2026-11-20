From Coq Require Import ZArith Lia.
From Machine Require Import Instructions.
From ProofArithmetic Require Export Expressions.
Open Scope Z_scope.

Definition madd_expr (high:bool) acc a b :=
 let p:=Times (Rem a (2^52)) (Rem b (2^52)) in
 Rem (Plus acc (if high then Quot p (2^52) else Rem p (2^52))) (2^64).
Definition rhs (mask_bits:Z) dst op : option expr := match op with
 | Load _ _ | MaddMem _ _ _ _ => None
 | Copy a => Some (V a) | Xor _ _ => Some (C 0)
 | Add a b => Some (Rem (Plus (V a) (V b)) (2^64))
 | Sub a b => Some (Rem (Plus (V a) (Times (C (-1)) (V b))) (2^64))
 | Mul a b => Some (Rem (Times (V a) (V b)) (2^64))
 | Shl a n => Some (Rem (Times (V a) (C (2^Z.of_nat n))) (2^64))
 | Shr a n => Some (Quot (V a) (2^Z.of_nat n))
 | And a _ => Some (Rem (V a) (2^mask_bits))
 | Madd high a b => Some (madd_expr high (V dst) (V a) (V b)) end.

(* AND's mask width varies by algorithm. IFMA's width remains fixed at 52. *)
Definition operand_ok mask_bits (r:nat->Z) op := match op with
 | Xor a b=>a=b | And _ b=>r b=Z.ones mask_bits | _=>True end.
Theorem rhs_ok mask_bits load r dst op e :
 0<=mask_bits -> operand_ok mask_bits r op ->
 rhs mask_bits dst op = Some e -> bits load r dst op = val r e.
Proof.
 intros Width Form;destruct op;cbn [operand_ok] in Form;try subst b;
 cbn [rhs];intro E;try discriminate;injection E as <-.
 all: cbv beta iota zeta delta [bits madd_expr val Move.copy Logic.vpxorq Logic.vpandq
   Arithmetic.vpaddq Arithmetic.vpsubq Arithmetic.vpmullq Shift.vpsllq Shift.vpsrlq IFMA.madd52 X86.low64];
 try rewrite Z.lxor_nilpotent;
 try rewrite Z.shiftl_mul_pow2 by lia;
 try rewrite Z.shiftr_div_pow2 by lia;
 repeat rewrite Z.land_ones by lia;try reflexivity.
 - rewrite Form;now rewrite Z.land_ones by lia.
 - destruct high;repeat rewrite Z.land_ones by lia;
   try rewrite Z.shiftr_div_pow2 by lia;reflexivity.
Qed.
