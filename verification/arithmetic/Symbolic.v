From Coq Require Import ZArith Lia.
From Machine Require Import Instructions.
From ProofArithmetic Require Export Expressions.
Open Scope Z_scope.

Definition rhs (mask_bits:Z) dst op := match op with
 | MaddMem _ _ _ _ => C 0
 | Copy a => V a | Load _ _ | Xor _ _ => C 0
 | Add a b => Rem (Plus (V a) (V b)) (2^64)
 | Sub a b => Rem (Plus (V a) (Times (C (-1)) (V b))) (2^64)
 | Mul a b => Rem (Times (V a) (V b)) (2^64)
 | Shl a n => Rem (Times (V a) (C (2^Z.of_nat n))) (2^64)
 | Shr a n => Quot (V a) (2^Z.of_nat n)
 | And a _ => Rem (V a) (2^mask_bits)
 | Madd high a b => let p:=Times (Rem (V a) (2^52)) (Rem (V b) (2^52)) in
   Rem (Plus (V dst) (if high then Quot p (2^52) else Rem p (2^52))) (2^64) end.

(* AND's mask width varies by algorithm. IFMA's width remains fixed at 52. *)
Definition operand_ok mask_bits (r:nat->Z) op := match op with
 | Xor a b=>a=b | And _ b=>r b=Z.ones mask_bits | _=>True end.
Theorem rhs_ok mask_bits load r dst op :
 0<=mask_bits -> operand_ok mask_bits r op ->
 bits load r dst op = match op with
 | Load b d=>load b d
 | MaddMem high a b d=>IFMA.madd52 high (r dst) (r a) (load b d)
 | _=>val r(rhs mask_bits dst op) end.
Proof.
 intros Width Form;destruct op;cbn [operand_ok] in Form;try subst b.
 all: cbv beta iota zeta delta [bits rhs val Move.copy Logic.vpxorq Logic.vpandq
   Arithmetic.vpaddq Arithmetic.vpsubq Arithmetic.vpmullq Shift.vpsllq Shift.vpsrlq IFMA.madd52 X86.low64];
 try rewrite Z.lxor_nilpotent;
 try rewrite Z.shiftl_mul_pow2 by lia;
 try rewrite Z.shiftr_div_pow2 by lia;
 repeat rewrite Z.land_ones by lia;try reflexivity.
 - rewrite Form;now rewrite Z.land_ones by lia.
 - destruct high;repeat rewrite Z.land_ones by lia;
   try rewrite Z.shiftr_div_pow2 by lia;reflexivity.
Qed.
