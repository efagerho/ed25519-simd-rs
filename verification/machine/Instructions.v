From Coq Require Import ZArith List Bool Strings.String Numbers.DecimalString.
From Machine Require Move Arithmetic Logic Shift IFMA.
Import ListNotations.
Open Scope Z_scope.

(* Unmasked EVEX.512 forms that write a ZMM destination. Register numbers
   name architectural registers. Load takes a GPR base and byte displacement. *)
Inductive opcode :=
| Copy (src : nat) | Load (base : nat) (disp : Z)
| Xor (a b : nat) | Add (a b : nat) | Sub (a b : nat) | Mul (a b : nat)
| Shl (a n : nat) | Shr (a n : nat) | And (a b : nat)
| Madd (high : bool) (a b : nat).
Definition instruction := (nat * opcode)%type.

Definition encodable (i : instruction) :=
  let '(dst, op) := i in
  let zmm n := Nat.ltb n 32 in
  zmm dst && match op with
  | Copy src => zmm src
  | Load base disp => Nat.ltb base 16 && (-2^31 <=? disp) && (disp <? 2^31)
  | Shl a n | Shr a n => zmm a && Nat.ltb n 256
  | Xor a b | Add a b | Sub a b | Mul a b | And a b | Madd _ a b => zmm a && zmm b
  end.

(* At a fixed qword lane, read [base + disp] through the supplied memory view. *)
Definition bits (load : nat -> Z -> Z) (r : nat -> Z) dst op :=
  match op with
  | Copy src => Move.copy (r src)
  | Load base disp => Move.copy (load base disp)
  | Xor a b => Logic.vpxorq (r a) (r b)
  | Add a b => Arithmetic.vpaddq (r a) (r b)
  | Sub a b => Arithmetic.vpsubq (r a) (r b)
  | Mul a b => Arithmetic.vpmullq (r a) (r b)
  | Shl a n => Shift.vpsllq (r a) n
  | Shr a n => Shift.vpsrlq (r a) n
  | And a b => Logic.vpandq (r a) (r b)
  | Madd high a b => IFMA.madd52 high (r dst) (r a) (r b)
  end.

Definition put {A} (s : nat -> A) i x j := if Nat.eqb i j then x else s j.
Fixpoint run (load : nat -> Z -> Z) (code : list instruction) (r : nat -> Z) :=
  match code with
  | [] => r
  | (dst, op) :: rest => run load rest (put r dst (bits load r dst op))
  end.

Definition encode (i : instruction) :=
  let '(dst, op) := i in
  match op with
  | Copy src => Move.encode_vmovdqa64 dst src
  | Load base disp => Move.encode_load dst (Z.of_nat base) disp
  | Xor a b => Logic.encode_vpxorq dst a b
  | Add a b => Arithmetic.encode_vpaddq dst a b
  | Sub a b => Arithmetic.encode_vpsubq dst a b
  | Mul a b => Arithmetic.encode_vpmullq dst a b
  | Shl a n => Shift.encode_vpsllq dst a n
  | Shr a n => Shift.encode_vpsrlq dst a n
  | And a b => Logic.encode_vpandq dst a b
  | Madd high a b => IFMA.encode_madd52 high dst a b
  end.

Open Scope string_scope.

Definition decimal n := NilZero.string_of_uint (Nat.to_uint n).
Definition zmm n := "zmm" ++ decimal n.
Definition gpr (n : nat) :=
  nth n ["rax"; "rcx"; "rdx"; "rbx"; "rsp"; "rbp"; "rsi"; "rdi"] ("r" ++ decimal n).
Definition address base (disp : Z) :=
  "[" ++ gpr base ++
  (if Z.eqb disp 0 then "" else
   (if Z.ltb disp 0 then " - " else " + ") ++ NilZero.string_of_uint (N.to_uint (Z.abs_N disp))) ++ "]".
Definition args3 name d a b := name ++ " " ++ zmm d ++ ", " ++ zmm a ++ ", " ++ zmm b.
Definition asm_of (i : instruction) :=
  let '(d, op) := i in
  match op with
  | Copy a => "vmovdqa64 " ++ zmm d ++ ", " ++ zmm a
  | Load base disp => "vmovdqu64 " ++ zmm d ++ ", zmmword ptr " ++ address base disp
  | Xor a b => args3 "vpxorq" d a b
  | Add a b => args3 "vpaddq" d a b
  | Sub a b => args3 "vpsubq" d a b
  | Mul a b => args3 "vpmullq" d a b
  | And a b => args3 "vpandq" d a b
  | Shl a n => "vpsllq " ++ zmm d ++ ", " ++ zmm a ++ ", " ++ decimal n
  | Shr a n => "vpsrlq " ++ zmm d ++ ", " ++ zmm a ++ ", " ++ decimal n
  | Madd high a b => args3 (if high then "vpmadd52huq" else "vpmadd52luq") d a b
  end.
