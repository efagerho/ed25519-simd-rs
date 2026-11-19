(* Intel syntax for the operand forms implemented by Machine.ProgramLayout and
   Machine.Instructions. The notation expands to ordinary Coq terms. *)
From Coq Require Import List ZArith.
From Machine Require Import ProgramLayout Instructions.
From Machine Require Assembly.
Import ListNotations.
Open Scope Z_scope.

Include Assembly.

Declare Custom Entry intel_gpr32.
Declare Custom Entry intel_gpr64.
Declare Custom Entry intel_zmm.
Declare Custom Entry intel_memory.
Declare Custom Entry intel_op.
Declare Custom Entry intel_vector.
Declare Custom Entry intel_label.
Declare Custom Entry intel_exit.

Notation "'eax'" := (0%nat) (in custom intel_gpr32 at level 0).
Notation "'ecx'" := (1%nat) (in custom intel_gpr32 at level 0).
Notation "'edx'" := (2%nat) (in custom intel_gpr32 at level 0).
Notation "'ebx'" := (3%nat) (in custom intel_gpr32 at level 0).
Notation "'esp'" := (4%nat) (in custom intel_gpr32 at level 0).
Notation "'ebp'" := (5%nat) (in custom intel_gpr32 at level 0).
Notation "'esi'" := (6%nat) (in custom intel_gpr32 at level 0).
Notation "'edi'" := (7%nat) (in custom intel_gpr32 at level 0).

Notation "'rax'" := (0%nat) (in custom intel_gpr64 at level 0).
Notation "'rcx'" := (1%nat) (in custom intel_gpr64 at level 0).
Notation "'rdx'" := (2%nat) (in custom intel_gpr64 at level 0).
Notation "'rbx'" := (3%nat) (in custom intel_gpr64 at level 0).
Notation "'rsp'" := (4%nat) (in custom intel_gpr64 at level 0).
Notation "'rbp'" := (5%nat) (in custom intel_gpr64 at level 0).
Notation "'rsi'" := (6%nat) (in custom intel_gpr64 at level 0).
Notation "'rdi'" := (7%nat) (in custom intel_gpr64 at level 0).
Notation "'r8'" := (8%nat) (in custom intel_gpr64 at level 0).
Notation "'r9'" := (9%nat) (in custom intel_gpr64 at level 0).
Notation "'r10'" := (10%nat) (in custom intel_gpr64 at level 0).
Notation "'r11'" := (11%nat) (in custom intel_gpr64 at level 0).
Notation "'r12'" := (12%nat) (in custom intel_gpr64 at level 0).
Notation "'r13'" := (13%nat) (in custom intel_gpr64 at level 0).
Notation "'r14'" := (14%nat) (in custom intel_gpr64 at level 0).
Notation "'r15'" := (15%nat) (in custom intel_gpr64 at level 0).

Notation "'zmm0'" := (0%nat) (in custom intel_zmm at level 0).
Notation "'zmm1'" := (1%nat) (in custom intel_zmm at level 0).
Notation "'zmm2'" := (2%nat) (in custom intel_zmm at level 0).
Notation "'zmm3'" := (3%nat) (in custom intel_zmm at level 0).
Notation "'zmm4'" := (4%nat) (in custom intel_zmm at level 0).
Notation "'zmm5'" := (5%nat) (in custom intel_zmm at level 0).
Notation "'zmm6'" := (6%nat) (in custom intel_zmm at level 0).
Notation "'zmm7'" := (7%nat) (in custom intel_zmm at level 0).
Notation "'zmm8'" := (8%nat) (in custom intel_zmm at level 0).
Notation "'zmm9'" := (9%nat) (in custom intel_zmm at level 0).
Notation "'zmm10'" := (10%nat) (in custom intel_zmm at level 0).
Notation "'zmm11'" := (11%nat) (in custom intel_zmm at level 0).
Notation "'zmm12'" := (12%nat) (in custom intel_zmm at level 0).
Notation "'zmm13'" := (13%nat) (in custom intel_zmm at level 0).
Notation "'zmm14'" := (14%nat) (in custom intel_zmm at level 0).
Notation "'zmm15'" := (15%nat) (in custom intel_zmm at level 0).
Notation "'zmm16'" := (16%nat) (in custom intel_zmm at level 0).
Notation "'zmm17'" := (17%nat) (in custom intel_zmm at level 0).
Notation "'zmm18'" := (18%nat) (in custom intel_zmm at level 0).
Notation "'zmm19'" := (19%nat) (in custom intel_zmm at level 0).
Notation "'zmm20'" := (20%nat) (in custom intel_zmm at level 0).
Notation "'zmm21'" := (21%nat) (in custom intel_zmm at level 0).
Notation "'zmm22'" := (22%nat) (in custom intel_zmm at level 0).
Notation "'zmm23'" := (23%nat) (in custom intel_zmm at level 0).
Notation "'zmm24'" := (24%nat) (in custom intel_zmm at level 0).
Notation "'zmm25'" := (25%nat) (in custom intel_zmm at level 0).
Notation "'zmm26'" := (26%nat) (in custom intel_zmm at level 0).
Notation "'zmm27'" := (27%nat) (in custom intel_zmm at level 0).
Notation "'zmm28'" := (28%nat) (in custom intel_zmm at level 0).
Notation "'zmm29'" := (29%nat) (in custom intel_zmm at level 0).
Notation "'zmm30'" := (30%nat) (in custom intel_zmm at level 0).
Notation "'zmm31'" := (31%nat) (in custom intel_zmm at level 0).

Notation "'[' b ']'" := (b, 0%Z)
  (in custom intel_memory at level 0, b custom intel_gpr64).
Notation "'[' b '+' n ']'" := (b, n%Z)
  (in custom intel_memory at level 0, b custom intel_gpr64, n constr at level 0).
Notation "'[' b '-' n ']'" := (b, (-n)%Z)
  (in custom intel_memory at level 0, b custom intel_gpr64, n constr at level 0).

Notation "'ops[' x ; .. ; y ']'" := (cons x .. (cons y nil) ..)
  (x custom intel_op at level 0, y custom intel_op at level 0, only parsing).
Notation "'mov' d , n" := (Mov32 d n%Z)
  (in custom intel_op at level 0, d custom intel_gpr32, n constr at level 0).
Notation "'movabs' 'rax' , n" := (MovAbsRax n%Z)
  (in custom intel_op at level 0, n constr at level 0).
Notation "'vpbroadcastq' d , 'rax'" := (BroadcastRax d)
  (in custom intel_op at level 0, d custom intel_zmm).
Notation "'sub' 'rsp' , n" := (AdjustRsp true n%Z)
  (in custom intel_op at level 0, n constr at level 0).
Notation "'add' 'rsp' , n" := (AdjustRsp false n%Z)
  (in custom intel_op at level 0, n constr at level 0).
Notation "'lea' 'r8' , '[' 'rsp' ']'" := (LeaR8Rsp 0)
  (in custom intel_op at level 0).
Notation "'lea' 'r8' , '[' 'rsp' '+' n ']'" := (LeaR8Rsp n%Z)
  (in custom intel_op at level 0, n constr at level 0).
Notation "'lea' 'r8' , '[' 'rsp' '-' n ']'" := (LeaR8Rsp (-n)%Z)
  (in custom intel_op at level 0, n constr at level 0).
Notation "'mov' 'rbp' , 'rsp'" := (MovReg 5 4) (in custom intel_op at level 0).
Notation "'mov' 'rsi' , 'rsp'" := (MovReg 6 4) (in custom intel_op at level 0).
Notation "'mov' 'rsp' , 'rbp'" := (MovReg 4 5) (in custom intel_op at level 0).
Notation "'and' 'rsp' , '-' '64'" := AlignRsp64 (in custom intel_op at level 0).
Notation "'lea' 'r8' , '[' 'rsi' '+' n ']'" := (LeaR8Rsi n%Z)
  (in custom intel_op at level 0, n constr at level 0).
Notation "'dec' 'ecx'" := DecEcx (in custom intel_op at level 0).
Notation "'vmovdqu64' d , 'zmmword' 'ptr' a" := (LoadZmm d (fst a) (snd a))
  (in custom intel_op at level 0, d custom intel_zmm, a custom intel_memory).
Notation "'vmovdqu64' 'zmmword' 'ptr' a , s" := (StoreZmm s (fst a) (snd a))
  (in custom intel_op at level 0, a custom intel_memory, s custom intel_zmm).
Notation "'vzeroupper'" := ZeroUpper (in custom intel_op at level 0).

Notation "'vecs[' x ; .. ; y ']'" := (cons x .. (cons y nil) ..)
  (x custom intel_vector at level 0, y custom intel_vector at level 0, only parsing).
Notation "'vmovdqa64' d , s" := (d, Copy s)
  (in custom intel_vector at level 0, d custom intel_zmm, s custom intel_zmm).
Notation "'vmovdqu64' d , 'zmmword' 'ptr' a" := (d, Load (fst a) (snd a))
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_memory).
Notation "'vpxorq' d , a , b" := (d, Xor a b)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_zmm).
Notation "'vpaddq' d , a , b" := (d, Add a b)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_zmm).
Notation "'vpsubq' d , a , b" := (d, Sub a b)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_zmm).
Notation "'vpmullq' d , a , b" := (d, Mul a b)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_zmm).
Notation "'vpandq' d , a , b" := (d, And a b)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_zmm).
Notation "'vpmadd52luq' d , a , b" := (d, Madd false a b)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_zmm).
Notation "'vpmadd52huq' d , a , b" := (d, Madd true a b)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_zmm).
Notation "'vpsllq' d , a , n" := (d, Shl a n%nat)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, n constr at level 0).
Notation "'vpsrlq' d , a , n" := (d, Shr a n%nat)
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, n constr at level 0).

(* Labels in a listing denote symbol-relative byte addresses. A label is used
   both at the destination block and wherever a branch names it. *)
Notation "'label[' l ']'" := l (l custom intel_label at level 0, only parsing).
Notation "'ends[' e ']'" := e (e custom intel_exit at level 0, only parsing).
Notation "'call' l" := (CallTo l) (in custom intel_exit at level 0, l custom intel_label).
Notation "'jne' l" := (JneTo l) (in custom intel_exit at level 0, l custom intel_label).
Notation "'ret'" := Return (in custom intel_exit at level 0).

Notation "'push' 'rbp'" := PushFrame (in custom intel_exit at level 0).
Notation "'pop' 'rbp'" := PopFrame (in custom intel_exit at level 0).

Notation "'mov' 'r9' , 'rsp'" := (MovReg 9 4) (in custom intel_op at level 0).
Notation "'mov' 'rcx' , 'rdx'" := (MovReg 1 2) (in custom intel_op at level 0).
Notation "'vpmadd52luq' d , a , 'zmmword' 'ptr' b" := (d, MaddMem false a (fst b) (snd b))
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_memory).
Notation "'vpmadd52huq' d , a , 'zmmword' 'ptr' b" := (d, MaddMem true a (fst b) (snd b))
  (in custom intel_vector at level 0, d custom intel_zmm, a custom intel_zmm, b custom intel_memory).
Notation "'lea' 'r8' , '[' 'rsi' ']'" := (LeaR8Rsi 0)
  (in custom intel_op at level 0).
Notation "'mov' 'rax' , 'rcx'" := (MovReg 0 1) (in custom intel_op at level 0).
