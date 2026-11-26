From Coq Require Import List ZArith Bool Lia Ring.
From Coqprime.elliptic Require GZnZ.
From ProofArithmetic Require Import Interval.
From Machine Require Import isa.Instructions.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Import PrimeField.
From Ed25519Simd Require Import FieldKernel FieldSymbolic.
From Ed25519Simd.Decode Require Import Kernels Power.
From Curve25519 Require Import Radix51Digits.
From Ed25519Simd.Decode Require Import Decode.
Import ListNotations. Local Open Scope Z_scope.

Definition two_d := five 1859910466990425 932731440258426 1072319116312658
                         1815898335770999 633789495995903.
Lemma two_d_split : split_field two_d.
Proof. intros [|[|[|[|[|i]]]]] H;vm_compute;easy. Qed.
Lemma two_d_value : value two_d = ((1+1)*d)%fp.
Proof. apply GZnZ.zirr; vm_compute; reflexivity. Qed.

(* For the memory-source instructions, registers 5..9 in this local projection
   denote the five read-only X limbs. They are never architectural writes. *)
Inductive linear := Difference | Sum | Twice.
Definition prefix op := flat_map (fun i => match op with
 | Difference => [(i,Add i (if Nat.eqb i 0 then 30 else 31));(i,Sub i (5+i))]
 | Sum => [(i,Add i (5+i))] | Twice => [(i,Add i i)] end)%nat (seq 0 5).
Definition formula op a b := match op with Difference=>a-b | Sum=>a+b | Twice=>a+a end.
Definition expression op :=
 let a:=packE V 0 in let b:=packE V 5 in match op with
 | Difference=>minus a b | Sum=>Plus a b | Twice=>Plus a a end.
Definition linear_code k op := prefix op ++ Kernels.carry k.
Definition linear_result k op a b := run (fun _ _=>0) (linear_code k op) (feed a b).
Definition checked k op :=
 let code:=linear_code k op in Nat.eqb (length (loads_of code)) 0 &&
 check_kernel code (initial Multiply) [] no_load [0%nat] (fun _=>radix+2^16)
              (fun _=>expression op).
Lemma linear_ok k op a b : checked k op=true -> split_field a -> split_field b ->
 split_field (linear_result k op a b) /\
 represents (limbs (linear_result k op a b)) (formula op (limbs a) (limbs b)).
Proof.
 unfold checked. rewrite andb_true_iff;intros [E C] A B.
 apply Nat.eqb_eq,length_zero_iff_nil in E.
 set (r:=feed a b).
 assert (I:forall i,models r (initial Multiply i) (r i)).
 { intro i;unfold initial,r,feed. destruct (constant i) as [z|] eqn:F;[split;[reflexivity|cbn;lia]|].
   split;[cbn;now rewrite F|]. unfold lower,upper,in_bound;cbn [fst snd].
   destruct (Nat.ltb_spec i 5), (Nat.ltb_spec i 10); try lia.
   - apply A;lia.
   - apply B;lia.
   - cbn;lia. }
 destruct (kernel_correct _ _ _ _ _ _ _ C r (fun _ _=>0) r eq_refl (Forall_nil _)
  ltac:(intros base disp H;rewrite E in H;contradiction) I 0%nat (or_introl eq_refl)) as [Bounds V].
 split.
 - intros i H;specialize(Bounds i H);change (0<=linear_result k op a b i<=radix+2^16) in Bounds.
   unfold radix,split in *;lia.
 - destruct op;unfold formula;try exact V.
Qed.

Inductive cache_op := TwoDT | YMinusX | YPlusX | TwoZ.
Definition field_order := [TwoDT;YMinusX;YPlusX;TwoZ].
Definition field_op c := match c with O=>YMinusX | S O=>YPlusX | S(S O)=>TwoDT | _=>TwoZ end.
Definition column_start op := match op with YMinusX=>0 | YPlusX=>5 | TwoDT=>10 | TwoZ=>15 end%nat.
Definition saved_in op := match op with TwoDT=>5 | YMinusX=>16 | YPlusX=>21 | TwoZ=>0 end%nat.
Definition source op := match op with TwoDT=>3 | TwoZ=>2 | _=>1 end%nat.
Definition rhs op := match op with TwoZ=>2 | _=>0 end%nat.
Definition linear_op op := match op with TwoDT=>None | YMinusX=>Some Difference
 | YPlusX=>Some Sum | TwoZ=>Some Twice end.
Definition compute k (a:nat->field) op := match linear_op op with
 | None=>mul k (a (source op)) two_d
 | Some f=>linear_result k f (a (source op)) (a (rhs op)) end.
