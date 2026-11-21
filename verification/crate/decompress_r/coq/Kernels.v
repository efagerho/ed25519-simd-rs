From Coq Require Import ZArith List Bool Lia.
From ProofArithmetic Require Import Interval.
From Machine Require Import isa.Instructions execution.Dependencies.
From Curve25519 Require Import Field Radix51.
From Ed25519Simd Require Import FieldSymbolic FieldKernel.
Import ListNotations. Local Open Scope Z_scope.

Record kernels := Kernels {
 seed_columns : list instruction; convolve : list instruction;
 fold_columns : list instruction; carry : list instruction;
 tighten : list instruction; square : list instruction
}.
Definition product k := seed_columns k ++ convolve k ++ fold_columns k ++ carry k.
Inductive operation := Multiply | ChainMultiply | Square.
Definition body k op := match op with
 | Multiply => product k | ChainMultiply => product k ++ tighten k | Square => square k end.

Definition constant r := match r with
 | 28%nat => Some 19 | 29%nat => Some (radix-1)
 | 30%nat => Some ((radix-19)*1024) | 31%nat => Some ((radix-1)*1024)
 | _ => None end.
Definition in_bound op i :=
 if Nat.ltb i 10 then match op with Square => square_bound i | _ => split-1 end
 else 2^64-1.
Definition initial op i := match constant i with
 | Some n => I (C n) n n | None => I (V i) 0 (in_bound op i) end.
Definition target op := Times (packE V 0) (packE V (match op with Square=>0 | _=>5 end)).
Definition out_bound op := match op with Multiply => fun _=>radix+2^16 | _=>square_bound end.
Definition no_load (_:nat) (_:Z) := I (C 0) 0 0.
Definition verified k op :=
 let code:=body k op in
 Nat.eqb (length (loads_of code)) 0 &&
 check_kernel code (initial op) [] no_load [0%nat] (out_bound op) (fun _=>target op) &&
 match op with Multiply => 2 <=? lower (arun [] no_load code (initial op) 0%nat)
 | _=>true end.

Definition input op (r:nat->Z) := forall i, match constant i with
 | Some n=>r i=n | None=>0<=r i<=in_bound op i end.
Definition result op (r out:nat->Z) :=
 field_bound (out_bound op) out /\
 represents (limbs out) (limbs r * pack r (match op with Square=>0 | _=>5 end)) /\
 (op=Multiply -> 2<=out 0%nat).

Theorem verified_result k op : verified k op=true ->
 forall r load, input op r -> result op r (run load (body k op) r).
Proof.
 unfold verified. intros H r load R. apply andb_true_iff in H as [H Low].
 apply andb_true_iff in H as [Empty Check]. apply Nat.eqb_eq,length_zero_iff_nil in Empty.
 assert (Mem : forall b d, In (b,d) (loads_of (body k op)) ->
    models r (no_load b d) (load b d)) by (rewrite Empty; contradiction).
 assert (Mask : r 29%nat=radix-1) by exact (R 29%nat).
 assert (Init : forall i, models r (initial op i) (r i)).
 { intro i; specialize (R i); unfold initial. destruct (constant i) as [n|].
   - rewrite R. split; [reflexivity|cbn;lia].
   - split; [reflexivity|exact R]. }
 destruct (kernel_correct _ _ _ _ _ _ _ Check r load r Mask (Forall_nil _) Mem Init
   0%nat (or_introl eq_refl)) as [Bounds Value].
 split; [exact Bounds|]. split; [exact Value|].
 intros ->. apply Z.leb_le in Low. unfold check_kernel in Check.
 apply andb_true_iff in Check as [Valid _].
 destruct (run_ok r [] _ _ _ _ _ (Forall_nil _) Mem Mask Init Valid 0%nat) as [_ Range].
 lia.
Qed.

(* The projection can discard temporaries at call boundaries only when all
   five result registers are independent of them and the constants survive. *)
Definition live op i := Nat.ltb i (match op with Square=>5 | _=>10 end) ||
 match constant i with Some _=>true | _=>false end.
Definition frame_check k op :=
 let code:=body k op in
 forallb (Dependencies.agreement (fun _ _=>false) code (live op)) (seq 0 5) &&
 forallb (fun i=>Nat.ltb (fst i) 28) code.
Definition kernel_frame k op :=
 forall l l' r r', (forall i, live op i=true -> r i=r' i) ->
 (forall i,(i<5)%nat -> run l (body k op) r i=run l' (body k op) r' i) /\
 (forall i,(28<=i)%nat -> run l (body k op) r i=r i).
Lemma frame_ok k op : frame_check k op=true -> kernel_frame k op.
Proof.
 unfold frame_check,kernel_frame. rewrite andb_true_iff;intros [A D] l l' r r' R;split.
 - intros i I;apply (Dependencies.agreement_sound (fun _ _=>false) (body k op) (live op) l l' r r' ltac:(discriminate) R).
   apply forallb_forall with (x:=i) in A;[exact A|apply in_seq;lia].
 - intros i I;apply Dependencies.untouched,forallb_forall;intros ins Mem.
   apply forallb_forall with (x:=ins) in D;auto. apply Nat.ltb_lt in D;apply negb_true_iff,Nat.eqb_neq;lia.
Qed.
