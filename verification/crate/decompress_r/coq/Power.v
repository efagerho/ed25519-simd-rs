From Coq Require Import List ZArith Bool Lia.
From ProofArithmetic Require Export AdditionChain.
From Machine Require Import isa.Instructions.
From Curve25519 Require Import Field Radix51.
From Curve25519.group Require Decompression.
From Ed25519Simd.Decode Require Import Kernels.
Import ListNotations. Local Open Scope Z_scope.

Definition field := nat -> Z.
Definition feed (x y:field) i := match constant i with Some n=>n | None=>
 if Nat.ltb i 5 then x i else if Nat.ltb i 10 then y (i-5)%nat else 0 end.
Definition apply_kernel k op x y := run (fun _ _=>0) (body k op) (feed x y).
Definition accepts op := match op with Square=>squared | _=>split_field end.
Lemma apply_ok k op x y : verified k op=true -> accepts op x -> accepts op y ->
 let out:=apply_kernel k op x y in
 field_bound (out_bound op) out /\
 represents (limbs out) (limbs x * limbs (match op with Square=>x | _=>y end)) /\
 (op=Multiply -> 2<=out 0%nat).
Proof.
 intros V X Y. assert (Init : input op (feed x y)); [|pose proof (verified_result _ _ V _ (fun _ _=>0) Init) as H; destruct op; exact H].
 intro i. unfold feed. destruct (constant i); [reflexivity|].
 unfold in_bound. destruct (Nat.ltb_spec i 5) as [L|L], (Nat.ltb_spec i 10) as [U|U]; try lia.
 - destruct op; exact (X i L).
 - destruct op; specialize (Y (i-5)%nat ltac:(lia)); try exact Y.
   unfold square_bound in *. replace (i mod 5)%nat with ((i-5) mod 5)%nat by (replace i with ((i-5)+1*5)%nat at 2 by lia; rewrite PeanoNat.Nat.Div0.mod_add; reflexivity). exact Y.
Qed.

Definition chain := [
 Product Root;Save A;Squares 2;Product Root;Save B;Product A;Squares 1;Product B;
 Save A;Squares 5;Product A;Save A;Squares 10;Product A;Save B;Squares 20;Product B;
 Squares 10;Product A;Save A;Squares 50;Product A;Save B;Squares 100;Product B;
 Squares 50;Product A;Squares 2;Product Root].
(* Uninitialized stack slots have no exponent. A use before a save is rejected.
   A square additionally requires that a previous kernel tightened the limbs. *)
Definition meta := option (bool*Z).
Definition start : meta := Some (false,1).
Definition times (x y:meta) : meta := match x,y with
 | Some (_,a),Some (_,b)=>Some (true,a+b) | _,_=>None end.
Definition twice (x:meta) : meta := match x with Some(true,a)=>Some(true,a+a) | _=>None end.
Definition related root (x:field) (m:meta) := match m with None=>True | Some(tight,e)=>
 0<=e /\ (if tight then squared x else split_field x) /\ represents (limbs x) (root^e) end.
Definition single k root := current(evaluate (apply_kernel k ChainMultiply)
 (fun x=>apply_kernel k Square x x) root (fun _=>0) chain).
Local Lemma counted : current(evaluate times twice start None chain)=Some(true,Decompression.exponent).
Proof. vm_compute; reflexivity. Qed.
Theorem chain_power k root ops e :
 current(evaluate times twice start None ops)=Some(true,e) -> verified k ChainMultiply=true -> verified k Square=true ->
 split_field root -> let out:=current(evaluate (apply_kernel k ChainMultiply)
   (fun x=>apply_kernel k Square x x) root (fun _=>0) ops) in
 squared out /\ represents (limbs out) (limbs root ^ e).
Proof.
 intros Count M S R. set (rel:=related (limbs root)).
 assert (Mul : forall a b x y, rel x a -> rel y b -> rel (apply_kernel k ChainMultiply x y) (times a b)).
 { intros [[t n]|] [[u m]|] x y; try exact (fun _ _=>I). intros [N [X Ex]] [P [Y Ey]].
   assert (B:split_field x) by (destruct t;auto using squared_split).
   assert (D:split_field y) by (destruct u;auto using squared_split).
   destruct (apply_ok _ _ _ _ M B D) as [O [E _]].
   split; [lia|]. split; [exact O|]. rewrite Z.pow_add_r by lia. eapply ctrans; eauto using ctimes. }
 assert (Sq : forall a x, rel x a -> rel (apply_kernel k Square x x) (twice a)).
 { intros [[[|] n]|] x; try exact (fun _=>I). intros [N [X Ex]].
   destruct (apply_ok _ _ _ _ S X X) as [O [E _]]. split;[lia|]. split;[exact O|].
   rewrite Z.pow_add_r by lia. eapply ctrans; eauto using ctimes. }
 assert (RootOK:rel root start).
 { split; [lia|]. split;[exact R|]. rewrite Z.pow_1_r. apply crefl. }
 pose proof (evaluate_sound rel _ _ _ _ Mul Sq ops _ _ (fun _=>0) None RootOK I) as H.
 rewrite Count in H.
 exact (proj2 H).
Qed.

Theorem single_power k root : verified k ChainMultiply=true -> verified k Square=true ->
 split_field root -> squared (single k root) /\
 represents (limbs(single k root)) (limbs root ^ Decompression.exponent).
Proof. apply chain_power, counted. Qed.
