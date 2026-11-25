From Coq Require Import List ZArith Lia.
From Machine Require Import execution.MaskTrace memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* The walk uses linked PCs and offsets relative to a representative stack
   top. Translate both into the caller's address space. Instruction operands
   and branch predicates use the same initial vectors and read-only inputs. *)
Definition origin pad:=8+16*Z.of_nat pad.
Definition render slide top pad bp input initial site:=
 let ip:=slide+instruction_pc site in let a:=top-origin pad+stack_offset site in
 match stored site with
 | IncomingBP=>qword ip a bp
 | ReturnAddress next=>qword ip a (slide+next)
 | VectorLanes gs src=>vector ip a (fun j=>value j (rev gs) (input j) (initial j) src)
 end.
Definition events {A} slide top pad bp (t:trace A) input initial:=
 map (render slide top pad bp input initial) (writes_on t input initial).
Lemma footprint {A} slide top pad bp (t:trace A) depth input initial:
 Forall (in_frame (origin pad-depth) (origin pad)) (writes_on t input initial) ->
 confined (fun x=>top-depth<=x<top) (events slide top pad bp t input initial).
Proof.
 intro H;unfold events;induction H as [|w ws [Base [Low High]] Rest IH];constructor;[|exact IH].
 intros x X;unfold touches,render in X;unfold byte_count in High;destruct(stored w);
 cbn [qword vector address size] in X;change (Z.of_nat 8) with 8 in *;change (Z.of_nat 64) with 64 in *;lia.
Qed.
Lemma run_and_stores fuel depth rows pad slide top bp start code other helper input initial:
 let t:=linked_writes fuel depth rows pad start code other helper in
 stack_writes depth pad t ->
 exists m,result (linked_tree fuel depth rows pad start code other helper) input initial=Some m /\
   result t input initial=Some m /\
   confined (fun x=>top-depth<=x<top) (events slide top pad bp t input initial).
Proof.
 cbv zeta;intro Bound;destruct(Bound input initial) as [W [m R]].
 exists m;split;[unfold linked_tree;now rewrite erase_result|split;[exact R|apply footprint,W]].
Qed.
