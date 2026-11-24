From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.LinkedCalls execution.ScalarBytes memory.WriteTrace.
From Ed25519Simd.Zip215 Require Import ScatterTrace.
Import ListNotations. Local Open Scope Z_scope.

(* Reverse the actual JAE to JB. The indexed byte is just beyond the output.
   Both the old byte and the rejected verdict are zero. *)
Local Definition mutant := firstn 26 code ++ [0x72] ++ skipn 27 code.
Local Definition entry := CPU (fun r=>match r with 6%nat=>100 | 2%nat=>1 | _=>0 end)
  (fun _ _=>0) None (fun a=>if (a=?72)||(a=?8) then 1 else 0).
Local Definition start := State (Running 0) entry None.
Example reversed_guard : ~confined_prefix mutant.
Proof.
 intro Safe.
 pose proof (observe_steps 12 4096 mutant start) as R.
 destruct (observe 12 4096 mutant start) as [t writes] eqn:E.
 assert (N:WordBounds.word64 (length64 entry)) by (change (0<=1<2^64);lia).
 assert (P:MemoryGeometry.fits64 (destination entry) (length64 entry)) by
   (change (0<=100 /\ 100+1<=2^64);lia).
 specialize (Safe 4096 entry None writes t N P R).
 destruct Safe as [S _].
 assert (map (fun w=>(pc w,address w,size w)) writes=[(4131,101,1%nat)]).
 { change (map (fun w=>(pc w,address w,size w)) (snd(t,writes))=[(4131,101,1%nat)]).
   rewrite <-E;vm_compute;reflexivity. }
 destruct writes as [|w rest];[discriminate|]. injection H as PC A W _.
 inversion S as [|? ? Allowed _];subst. assert (X:touches w 101) by (unfold touches;rewrite A,W;lia). pose proof (Allowed 101 X) as Outside.
 change (100<=101<101) in Outside;lia.
Qed.
