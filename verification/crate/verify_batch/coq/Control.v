From Coq Require Import List PeanoNat Bool Lia.
From Ed25519Simd.VerifyBatch Require Import Image.
Import ListNotations. Local Open Scope nat_scope.

Fixpoint fallthrough b listing := match listing with
 | []=>None | x::xs=>if block_beq b x then hd_error xs else fallthrough b xs end.
Definition branch b zero below := match ending b with
 | Next | Call _=>fallthrough b order
 | Jump cond _ dest=>if match cond with Equal=>zero | Unequal=>negb zero | Below=>below | Always=>true end
                    then Some dest else fallthrough b order
 | Ret=>None end.
Definition initial count := branch Entry (count=?0) false.
Record segment := Segment { lanes:nat; remaining:nat; calls:list target; resume:block }.

(* Stop when a chunk returns to Choose or reaches the epilogue. EAX from
   prepare selects the hash pipeline or the zero-mask scatter. The final
   EAX check handles the result of either scatter path. *)
Fixpoint follow fuel b count active padded ready scatter_ok trace : option segment :=
 match fuel with 0=>None | S fuel'=>
 let go next left live copied events := match next with
   | Some dst =>follow fuel' dst left live copied ready scatter_ok events | None=>None end in
 let ordinary := fun e below=>go (branch b e below) count active padded trace in
 match b with
 | Choose => ordinary false (count<?8)
 | Full => go (branch b false false) (count-8) 8 padded trace
 | Tail => go (branch b false false) 0 count 0 trace
 | Pad => go (branch b (S padded=?8) false) count active (S padded) trace
 | Prepared=>ordinary (negb ready) false
 | Continue=>ordinary (negb scatter_ok) false
 | More=>match branch b (count=?0) false with
   | Some dst=>Some(Segment active count (rev trace) dst) | None=>None end
 | Epilogue=>Some(Segment active count (rev trace) Epilogue)
 | _=> match ending b with Call callee =>
          go (branch b false false) count active padded (callee::trace)
       | _=>ordinary false false end end end.
Definition chunk_trace n ready := follow 32 Choose n 0 0 ready true [].
Definition expected (ready:bool) := if ready then [Prepare;Hash;Score] else [Prepare;Scatter].
Lemma entry_paths n : initial n=Some(if n=?0 then Empty else Prologue) /\
 branch Prologue false false=Some Choose /\ ending Empty=Ret /\ ending Epilogue=Ret.
Proof. unfold initial,branch;cbn;destruct (n=?0);repeat split;reflexivity. Qed.

Lemma chunk_trace_correct n ready : 0<n -> chunk_trace n ready=
 Some(Segment (Nat.min n 8) (n-8) (expected ready) (if n-8=?0 then Epilogue else Choose)).
Proof.
 intro N. do 8 (destruct n as [|n];[destruct ready;try reflexivity;lia|]).
 replace (Nat.min (S(S(S(S(S(S(S(S n)))))))) 8) with 8 by lia.
 unfold chunk_trace; simpl Nat.sub.
 change (S(S(S(S(S(S(S(S n))))))) <? 8) with false.
 destruct ready;cbn; destruct (n-0=?0);reflexivity.
Qed.
