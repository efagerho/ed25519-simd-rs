From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.ScalarBytes execution.MappedFetch
 memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* A route is a certificate for the instruction fetches on one control-flow
   path. The CPU chooses the next PC, including branch, CALL and RET targets.
   A successful route may be lifted to fetch from mutable memory by run_lift. *)
Definition line := (Z*nat*instruction)%type.
Definition linked (text:list Z) (path:list line) :=
 Forall (fun '(off,n,i)=>0<=off /\ decode (skipn (Z.to_nat off) text)=Some(n,i)) path.

Fixpoint follow origin (path:list line) (s:state) : option (state*list store) :=
 match path with
 | []=>Some(s,[])
 | (off,n,i)::rest=>
    match loc s with
    | Returned _=>None
    | Running actual=>
      if off=?actual then
        match step origin off n i (cpu_state s) (cf s) with
        | Some(mid,ws)=>option_map (fun '(t,tail)=>(t,ws++tail)) (follow origin rest mid)
        | None=>None end
      else None end end.

Lemma checked origin text path : linked text path -> forall s t ws,
 follow origin path s=Some(t,ws) -> run (length path) (ScalarBytes.fetch origin text) s=Some(t,ws).
Proof.
 induction 1 as [|[[a n] i] ops [Pos Bytes] L IH];intros s t ws H;[exact H|].
 destruct s as [[off|ret] s c];cbn [follow loc cpu_state cf] in H;try discriminate.
 destruct (a=?off) eqn:E;try discriminate. apply Z.eqb_eq in E;subst off.
 destruct (step origin a n i s c) as [[u own]|] eqn:Step;try discriminate.
 destruct (follow origin ops u) as [[v tail]|] eqn:R;try discriminate.
 injection H as <- <-;cbn [length run]. unfold ScalarBytes.fetch at 1;cbn [loc cpu_state cf].
 now rewrite (proj2 (Z.ltb_ge _ _) Pos),Bytes,Step,(IH _ _ _ R).
Qed.
