From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.StoreInstructions abi.TracedCalls memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

Definition outcome := (Z*cpu*list store)%type.
Definition prepend own (result:outcome):outcome:=let '(ip,s,tail):=result in (ip,s,own++tail).
Fixpoint execute (child:Z->cpu->option outcome) slide pc code s : option outcome :=
 match code with []=>None | op::tail=>
 let next:=next_pc pc op in let '(ip,mid):=caller_step slide pc op s in let own:=caller_stores slide pc op s in
 match op with
 | Invoke _=>match child ip mid with Some(back,out,ws)=>
      if back=?word(slide+next) then option_map (prepend (own++ws)) (execute child slide next tail out)
      else None | None=>None end
 | Return=>Some(ip,mid,own)
 | _=>option_map (prepend own) (execute child slide next tail mid) end end.

Lemma checked child slide code : forall pc s ip out ws,
 complete (fun a e r f w=>child a e=Some(r,f,w)) slide pc code s ip out ws ->
 execute child slide pc code s=Some(ip,out,ws).
Proof.
 induction code as [|op tail IH];intros pc s ip out ws R;[contradiction|].
 cbn [complete] in R;cbn [execute];destruct(caller_step _ _ _ _) as [a m];destruct op;cbn zeta in R;
 try solve [destruct R as [rest [R ->]];rewrite (IH _ _ _ _ _ R);reflexivity].
 - destruct R as [back [childlog [rest [Call [R ->]]]]];rewrite Call,Z.eqb_refl,(IH _ _ _ _ _ R).
   cbn [option_map prepend];now rewrite app_assoc.
 - destruct R as [-> [-> ->]];reflexivity.
Qed.
