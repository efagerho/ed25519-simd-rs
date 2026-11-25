From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.StoreInstructions execution.WordSemantics abi.TracedCalls memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

Lemma project (call view:Z->cpu->Z->cpu->Prop) :
 (forall a s r f,call a s r f -> view a s r f) ->
 forall slide code pc s r f,runs call slide pc code s r f -> runs view slide pc code s r f.
Proof.
 intros Sub slide code;induction code as [|op tail IH];intros pc s r f R;[exact R|].
 cbn [runs] in *;destruct(caller_step _ _ _ _) as [a e];destruct op;try (apply IH;exact R);try exact R.
 destruct R as [mid [C R]];exists mid;split;[apply Sub,C|apply IH,R].
Qed.

Definition no_push op := match op with Save _=>false|_=>true end.
(* Ordinary pushes belong to the caller's prologue. Within the remaining
   code every write is a CALL push or an ordered store issued by a child. *)
Section History.
Variables (entry:Z->cpu->Z->cpu->Prop) (child:completed_call) (region:Z->Prop) (loaded:(Z->Z)->Prop).
Hypothesis keep:forall m ws,loaded m -> confined region ws -> loaded (replay m ws).
Hypothesis slot:forall a s r f,entry a s r f -> forall x,regs s 4%nat<=x<regs s 4%nat+8 -> region x.
Hypothesis invoke:forall a s r f,entry a s r f -> loaded (mem s) -> exists ws, child a s r f ws /\
 confined region ws /\ mem f=replay (mem s) ws.

Lemma collect slide code : forall pc s r f,forallb no_push code=true -> loaded(mem s) ->
 runs entry slide pc code s r f ->
 exists ws,complete child slide pc code s r f ws /\ confined region ws /\ mem f=replay (mem s) ws.
Proof.
 induction code as [|op tail IH];intros pc s r f Free Image Run;[contradiction|].
 cbn [forallb] in Free;apply Bool.andb_true_iff in Free as [Op Tail].
 cbn [runs] in Run;cbn [complete];pose proof(caller_store_memory slide pc op s) as Bytes.
 destruct op;try discriminate.
 all: try solve [cbn [caller_stores] in Bytes;destruct(caller_step _ _ _ _) as [ip u];cbn [snd replay] in Bytes;
  destruct(IH _ _ _ _ Tail ltac:(now rewrite Bytes) Run) as [ws [R [Safe M]]];
  exists ws;split;[exists ws;split;[exact R|reflexivity]|split;[exact Safe|now rewrite M,Bytes]]].
 - remember (caller_step slide pc (Invoke target) s) as step eqn:E;destruct step as [ip u].
   destruct Run as [back [C Rest]];cbn [snd] in Bytes.
   assert (SP:regs u 4%nat=word(regs s 4%nat-8)).
   { change (regs (snd(ip,u)) 4%nat=word(regs s 4%nat-8));rewrite E;reflexivity. }
   assert (Push:confined region (caller_stores slide pc (Invoke target) s)).
   { apply call_push_confined;rewrite <-SP;apply (slot _ _ _ _ C). }
   destruct(invoke _ _ _ _ C ltac:(rewrite Bytes;apply keep;assumption)) as [own [Ret [Safe M]]].
   assert (Next:loaded(mem back)) by (rewrite M;apply keep;[rewrite Bytes;apply keep;assumption|exact Safe]).
   destruct(IH _ _ _ _ Tail Next Rest) as [ws [R [S Final]]].
   exists (caller_stores slide pc (Invoke target) s++own++ws);split.
   + exists back,own,ws;auto.
   + split;[apply Forall_app;split;[exact Push|now apply Forall_app]|now rewrite !replay_app,<-Bytes,<-M].
 - destruct(caller_step slide pc Return s) as [ip u];exists [];destruct Run as [-> ->];repeat split;try constructor;exact Bytes.
Qed.
End History.
