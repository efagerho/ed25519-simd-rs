From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.ScalarBytes execution.WordSemantics
 memory.FlatMemory memory.ByteMemory memory.WriteTrace execution.WordBounds memory.MemoryGeometry.
From Machine Require execution.MappedFetch.
From Ed25519Simd.Zip215 Require ScatterTrace ScatterBytes.
Module S := ScatterTrace.
Local Open Scope Z_scope.

(* Separation from the output protects the actual eight bytes at RSP. The
   return target is read from those bytes even on a malformed metadata path. *)
Definition stack_position top ret t := match loc t with
 | Running _=>regs (cpu_state t) 4%nat=top /\ read_word (mem (cpu_state t)) top=ret
 | Returned ip=>ip=word ret /\ regs (cpu_state t) 4%nat=word(top+8) end.

Lemma instruction_stack o l s c t ws :
 fetch o S.code (State (Running (S.offset l)) s c)=Some(t,ws) ->
 match loc t with
 | Running _=>regs (cpu_state t) 4%nat=regs s 4%nat
 | Returned ip=>ip=word (read_word (mem s) (word (regs s 4%nat))) /\
   regs (cpu_state t) 4%nat=word(regs s 4%nat+8) end.
Proof.
 rewrite S.fetched;destruct l;
 match goal with |-context[S.fetch_at ?l] =>
   let op:=eval vm_compute in (S.fetch_at l) in change (S.fetch_at l) with op end;
 cbn [step];intro F.
 all: try match type of F with context [option_map _ ?b] =>
    destruct b as [[]|];cbn [option_map] in F;try discriminate end.
 all: injection F as <- <-;repeat split;reflexivity.
Qed.

Lemma prefixes o a n top ret : word64 n -> fits64 a n -> word64 top ->
 (forall k,0<=k<8 -> ~S.output a n (top+k)) ->
 forall s ws t,steps o S.code s ws t -> S.invariant a n s ->
 stack_position top ret s -> stack_position top ret t.
Proof.
 intros N Fits Top Apart s ws t Run;induction Run as [s|s mid t own tail F R IH];
 intros Inv Stack;[exact Stack|].
 destruct s as [[off|back] s c];[|discriminate].
 destruct Inv as [D [L [l [Off Guard]]]];cbn [loc] in Off;subst off.
 destruct(S.live_step o a n l s c N Fits D L Guard) as [u [writes [One [Safe Next]]]].
 rewrite F in One;injection One as <- <-. apply IH;[exact Next|].
 destruct Stack as [SP Word]. pose proof(instruction_stack _ _ _ _ _ _ F) as A.
 assert (Mem:mem(cpu_state mid)=WriteTrace.replay (mem s) own).
 { apply (steps_memory o S.code (State (Running (S.offset l)) s c)).
   rewrite <- (app_nil_r own) at 1;eapply advance;[exact F|constructor]. }
 destruct mid as [[loc|ip] m carry];cbn [stack_position cpu_state ScalarBytes.loc] in *.
 - split;[congruence|rewrite <- Word]. eapply preserved_read
    with (outside:=fun x=>~S.output a n x).
   + intros x X;rewrite Mem;exact (WriteTrace.frame _ _ Safe _ _ X).
   + exact Apart.
 - destruct A as [A B];rewrite SP,(word_fits _ Top),Word in A;split;congruence.
Qed.

Lemma mapped_prefix ip s c ws t a n top ret :
 ScatterBytes.symbol_bytes=S.code -> word64 n -> fits64 a n -> word64 top ->
 regs s 6%nat=a -> regs s 2%nat=n -> regs s 4%nat=top -> read_word (mem s) top=ret ->
 (forall k,0<=k<8 -> ~S.output a n (top+k)) ->
 MappedFetch.mapped (mem s) ip ScatterBytes.symbol_bytes ->
 (forall x,ip<=x<ip+Z.of_nat(length ScatterBytes.symbol_bytes) -> ~S.output a n x) ->
 MappedFetch.steps ip (length ScatterBytes.symbol_bytes) (State (Running 0) s c) ws t ->
 stack_position top ret t /\ confined (S.output a n) ws /\
 mem(cpu_state t)=WriteTrace.replay (mem s) ws /\
 match ScalarBytes.loc t with Returned _=>True | Running _=>
   exists u own,MappedFetch.fetch ip (length ScatterBytes.symbol_bytes) t=Some(u,own) end.
Proof.
 intros Image N Fits Top D L SP Word Apart Map Text Run;rewrite Image in *.
 assert (Inv:S.invariant a n (State (Running 0) s c)) by
   (split;[exact D|split;[exact L|exists S.Count;split;[reflexivity|exact I]]]).
 assert (All:forall xs u, steps ip S.code (State (Running 0) s c) xs u -> confined (S.output a n) xs).
 { intros xs u P;exact (proj1 (S.prefixes _ _ _ _ _ _ P N Fits Inv)). }
 apply (MappedFetch.same_prefixes ip S.code (State (Running 0) s c) (S.output a n) Map Text All) in Run.
 split;[eapply prefixes;[exact N|exact Fits|exact Top|exact Apart|exact Run|exact Inv|split;assumption]|].
 split;[exact (All _ _ Run)|]. pose proof (steps_memory _ _ _ _ _ Run) as Replay;split;[exact Replay|].
 pose proof (S.scatter_confined ip s c ws t) as Cert;unfold S.length64,S.destination in Cert;
 rewrite L,D in Cert;destruct (Cert N Fits Run) as [_ [_ Live]].
 destruct (ScalarBytes.loc t);[|exact I]. destruct Live as [u [own F]].
 exists u,own;unfold MappedFetch.fetch;change (mem (cpu_state t)=WriteTrace.replay (mem s) ws) in Replay;rewrite Replay.
 rewrite (MappedFetch.snapshot_mapped _ _ _ (MappedFetch.keep_image _ _ _ _ _ Map Text (All _ _ Run)));exact F.
Qed.

(* The only back edge advances R8 by one. The entry guard limits the number
   of iterations to eight even if the metadata contains arbitrary qwords. *)
Definition terminates o fuel (start:state) :=
 exists n t ws ip,(n<=fuel)%nat /\ MappedFetch.run n (fetch o S.code) start=Some(t,ws) /\ loc t=Returned ip.
Lemma more o n s t own : fetch o S.code s=Some(t,own) -> terminates o n t -> terminates o (S n) s.
Proof.
 intros F [k [last [ws [ip [K [R E]]]]]];exists (S k),last,(own++ws),ip.
 split;[lia|split;[cbn [MappedFetch.run];rewrite F,R;reflexivity|exact E]].
Qed.
Lemma longer o n m s : (n<=m)%nat -> terminates o n s -> terminates o m s.
Proof. intros N [k [t [ws [ip [H T]]]]];exists k,t,ws,ip;split;[lia|exact T]. Qed.

Local Ltac opcode l :=
 rewrite (S.fetched _ l);let decoded:=eval vm_compute in (S.fetch_at l) in
 change (S.fetch_at l) with decoded;cbn [step].
Local Ltac take l := eapply more;[opcode l;reflexivity|].
Lemma done_at o good s c : terminates o 2 (State (Running (S.offset (if good:bool then S.Success else S.Bad))) s c).
Proof.
 destruct good;[take S.Success;take S.GoodRet|take S.Bad;take S.BadRet].
 all: do 4 eexists;split;[apply Nat.le_refl|split;reflexivity].
Qed.
Lemma loop_finishes o a : forall j total s c,(j+a=total)%nat -> (total<=8)%nat ->
 regs s 8%nat=Z.of_nat j -> word (regs s 1%nat)=Z.of_nat total ->
 (0<a)%nat -> terminates o (10*a+2) (State (Running (S.offset S.Index)) s c).
Proof.
 induction a as [|a IH];intros j total s c Left Small J N Live;[lia|].
 replace (10*S a+2)%nat with (10+(10*a+2))%nat by lia.
 (* Only RCX and R8 matter for the loop count. Forget vector and memory
    expressions after each iteration instead of unfolding their payloads. *)
 take S.Index. take S.Compare.
 lazymatch goal with |-terminates _ _ (State _ ?v (Some ?guard))=>
   destruct guard eqn:B end.
 - take S.Guard. take S.Byte. take S.Mask. take S.Write. take S.Shift. take S.Increment.
   lazymatch goal with |-terminates _ _ (State _ ?v ?carry)=>set (next:=v) end.
   assert (R8:regs next 8%nat=Z.of_nat(S j)).
   { change (word (regs s 8%nat+1)=Z.of_nat(S j));rewrite J,word_fits;unfold WordBounds.word64;lia. }
   assert (RCX:word(regs next 1%nat)=Z.of_nat total) by exact N.
   clearbody next. eapply more;[opcode S.More;reflexivity|].
   rewrite R8,RCX.
   rewrite word_fits by (unfold WordBounds.word64;lia).
   destruct a as [|a].
   + assert ((Z.of_nat (S j)<?Z.of_nat total)=false) by (apply Z.ltb_ge;lia).
     rewrite H;take S.Again;apply (done_at _ true).
   + assert ((Z.of_nat (S j)<?Z.of_nat total)=true) by (apply Z.ltb_lt;lia).
     rewrite H;take S.Again;apply (IH (S j) total);[lia|exact Small|exact R8|exact RCX|lia].
 - take S.Guard;eapply longer;[|apply (done_at _ false)];lia.
Qed.
Lemma returns_by_88 o s c : terminates o 88 (State (Running 0) s c).
Proof.
 change 0 with (S.offset S.Count) at 1. take S.Count. take S.Limit.
 lazymatch goal with |-terminates _ _ (State _ ?v (Some (?size <? 8)))=>
   set (active:=size) in * end.
 assert (Guard:negb ((active=?8)||(active<?8))=(8<?active)).
 { destruct (Z.ltb_spec active 8), (Z.eqb_spec active 8), (Z.ltb_spec 8 active);
   cbn;lia || reflexivity. }
 eapply more;[opcode S.Above;cbn [eval_condition option_map flag with_zf];rewrite Guard;reflexivity|].
 destruct (Z.ltb_spec 8 active) as [Bad|Small].
 - eapply longer;[|apply (done_at _ false)];lia.
 - take S.Clear. take S.Test.
   lazymatch goal with |-terminates _ _ (State _ ?st ?cf)=>set (tested:=st) end.
   assert (N:word (regs tested 1%nat)=active) by reflexivity.
   assert (J:regs tested 8%nat=0) by reflexivity.
   assert (Zf:flag tested=Some (active=?0)) by reflexivity.
   assert (Nonneg:0<=active) by (unfold active,word;apply Z.mod_pos_bound;lia).
   clearbody tested;destruct (Z.eqb_spec active 0) as [Z|Z].
   + eapply more;[opcode S.Empty;cbn [eval_condition];rewrite Zf;reflexivity|].
     eapply longer;[|apply (done_at _ true)];lia.
   + eapply more;[opcode S.Empty;cbn [eval_condition];rewrite Zf;reflexivity|].
     eapply longer with (n:=(10*Z.to_nat active+2)%nat);[lia|].
     apply (loop_finishes o (Z.to_nat active) 0 (Z.to_nat active));[lia|lia|exact J|rewrite Z2Nat.id by lia;exact N|lia].
Qed.

Theorem mapped_termination ip s c a n : ScatterBytes.symbol_bytes=S.code ->
 word64 n -> fits64 a n -> regs s 6%nat=a -> regs s 2%nat=n ->
 MappedFetch.mapped (mem s) ip ScatterBytes.symbol_bytes ->
 (forall x,ip<=x<ip+Z.of_nat(length ScatterBytes.symbol_bytes) -> ~S.output a n x) ->
 exists k t ws back,(k<=88)%nat /\
 MappedFetch.run k (MappedFetch.fetch ip (length ScatterBytes.symbol_bytes)) (State (Running 0) s c)=Some(t,ws) /\
 MappedFetch.steps ip (length ScatterBytes.symbol_bytes) (State (Running 0) s c) ws t /\ loc t=Returned back.
Proof.
 intros Image N Fit D L Map Apart;rewrite Image in *.
 destruct (returns_by_88 ip s c) as [k [t [ws [back [K [R End]]]]]].
 assert (All:forall xs u,steps ip S.code (State (Running 0) s c) xs u -> confined (S.output a n) xs).
 { intros xs u P;pose proof (S.scatter_confined ip s c xs u) as C;unfold S.length64,S.destination in C;
   rewrite D,L in C;exact (proj1 (C N Fit P)). }
 pose proof (MappedFetch.run_steps _ _ _ _ _ _ R) as Steps.
 exists k,t,ws,back;split;[exact K|split;[exact (MappedFetch.run_lift _ _ _ _ _ _ _ R (All _ _ Steps) Map Apart)|]].
 split;[apply (MappedFetch.same_prefixes ip S.code (State (Running 0) s c) _ Map Apart All);exact Steps|exact End].
Qed.
