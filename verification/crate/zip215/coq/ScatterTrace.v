From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics
 execution.ScalarBytes execution.StoreInstructions execution.WordBounds memory.MemoryGeometry
 memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.Zip215 Require Caller.
Import ListNotations. Local Open Scope Z_scope.

Definition code := Eval vm_compute in Caller.image (fun _=>0) Caller.Scatter.
Inductive label := Count | Limit | Above | Clear | Test | Empty | Index | Compare |
 Guard | Byte | Mask | Write | Shift | Increment | More | Again | Success | GoodRet | Bad | BadRet.
Definition offset l := match l with
 | Count=>0 | Limit=>4 | Above=>8 | Clear=>10 | Test=>13 | Empty=>16
 | Index=>18 | Compare=>23 | Guard=>26 | Byte=>28 | Mask=>32 | Write=>35
 | Shift=>39 | Increment=>41 | More=>44 | Again=>47 | Success=>49
 | GoodRet=>54 | Bad=>55 | BadRet=>57 end.

Definition fetch_at l := decode (skipn (Z.to_nat (offset l)) code).
Lemma fetched o l s c : fetch o code (State (Running (offset l)) s c) =
 match fetch_at l with Some (n,i)=>step o (offset l) n i s c | None=>None end.
Proof. destruct l;reflexivity. Qed.

Definition destination s := regs s 6%nat.
Definition length64 s := regs s 2%nat.
Definition index s := regs s 9%nat.
Definition ok_at l s c n := match l with
 | Guard=>c=Some (word (index s) <? n)
 | Byte | Mask | Write=>word (index s)<n
 | Above=>exists z cf,flag s=Some z /\ c=Some cf
 | Empty=>exists z,flag s=Some z
 | Again=>exists cf,c=Some cf
 | _=>True end.
Definition invariant a n st :=
 destination (cpu_state st)=a /\ length64 (cpu_state st)=n /\
 match loc st with Returned _=>True | Running off=>
 exists l,off=offset l /\ ok_at l (cpu_state st) (cf st) n end.

Lemma octet_allowed o s a n : fits64 a n -> destination s=a ->
 word(index s)<n ->
 permits (fun x=>a<=x<a+n) (byte_store o (IndexedByte 10 6 9) s).
Proof.
 intros [A N] Base B. unfold permits,touches,byte_store;cbn [address size base StoreInstructions.index].
 change (regs s 6%nat=a) in Base;rewrite Base. fold (index s).
 assert (E:word(a+index s)=a+word(index s)).
 { unfold word. rewrite <-Z.add_mod_idemp_r by lia.
   apply Z.mod_small. pose proof (Z.mod_pos_bound (index s) (2^64) ltac:(lia));unfold word in B;lia. }
 rewrite E. assert (W:0<=word(index s)) by (apply Z.mod_pos_bound;lia).
 change (forall x, a+word(index s)<=x<a+word(index s)+1 -> a<=x<a+n);lia.
Qed.

Definition output a n x := a<=x<a+n.
Definition confined_prefix text := forall o s carry ws last,
 word64 (length64 s) -> fits64 (destination s) (length64 s) ->
 steps o text (State (Running 0) s carry) ws last ->
 confined (output (destination s) (length64 s)) ws /\
 (forall x,~output (destination s) (length64 s) x -> mem(cpu_state last) x=mem s x) /\
 match loc last with Running _=>exists next writes,fetch o text last=Some(next,writes)
                    | Returned _=>True end.

Local Ltac successor_at :=
 let rec choose xs := lazymatch xs with
 | ?l::?t => first [exists l;split;[reflexivity|] | choose t]
 end in choose constr:([Count;Limit;Above;Clear;Test;Empty;Index;Compare;Guard;Byte;
                        Mask;Write;Shift;Increment;More;Again;Success;GoodRet;Bad;BadRet]).
Lemma live_step o a n l s c : word64 n -> fits64 a n ->
 destination s=a -> length64 s=n -> ok_at l s c n ->
 exists t ws,fetch o code (State (Running (offset l)) s c)=Some(t,ws) /\
 confined (output a n) ws /\ invariant a n t.
Proof.
 intros N Fits D L Guarded. rewrite fetched. destruct l;
 match goal with |- context [fetch_at ?l] =>
   let op:=eval vm_compute in (fetch_at l) in change (fetch_at l) with op end;
 cbn [step offset eval_condition ok_at] in *.
 all: try match type of Guarded with
 | exists _ _, _ => destruct Guarded as [z [b [-> ->]]];destruct z,b
 | exists _, _ => destruct Guarded as [b ->];destruct b
 | ?carry=Some _ => rewrite Guarded;destruct (word (index s) <? n) eqn:Cmp
 end.
 all: do 2 eexists;split;[reflexivity|].
 all: split;[first [constructor;[apply octet_allowed;eassumption|constructor]|constructor]|].
 all: unfold invariant;cbn [cpu_state loc].
 all: split;[exact D|split;[exact L|]].
 all: try exact I;successor_at;cbn [ok_at].
 all: try exact I;try exact Guarded;try solve [do 2 eexists;split;reflexivity|eexists;reflexivity].
 - change (Some (word (index s) <? word (length64 s))=Some (word (index s) <? n)).
   rewrite L,(word_fits n N);reflexivity.
 - apply Z.ltb_lt,Cmp.
Qed.

Lemma prefixes o a n s ws t : steps o code s ws t ->
 word64 n -> fits64 a n -> invariant a n s ->
 confined (output a n) ws /\ invariant a n t.
Proof.
 induction 1 as [|s mid t own tail F R IH];intros N A I;[split;[constructor|exact I]|].
 destruct s as [[off|ip] s c];[|discriminate].
 destruct I as [D [L [l [E G]]]]. cbn [loc] in E;subst off.
 destruct (live_step o a n l s c N A D L G) as [v [events [Step [Safe Inv]]]].
 rewrite Step in F;injection F as <- <-. destruct (IH N A Inv) as [Tail Last].
 split;[apply Forall_app;auto|exact Last].
Qed.

Theorem scatter_confined : confined_prefix code.
Proof.
 intros o s c ws t N A R.
 assert (I:invariant (destination s) (length64 s) (State (Running 0) s c))
 by (split;[reflexivity|split;[reflexivity|exists Count;split;[reflexivity|exact I]]]).
 destruct (prefixes _ _ _ _ _ _ R N A I) as [W T].
 split;[exact W|split].
 - rewrite (steps_memory _ _ _ _ _ R);apply WriteTrace.frame,W.
 - destruct t as [[off|ip] f carry];[|exact Logic.I].
   destruct T as [D [L [l [E G]]]]. cbn [loc] in E;subst off.
   destruct (live_step o _ _ l f carry N A D L G) as [v [writes [S _]]];exists v,writes;exact S.
Qed.
