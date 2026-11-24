From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.ScalarBytes execution.LinkedCalls execution.WordSemantics
 execution.WordBounds memory.WriteTrace memory.FlatMemory.
From Machine Require execution.MappedFetch.
From Ed25519Simd.VerifyBatch Require Import Image Rows Return EntryWrites Prologue.
Import ListNotations. Local Open Scope Z_scope.

(* The counter in ECX advances by 40 until eight complete descriptors have
   been written. RSI and its source bytes can take arbitrary values here. *)
Definition listing : list (Z*nat*ScalarBytes.instruction) :=
 [(0,4%nat,LoadY 0 (Address 6 None 0));(4,4%nat,Load64 0 (Address 6 None 32));
  (8,5%nat,StoreY 0 (Address 3 (Some (1%nat,1)) 0));
  (13,5%nat,Store64 0 (Address 3 (Some (1%nat,1)) 32));
  (18,4%nat,LeaG 0 (Address 6 None 40));(22,3%nat,Compare 6 7);
  (25,4%nat,MoveBelow 6 0);(29,3%nat,Add32 1 40);
  (32,6%nat,Compare32 1 320);(38,2%nat,Branch ScalarBytes.Unequal (-40))].
Definition bound text := Forall (fun '(a,n,i)=>
 ScalarBytes.decode (skipn (Z.to_nat (offset Pad+a)) text)=Some(n,i)) listing.
Definition caller_registers e s := regs s 4%nat=Rows.frame e /\ Prologue.context_registers e s.
Definition padded_registers e s := caller_registers e s /\ regs s 12%nat=0.
Definition pointers e j s := regs s 3%nat=Rows.frame e /\ regs s 1%nat=40*Z.of_nat j /\ padded_registers e s.
Definition end_of j := if Nat.eqb (S j) 8 then offset TailDone else offset Pad.
Definition state_after e j st := loc st=Running (end_of j) /\ pointers e (S j) (cpu_state st).
Definition target e j := sp e-1000+40*Z.of_nat j.

Lemma address_ok e j s k : placement e -> (j<8)%nat -> pointers e j s -> 0<=k<=32 ->
 effective s (Address 3 (Some (1%nat,1)) k)=target e j+k.
Proof.
 intros P J [B [C SP]] K. cbn [effective];rewrite B,C;unfold Rows.frame,target,sp;rewrite Z.mul_1_r.
 apply word_fits;destruct(stack_ok _ P) as [[Lo Hi] _];unfold sp,word64 in *;lia.
Qed.
Lemma row_write e j pc addr n v : (j<8)%nat ->
 target e j<=addr -> addr+Z.of_nat n<=target e j+40 ->
 confined (writable e) [WriteTrace.Store pc addr n v].
Proof.
 intros J L H;apply Forall_cons;[|constructor].
 intros x X;left;change (addr<=x<addr+Z.of_nat n) in X;unfold span,target in *;lia.
Qed.

Local Ltac one d :=
 match goal with D:ScalarBytes.decode (skipn (Z.to_nat (offset Pad+d)) ?text)=Some(?n,?op) |- _=>
  eapply Prologue.more;
  [rewrite (EntryWrites.fetch_at _ text (offset Pad+d) _ _ n op
     ltac:(change (0<=639+d);lia) D);cbn [ScalarBytes.step];reflexivity| |]
 end.
Lemma iteration ip text e j s c : bound text -> placement e -> (j<8)%nat -> pointers e j s ->
 Prologue.segment ip text e 10 (offset Pad) s c (state_after e j).
Proof.
 intros Image P J V. unfold bound,listing in Image.
 do 10 (let D:=fresh "ins" in apply Forall_cons_iff in Image as [D Image];cbv beta iota in D).
 Local Ltac forget_cpu V j :=
   lazymatch goal with |-Prologue.segment _ _ ?e _ _ ?s _ _=>
     let u:=fresh "mid" in set (u:=s);let W:=fresh "ptrs" in
     assert (W:pointers e j u) by exact V;clearbody u;clear V;rename W into V end.
 one 0;[constructor|forget_cpu V j]. one 4;[constructor|forget_cpu V j].
 one 8;[rewrite (address_ok e j _ 0 P J V ltac:(lia));apply (row_write e j);change (j<8)%nat || cbn [Z.of_nat];lia|forget_cpu V j].
 one 13;[rewrite (address_ok e j _ 32 P J V ltac:(lia));apply (row_write e j);change (j<8)%nat || cbn [Z.of_nat];lia|forget_cpu V j].
 one 18;[constructor|forget_cpu V j].
 one 22;[constructor|].
 lazymatch goal with |-Prologue.segment _ _ _ _ _ _ (Some ?b) _ => destruct b eqn:Take end.
 all: one 25;[constructor|forget_cpu V j].
 all: one 29;[constructor|].
 all: lazymatch goal with |-Prologue.segment _ _ _ _ _ ?s _ _=>
   let u:=fresh "advanced" in set (u:=s);let W:=fresh "updated" in
   assert (W:pointers e (S j) u) by
     (destruct V as [B [C SP]];split;[exact B|split;[|exact SP];unfold u;cbn [set set_regs regs with_zf put Nat.eqb];
       rewrite C;change (40 mod 2^32) with 40;rewrite (Z.mod_small (40*Z.of_nat j) (2^32)) by lia;rewrite Z.mod_small by lia;lia]);
   clearbody u;clear V;rename W into V
 end.
 all: one 32;[constructor|].
 all: destruct V as [B [C SP]];cbn [regs flag with_zf];rewrite C.
 all: rewrite !Z.mod_small by lia.
 all: eapply Prologue.more;
 [rewrite (EntryWrites.fetch_at ip text (offset Pad+38) _ _ _ _ ltac:(change (0<=677);lia) ins8);
  cbn [ScalarBytes.step eval_condition flag with_zf option_map];reflexivity|constructor|].
 all: apply Prologue.finish;unfold state_after,end_of;cbn [loc cpu_state];split;[|split;[exact B|split;assumption]].
 all: destruct (Nat.eqb_spec (S j) 8) as [E|N].
 all: first [rewrite (proj2 (Z.eqb_eq (40*Z.of_nat (S j)) 320) ltac:(lia));reflexivity|
      rewrite (proj2 (Z.eqb_neq (40*Z.of_nat (S j)) 320) ltac:(lia));reflexivity].
Qed.

Definition reached e t := loc t=Running (offset TailDone) /\ padded_registers e (cpu_state t).
Lemma remaining ip text e : bound text -> placement e -> forall fuel j s carry,
 (fuel+j=8)%nat -> pointers e j s ->
 Prologue.segment ip text e (10*fuel)
   (if Nat.eqb j 8 then offset TailDone else offset Pad) s carry (reached e).
Proof.
 intros Code Place fuel;induction fuel as [|fuel IH];intros j s carry Count Ptr.
 - assert (j=8%nat) by lia;subst;apply Prologue.finish;split;[reflexivity|exact (proj2 (proj2 Ptr))].
 - assert (J:(j<8)%nat) by lia;rewrite (proj2 (Nat.eqb_neq j 8) ltac:(lia)).
   destruct(iteration ip text e j s carry Code Place J Ptr) as [st [ws [R [Safe [End Next]]]]].
   destruct st as [l t c];cbn [loc cpu_state] in End,Next;subst l.
   destruct (IH (S j) t c ltac:(lia) Next) as [last [tail [T [W Done]]]].
   exists last,(ws++tail);split;[|split;[apply Forall_app;auto|exact Done]].
   replace (10*S fuel)%nat with (10+10*fuel)%nat by lia.
   eapply MappedFetch.run_append;[exact R|exact T].
Qed.
