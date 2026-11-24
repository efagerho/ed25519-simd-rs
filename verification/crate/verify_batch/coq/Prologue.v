From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordBounds execution.WordSemantics
 execution.StoreInstructions execution.ScalarBytes memory.WriteTrace memory.MemoryGeometry.
From Machine Require execution.MappedFetch.
From Ed25519Simd.VerifyBatch Require Import Image Rows Scatter Return EntryWrites.
Import ListNotations. Local Open Scope Z_scope.

Definition saves_and_setup : list (Z*nat*ScalarBytes.instruction) :=
 [(0,3%nat,Test 6);(3,6%nat,Branch ScalarBytes.Equal (offset Empty-9));
  (9,1%nat,SaveG 3);(10,2%nat,SaveG 12);(12,2%nat,SaveG 13);
  (14,2%nat,SaveG 14);(16,2%nat,SaveG 15);(18,7%nat,Sub64 4 960);
  (25,3%nat,CopyG 3 7);(28,3%nat,CopyG 12 6);(31,3%nat,CopyG 13 6);
  (34,3%nat,CopyG 14 2);(37,3%nat,CopyG 15 1)].
Definition pointer_spills : list (Z*nat*ScalarBytes.instruction) :=
 [(40,8%nat,Store64 8 (Address 4 None 936));(48,8%nat,Store64 9 (Address 4 None 944))].
Definition listing := saves_and_setup ++ pointer_spills.
Definition bound text := Forall (fun '(a,n,i)=>decode (skipn (Z.to_nat a) text)=Some(n,i)) listing.
(* The postcondition can inspect the final state. Intermediate CPUs stay
   abstract so the proof does not repeatedly expand their stack memories. *)
Definition segment ip text e n a s c (post:state->Prop) :=
 exists t ws,MappedFetch.run n (ScalarBytes.fetch ip text) (State (Running a) s c)=Some(t,ws) /\
 confined (Return.writable e) ws /\ post t.

Lemma more ip text e n a s c b next carry own post :
 ScalarBytes.fetch ip text (State (Running a) s c)=Some(State (Running b) next carry,own) ->
 confined (Return.writable e) own -> segment ip text e n b next carry post ->
 segment ip text e (S n) a s c post.
Proof.
 intros F W [t [ws [R [S P]]]]. exists t,(own++ws);cbn [MappedFetch.run];rewrite F,R;cbn [option_map].
 split;[reflexivity|split;[apply Forall_app;auto|exact P]].
Qed.
Lemma finish ip text e a s c post : post (State (Running a) s c) ->
 segment ip text e 0 a s c post.
Proof. intro P;exists (State (Running a) s c),[];repeat split;auto;constructor. Qed.

Definition at_offset text a len op := decode (skipn (Z.to_nat a) text)=Some(len,op).
Definition frame_word e a := sp e-16384<=a /\ a+8<=sp e.

Lemma slot_word e a : placement e -> frame_word e a -> word a=a.
Proof. intros P [L H];apply word_fits;destruct(stack_ok _ P) as [[A B] _];unfold word64;lia. Qed.
Lemma slot_allowed e pc a v : frame_word e a -> confined (writable e) [qword pc a v].
Proof.
 intros [L H];apply Forall_cons;[|constructor].
 intros x X;left;change (a<=x<a+8) in X;unfold span;lia.
Qed.

Definition registers s (expected:nat->Z) := forall r,r<>4%nat -> regs s r=expected r.
Definition continuation ip text e n b d expected post := forall t c, regs t 4%nat=sp e+d -> registers t expected ->
 segment ip text e n b t c post.
Lemma push_next ip text e n a len r s c d expected post : 0<=a ->
 at_offset text a len (SaveG r) -> placement e -> regs s 4%nat=sp e+d ->
 frame_word e (sp e+d-8) ->
 registers s expected -> continuation ip text e n (a+Z.of_nat len) (d-8) expected post ->
 segment ip text e (S n) a s c post.
Proof.
 intros A D P R Slot Regs K. eapply more.
 - rewrite (fetch_at _ _ _ _ _ _ _ A D);reflexivity.
 - cbn [caller_stores];rewrite R,(slot_word _ _ P Slot);apply slot_allowed,Slot.
 - apply K.
   + change (word (regs s 4%nat-8)=sp e+(d-8)). rewrite R,(slot_word _ _ P Slot);ring.
   + intros r' Live;change (put (regs s) 4 (word(regs s 4%nat-8)) r'=expected r').
     unfold put;rewrite (proj2 (Nat.eqb_neq 4 r') ltac:(congruence));apply Regs,Live.
Qed.
Lemma move_next ip text e n a len dst src s c d expected post : 0<=a ->
 at_offset text a len (CopyG dst src) -> dst<>4%nat -> regs s 4%nat=sp e+d ->
 src<>4%nat -> registers s expected ->
 continuation ip text e n (a+Z.of_nat len) d (put expected dst (expected src)) post ->
 segment ip text e (S n) a s c post.
Proof.
 intros A D Other R Src Regs K;eapply more.
 - rewrite (fetch_at _ _ _ _ _ _ _ A D);reflexivity.
 - constructor.
 - apply K.
   + change ((if Nat.eqb dst 4 then regs s src else regs s 4%nat)=sp e+d);rewrite (proj2 (Nat.eqb_neq _ _) Other);exact R.
   + intros r Live;change (put (regs s) dst (regs s src) r=put expected dst (expected src) r).
     unfold put;destruct (Nat.eqb dst r);apply Regs;assumption.
Qed.
Lemma allocate_next ip text e n a len amount s c d expected post : 0<=a ->
 at_offset text a len (Sub64 4 amount) -> regs s 4%nat=sp e+d ->
 word64 (sp e+d) -> word64 amount -> word64 (sp e+d-amount) ->
 registers s expected -> continuation ip text e n (a+Z.of_nat len) (d-amount) expected post ->
 segment ip text e (S n) a s c post.
Proof.
 intros A D R SP Imm SP' Regs K;eapply more.
 - rewrite (fetch_at _ _ _ _ _ _ _ A D);reflexivity.
 - constructor.
 - apply K.
   + change (word (word(regs s 4%nat)-word amount)=sp e+(d-amount)).
   rewrite R,(word_fits _ SP),(word_fits _ Imm),(word_fits _ SP');ring.
   + intros r Live;change (put (regs s) 4 (word(word(regs s 4%nat)-word amount)) r=expected r).
     unfold put;rewrite (proj2 (Nat.eqb_neq 4 r) ltac:(congruence));apply Regs,Live.
Qed.
Lemma spill_next ip text e n a len r off s c d expected post : 0<=a ->
 at_offset text a len (Store64 r (Address 4 None off)) -> placement e ->
 regs s 4%nat=sp e+d -> frame_word e (sp e+d+off) ->
 registers s expected -> continuation ip text e n (a+Z.of_nat len) d expected post ->
 segment ip text e (S n) a s c post.
Proof.
 intros A D P R Slot Regs K;eapply more.
 - rewrite (fetch_at _ _ _ _ _ _ _ A D);reflexivity.
 - cbn [effective];rewrite R,Z.add_0_r,(slot_word _ _ P Slot);apply slot_allowed,Slot.
 - apply K;[exact R|exact Regs].
Qed.

Definition output_registers e s := regs s 13%nat=regs e 6%nat /\ regs s 14%nat=output e.
Definition context_registers e s := regs s 15%nat=scratch e /\ output_registers e s.
Definition bindings e s := regs s 3%nat=regs e 7%nat /\ regs s 12%nat=regs e 6%nat /\
 context_registers e s.
Definition prepared e t := loc t=Running (offset Choose) /\ regs (cpu_state t) 4%nat=Rows.frame e /\ bindings e (cpu_state t).

Lemma before_spills ip text e carry :
 Forall (fun '(a,n,i)=>at_offset text a n i) saves_and_setup ->
 placement e -> (0<count e)%nat ->
 segment ip text e 13 0 e carry (fun t=>loc t=Running 40 /\ regs (cpu_state t) 4%nat=Rows.frame e /\ bindings e (cpu_state t)).
Proof.
 intros Image P Nonempty.
 assert (NZ:(word (regs e 6%nat)=?0)=false).
 { rewrite word_fits by apply (initial_cpu _ P);apply Z.eqb_neq;unfold count in Nonempty.
   intro Z;rewrite Z in Nonempty;cbn in Nonempty;lia. }
 unfold saves_and_setup in Image. do 13 (let D:=fresh "ins" in
   apply Forall_cons_iff in Image as [D Image];cbv beta iota in D).
 eapply more;[rewrite (fetch_at ip text 0 _ _ _ _ ltac:(lia) ins);cbn [ScalarBytes.step];rewrite NZ;reflexivity|constructor|].
 eapply more;[rewrite (fetch_at ip text 3 _ _ _ _ ltac:(lia) ins0);reflexivity|constructor|].
 assert (R:regs (with_zf e false) 4%nat=sp e+0) by (unfold sp;rewrite Z.add_0_r;reflexivity).
 destruct(stack_ok _ P) as [[Lo Hi] _];unfold fits64 in *.
 assert (G:registers (with_zf e false) (regs e)) by (intros r _;reflexivity).
 Local Ltac forward rule :=
   lazymatch goal with |-segment _ _ _ _ _ ?s _ _=>
     match goal with R:regs s 4%nat=sp _+_, G:registers s _ |- _=>
       eapply rule;[lia|eassumption|..];try exact R;try exact G;try assumption;
       try solve [discriminate | unfold frame_word,word64;lia];
       intros ? ? ? ?
     end
   end.
 do 5 forward push_next. forward allocate_next. do 5 forward move_next.
 apply finish;split;[reflexivity|]. split;[unfold Rows.frame;fold (sp e);cbn [cpu_state];lia|].
 unfold bindings,context_registers,output_registers,scratch,output;cbn [cpu_state];repeat split;
 match goal with G:registers ?s ?rs |-regs ?s ?r=_=> exact (G r ltac:(discriminate)) end.
Qed.

Lemma execute ip text e carry : bound text -> placement e -> (0<count e)%nat ->
 segment ip text e 15 0 e carry (prepared e).
Proof.
 intros Image P Live. unfold bound,listing in Image;apply Forall_app in Image as [Start Stores].
 destruct (before_spills ip text e carry Start P Live) as [[l s c] [head [Run [Safe [L [R B]]]]]].
 cbn [loc cpu_state] in L,R,B;subst l. unfold pointer_spills in Stores.
 apply Forall_cons_iff in Stores as [First Stores];apply Forall_cons_iff in Stores as [Second _].
 assert (End:segment ip text e 2 40 s c (prepared e)).
 { change (regs s 4%nat=sp e+(-1000)) in R.
   assert (G:registers s (regs s)) by (intros r _;reflexivity).
   do 2 (eapply spill_next;[lia|eassumption|exact P|eassumption|unfold frame_word;lia|eassumption|intros ? ? ? ?]).
   apply finish;split;[reflexivity|];split;[cbn [cpu_state];unfold Rows.frame;fold (sp e);lia|].
   unfold bindings,context_registers,output_registers in *;destruct B as [BX [N [Scratch [Count Out]]]];cbn [cpu_state];repeat split;
   match goal with G:registers ?u (regs s) |-regs ?u ?r=_ => rewrite (G r ltac:(discriminate));assumption end. }
 destruct End as [last [tail [Remainder [Conf Done]]]].
 exists last,(head++tail);split;[exact (MappedFetch.run_append _ 13 _ _ _ Run 2 _ _ Remainder)|].
 split;[apply Forall_app;auto|exact Done].
Qed.
