From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds
 execution.StoreInstructions execution.ScalarBytes execution.MappedFetch execution.InstructionRoute memory.MemoryGeometry memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Rows Return Prologue.
Import ListNotations. Local Open Scope Z_scope.

Definition saved e m := forall x,sp e-40<=x<sp e -> m x=saved_memory e x.

Definition guard : list line := [(0,3%nat,Test 6);(3,6%nat,Branch Equal (604-9))].
Definition pushes : list line := [(9,1%nat,SaveG 3);(10,2%nat,SaveG 12);(12,2%nat,SaveG 13);
 (14,2%nat,SaveG 14);(16,2%nat,SaveG 15)].
Definition setup : list line :=
 [(18,7%nat,Sub64 4 960);(25,3%nat,CopyG 3 7);(28,3%nat,CopyG 12 6);(31,3%nat,CopyG 13 6);
  (34,3%nat,CopyG 14 2);(37,3%nat,CopyG 15 1)].
Lemma bound text : Prologue.bound text -> linked text guard /\ linked text pushes /\
 linked text setup /\ linked text pointer_spills.
Proof.
 intros L;unfold Prologue.bound,Prologue.listing,saves_and_setup,pointer_spills in L;cbn [app] in L.
 do 15 (let D:=fresh in apply Forall_cons_iff in L as [D L];cbv beta iota in D).
 repeat constructor;try discriminate;assumption.
Qed.
Lemma guarded ip text e c : linked text guard -> placement e -> (0<Scatter.count e)%nat ->
 run 2 (ScalarBytes.fetch ip text) (State (Running 0) e c)=Some(State (Running 9) (with_zf e false) (Some false),[]).
Proof.
 intros Guard Place Live;apply (checked _ _ _ Guard);cbn [guard follow loc cpu_state cf step eval_condition flag with_zf option_map].
 assert (N:(word (regs e 6%nat)=?0)=false) by
   (apply Z.eqb_neq;rewrite word_fits by apply (initial_cpu _ Place);unfold Scatter.count in Live;lia).
 rewrite N;reflexivity.
Qed.
Definition push_len (r:nat) := if (r<?8)%nat then 1%nat else 2%nat.
Fixpoint push_list off rs : list line := match rs with []=>[] | r::tail=>
 (off,push_len r,SaveG r)::push_list (off+Z.of_nat(push_len r)) tail end.
Fixpoint after_pushes off rs := match rs with []=>off | r::tail=>
 after_pushes (off+Z.of_nat(push_len r)) tail end.
Lemma pushes_spill ip text g rs : forall off top s c,
 linked text (push_list off rs) -> Forall (fun r=>r<>4%nat) rs ->
 8*Z.of_nat(length rs)<=top<2^64 -> regs s 4%nat=top -> (forall r,r<>4%nat -> regs s r=g r) ->
 exists t ws,run (length rs) (ScalarBytes.fetch ip text) (State (Running off) s c)=
 Some(State (Running (after_pushes off rs)) t c,ws) /\ mem t=spill g (mem s) top rs /\ regs t 4%nat=top-8*Z.of_nat(length rs) /\
 (forall r,r<>4%nat -> regs t r=g r).
Proof.
 induction rs as [|r rs IH];intros off top s c Code NotSP Space SP G.
 - do 2 eexists;split;[reflexivity|split;[reflexivity|split;[cbn;lia|exact G]]].
 - apply Forall_cons_iff in Code as [[Pos Bytes] Code];apply Forall_cons_iff in NotSP as [Other Tail].
   cbn [length] in Space;rewrite Nat2Z.inj_succ in Space.
   assert (Slot:word(top-8)=top-8) by (apply word_fits;unfold word64;lia).
   set (mid:=push s (regs s r)).
   assert (Stack:regs mid 4%nat=top-8) by (change (word(regs s 4%nat-8)=top-8);now rewrite SP).
   assert (Regs:forall i,i<>4%nat -> regs mid i=g i).
   { intros i I;change (put (regs s) 4 (word(regs s 4%nat-8)) i=g i).
     unfold put;rewrite (proj2(Nat.eqb_neq 4 i) ltac:(congruence));apply G,I. }
   destruct (IH (off+Z.of_nat(push_len r)) (top-8) mid c Code Tail ltac:(lia) Stack Regs)
      as [t [w [Run [M [End OtherRegs]]]]].
   exists t,(caller_stores ip off (Save r) s++w);split.
   + cbn [length run];rewrite (EntryWrites.fetch_at ip text off s c (push_len r) _ Pos Bytes);cbn [step].
     change (snd (caller_step ip off (Save r) s)) with mid;rewrite Run;reflexivity.
   + split.
     * rewrite M;cbn [spill];change (spill g (store_word (mem s) (word(regs s 4%nat-8)) (regs s r)) (top-8) rs=
         spill g (store_word (mem s) (top-8) (g r)) (top-8) rs);now rewrite SP,Slot,G by exact Other.
     * split;[cbn [length];rewrite Nat2Z.inj_succ;lia|exact OtherRegs].
Qed.
Lemma saved_five ip text e : linked text pushes -> placement e ->
 exists s ws,run 5 (ScalarBytes.fetch ip text) (State (Running 9) (with_zf e false) (Some false))=
 Some(State (Running 18) s (Some false),ws) /\ mem s=saved_memory e /\ regs s 4%nat=sp e-40 /\ (forall r,r<>4%nat -> regs s r=regs e r).
Proof.
 intros Code P;destruct(stack_ok _ P) as [[L H] _].
 exact (pushes_spill ip text (regs e) Image.saved 9 (sp e) (with_zf e false) (Some false)
   Code ltac:(repeat constructor;discriminate) ltac:(change (40<=sp e<2^64);lia)
   eq_refl ltac:(intros;reflexivity)).
Qed.
Lemma private_setup ip text e s c : linked text setup -> placement e -> regs s 4%nat=sp e-40 ->
 exists t cf,run 6 (ScalarBytes.fetch ip text) (State (Running 18) s c)=Some(State (Running 40) t cf,[]) /\
 regs t 4%nat=Rows.frame e /\ mem t=mem s /\ regs t 8%nat=regs s 8%nat /\ regs t 9%nat=regs s 9%nat.
Proof.
 intros Code P SP;do 2 eexists;split;[apply (checked _ _ _ Code);reflexivity|].
 destruct(stack_ok _ P) as [[L H] _];cbn [setup follow step option_map loc cf cpu_state regs mem set set_regs with_zf put Nat.eqb].
 rewrite SP;unfold Rows.frame;fold (sp e);rewrite (word_fits (sp e-40)) by (unfold word64;lia).
 change (word 960) with 960;rewrite word_fits by (unfold word64;lia);repeat split;lia.
Qed.
Lemma spilled ip text e s c : linked text pointer_spills -> placement e -> regs s 4%nat=Rows.frame e ->
 exists t ws,run 2 (ScalarBytes.fetch ip text) (State (Running 40) s c)=Some(State (Running 56) t c,ws) /\
 (forall x,sp e-40<=x<sp e -> mem t x=mem s x) /\
 read_word (mem t) (Rows.frame e+936)=word(regs s 8%nat) /\ read_word (mem t) (Rows.frame e+944)=word(regs s 9%nat).
Proof.
 intros Code P SP;do 2 eexists;split;[apply (checked _ _ _ Code);reflexivity|].
 destruct(stack_ok _ P) as [[L H] _].
 cbn [pointer_spills follow step option_map loc cf cpu_state regs mem effective with_words commit qword address size payload].
 rewrite SP,Z.add_0_r;unfold Rows.frame;fold (sp e);
 repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end.
 unfold commit;cbn [qword address size payload];split.
 - intros x X;rewrite !FlatMemory.write_outside by lia;reflexivity.
 - split;apply read_word_encoded;intros k K.
   + rewrite FlatMemory.write_outside by lia;apply FlatMemory.write_at,K.
   + apply FlatMemory.write_at,K.
Qed.
Definition table_arguments e m:=read_word m (Rows.frame e+936)=regs e 8%nat /\ read_word m (Rows.frame e+944)=regs e 9%nat.
Lemma keep_tables e m m' : (forall x,Rows.frame e+936<=x<Rows.frame e+952 -> m' x=m x) ->
 table_arguments e m -> table_arguments e m'.
Proof.
 intros Same [Id Base];split;[rewrite <-Id|rewrite <-Base];
 apply preserved_read with (outside:=fun x=>Rows.frame e+936<=x<Rows.frame e+952);
 [exact Same|intros k K;change (0<=k<8) in K;lia|exact Same|intros k K;change (0<=k<8) in K;lia].
Qed.
Lemma from_entry ip text e c t ws : Prologue.bound text -> placement e -> (0<Scatter.count e)%nat ->
 run 15 (ScalarBytes.fetch ip text) (State (Running 0) e c)=Some(t,ws) -> saved e (mem(cpu_state t)) /\ table_arguments e (mem(cpu_state t)).
Proof.
 intros Code P N Run;destruct(bound _ Code) as [G [S [A B]]].
 pose proof(guarded ip text e c G P N) as Start.
 destruct(saved_five ip text e S P) as [u [pushes [Push [Slots [SP GP]]]]].
 destruct(private_setup ip text e u (Some false) A P SP) as [v [cf [Args [Top [M [IdReg BaseReg]]]]]].
 destruct(spilled ip text e v cf B P Top) as [w [tail [Store [End [Id Base]]]]].
 pose proof(run_append _ _ _ _ _ (run_append _ _ _ _ _ (run_append _ _ _ _ _ Start _ _ _ Push) _ _ _ Args) _ _ _ Store) as Full.
 change (run 15 (ScalarBytes.fetch ip text) (State (Running 0) e c)=Some(State (Running 56) w cf,(([]++pushes)++[])++tail)) in Full.
 rewrite Run in Full;injection Full as -> _;cbn [cpu_state];split.
 - intros x X;now rewrite End,M,Slots by exact X.
 - unfold table_arguments;rewrite Id,Base,IdReg,BaseReg,!GP by discriminate;now rewrite !word_fits by apply (initial_cpu _ P).
Qed.
