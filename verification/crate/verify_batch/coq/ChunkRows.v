From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Return StageEntry.
Local Open Scope Z_scope.
Definition base e first:=regs e 7%nat+40*Z.of_nat first.
Definition lane first n j:=(first+Nat.min j (n-1))%nat.
Definition active n:=Z.of_nat(Nat.min n 8).
Definition length n:=if (n<?8)%nat then 90%nat else 4%nat.
Definition readable e:=fits64 (regs e 7%nat) (40*Z.of_nat(Scatter.count e)) /\
 forall x,regs e 7%nat<=x<regs e 7%nat+40*Z.of_nat(Scatter.count e) -> ~writable e x.
Definition words e first n s:=forall j k,(j<8)%nat -> 0<=k<40 ->
 mem s (regs s 3%nat+40*Z.of_nat j+k)=mem e (base e (lane first n j)+k).
Definition allowed e first n := fits64 (base e first) (40*Z.of_nat n) /\
 disjoint (Rows.frame e) 960 (base e first) (40*Z.of_nat n).
Lemma bounds e first n:readable e -> (0<n)%nat -> (first+n<=Scatter.count e)%nat -> allowed e first n.
Proof.
 intros [[L H] Sep] Live N;unfold allowed,base;split;[unfold fits64 in *;lia|unfold disjoint].
 destruct (Z_le_dec (Rows.frame e+960) (regs e 7%nat+40*Z.of_nat first));[auto|right].
 destruct (Z_le_dec (regs e 7%nat+40*Z.of_nat first+40*Z.of_nat n) (Rows.frame e));[auto|].
 exfalso;set(x:=Z.max (Rows.frame e) (regs e 7%nat+40*Z.of_nat first));apply (Sep x ltac:(unfold x;lia));left;unfold x,Rows.frame,sp,span in *;lia.
Qed.

Record selected e first n s t:Prop:=Selected {
 stack:TailWrites.caller_registers e t; left:regs t 12%nat=Z.of_nat(n-8);
 row_area:fits64 (regs t 3%nat) 320 /\ IndexStores.allowed_inputs (Rows.frame e) (regs t 3%nat);
 count_slot:read_word (mem t) (Rows.frame e+928)=active n;
 above:forall x,Rows.frame e+936<=x -> mem t x=mem s x;
 bytes:words e first n t;
 next_base:(8<=n)%nat -> regs t 3%nat=base e first
}.

Theorem choose ip text e first n s c:StageEntry.bound text -> TailWrites.bound text -> placement e ->
 readable e -> (0<n)%nat -> (first+n=Scatter.count e)%nat ->
 TailWrites.caller_registers e s -> regs s 3%nat=base e first -> regs s 12%nat=Z.of_nat n ->
 byte_memory(mem s) -> preserved (fun x=>~writable e x) (mem e) (mem s) ->
 exists t cf ws,run (length n) (ScalarBytes.fetch ip text) (State(Running(Image.offset Image.Choose)) s c)=
  Some(State(Running(Image.offset Image.Stage)) t cf,ws) /\ confined (writable e) ws /\ selected e first n s t.
Proof.
 intros Select Tail P Read N Total Frame BX Count Bytes Outside;pose proof(bounds e first n Read N ltac:(lia)) as [Fit Away].
 destruct(Read) as [_ Sep];destruct(stack_ok _ P) as [[Low High] _].
 assert (FF:fits64 (Rows.frame e) 960) by (unfold fits64,Rows.frame,sp in *;lia).
 assert (W:word(regs s 12%nat)=Z.of_nat n) by (rewrite Count;apply word_fits;pose proof(proj1(initial_cpu _ P) 6%nat);unfold Scatter.count,word64 in *;lia).
 assert (Original:forall x,base e first<=x<base e first+40*Z.of_nat n -> mem s x=mem e x) by (intros x X;apply Outside,Sep;unfold base in *;lia).
 destruct(StageEntry.choose ip text e s c Select Tail P Frame) as [[l t cf] [ws [Run [Safe [[PC St] [Full Rem]]]]]].
 cbn [loc cpu_state] in PC,St,Full,Rem;subst l;rewrite W in Run,Full.
 assert (Left:regs t 12%nat=Z.of_nat(n-8)).
 { rewrite Rem;unfold Prologue.rows_left;rewrite W;destruct(Z.ltb_spec (Z.of_nat n) 8);[lia|].
   rewrite word_fits;[lia|pose proof(proj1(initial_cpu _ P) 6%nat);unfold Scatter.count,word64 in *;lia]. }
 assert (AlignedCount: (Z.of_nat n<?8)=(n<?8)%nat) by (destruct(Z.ltb_spec (Z.of_nat n) 8), (Nat.ltb_spec n 8);auto;lia).
 rewrite AlignedCount in Run;exists t,cf,ws;split;[exact Run|split;[exact Safe|]].
 destruct (Nat.ltb_spec n 8) as [Short|Long].
 - destruct(StageEntry.pad_code _ Select) as [Start Jump];destruct(TailCopy.staged ip text (Rows.frame e) (base e first) (Z.of_nat n)
     (mem e) s c Start Jump Tail ltac:(lia) Fit FF Away (proj1 Frame) BX Count Bytes Original) as [u [cf' [writes [TailRun [Base [Data [Active HighMem]]]]]]].
   change (run 90 (ScalarBytes.fetch ip text) (State(Running 56) s c)=Some(State(Running 82) t cf,ws)) in Run.
   rewrite Run in TailRun;injection TailRun as <- <- <-;constructor;[exact St|exact Left| | |exact HighMem| |lia].
   + rewrite Base;split;[unfold fits64 in *;lia|unfold IndexStores.allowed_inputs,disjoint;lia].
   + rewrite Active;unfold active;rewrite Nat.min_l by lia;reflexivity.
   + intros j k J K;rewrite Base,Data by assumption;unfold TailCopy.source,base,lane.
     rewrite Nat2Z.inj_add,Nat2Z.inj_min,Nat2Z.inj_sub by lia;change (Z.of_nat 1) with 1;apply f_equal;ring.
 - assert (Base:regs t 3%nat=base e first) by (rewrite Full by lia;exact BX).
   destruct(StageEntry.full_active ip text s c (Rows.frame e) Select ltac:(rewrite W;lia) (proj1 Frame) FF)
      as [u [cu [w [Raw [Active HighMem]]]]].
   change (run 4 (ScalarBytes.fetch ip text) (State(Running 56) s c)=Some(State(Running 82) t cf,ws)) in Run.
   rewrite Run in Raw;injection Raw as <- <- <-.
   constructor;[exact St|exact Left| | |exact HighMem| |auto].
   + rewrite Base;split;[unfold fits64 in *;lia|unfold IndexStores.allowed_inputs,disjoint in *;lia].
   + rewrite Active;unfold active;rewrite Nat.min_r by lia;reflexivity.
   + intros j k J K;rewrite Base;unfold lane;rewrite Nat.min_l by lia;unfold base;rewrite Nat2Z.inj_add.
     pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)) as M;cbn [cpu_state] in M;rewrite M;
     rewrite (WriteTrace.frame _ _ Safe),Outside;[f_equal;ring|apply Sep;lia|apply Sep;lia].
Qed.
