From Coq Require Import List Bool ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes
 execution.WordSemantics execution.WordBounds execution.MappedFetch execution.InstructionRoute
 memory.WriteTrace memory.ByteMemory abi.CallFrame.
From Machine Require execution.Cutpoint abi.StackFrame.
Import ListNotations. Local Open Scope Z_scope.

(* 0: call 6        5: ret
   6: dec ecx       8: jne 6       10: ret *)
Definition code:list Z := [0xe8;1;0;0;0;0xc3;0xff;0xc9;0x75;0xfc;0xc3].
Definition loop_body:list line := [(6,2%nat,Dec32 1);(8,2%nat,Branch Unequal (-4))].
Definition after_dec s n := with_zf (set s 1 (Z.of_nat n)) (Z.of_nat n=?0).

Lemma one_iteration n s c : regs s 1%nat=Z.of_nat (S n) -> Z.of_nat n<2^32 ->
 run 2 (ScalarBytes.fetch 0 code) (State (Running 6) s c)=
 Some(State (Running (if Nat.eqb n 0 then 10 else 6)) (after_dec s n) c,[]).
Proof.
 intros Count Fits;apply (checked 0 code loop_body ltac:(repeat constructor;discriminate || reflexivity)).
 cbn [loop_body follow step loc cf cpu_state eval_condition option_map flag with_zf].
 replace (regs s 1%nat-1) with (Z.of_nat n) by (rewrite Count;lia).
 rewrite Z.mod_small by lia;unfold after_dec;destruct n;reflexivity.
Qed.

Lemma loop n : forall s c, regs s 1%nat=Z.of_nat (S n) -> Z.of_nat n<2^32 ->
 exists t,run (2*S n) (ScalarBytes.fetch 0 code) (State (Running 6) s c)=
   Some(State (Running 10) t c,[]) /\ regs t 1%nat=0 /\ regs t 4%nat=regs s 4%nat /\ mem t=mem s.
Proof.
 induction n as [|n IH];intros s c C B;pose proof (one_iteration _ _ c C B) as R.
 - exists (after_dec s 0);split;[exact R|repeat split].
 - destruct (IH (after_dec s (S n)) c eq_refl ltac:(lia)) as [t [Rest End]].
   exists t;split;[|exact End].
   replace (2*S (S n))%nat with (2+2*S n)%nat by lia.
   exact (run_append _ _ _ _ _ R _ _ _ Rest).
Qed.

(* The first RET pops the nested link. The next fetch uses the address it
   actually popped. The second RET reads the outer caller's original word. *)
Definition execute fuel s c :=
 let next:=MappedFetch.fetch 0 (length code) in
 let segment:=Cutpoint.until fuel (Cutpoint.outside (length code)) next in
 bind (segment (State (Running 0) s c)) (fun '(mid,own) =>
 match loc mid with
 | Running _=>None
 | Returned addr=>option_map (fun '(last,tail)=>(last,own++tail))
                     (segment (State (Running addr) (cpu_state mid) (cf mid)))
 end).

Theorem countdown_returns n s c :
 regs s 1%nat=Z.of_nat (S n) -> Z.of_nat (S n)<2^32 ->
 let top:=regs s 4%nat in 32<=top -> word64 (top+8) ->
 mapped (mem s) 0 code ->
 exists t, execute (2*S n+2) s c=Some(t,[qword 0 (top-8) 5]) /\
   loc t=Returned (word(read_word (mem s) top)) /\ regs(cpu_state t) 1%nat=0 /\
   regs(cpu_state t) 4%nat=top+8 /\
   preserved (StackFrame.outside top 8) (mem s) (mem(cpu_state t)).
Proof.
 intros Count Bound top Low High Image.
 set (child:=push s 5);set (w:=qword 0 (top-8) 5).
 assert (Fit:word64(top-8)) by (unfold word64 in *;lia).
 assert (SP:regs child 4%nat=top-8) by (change (word(top-8)=top-8);now rewrite word_fits).
 assert (Enter:run 1 (ScalarBytes.fetch 0 code) (State (Running 0) s c)=Some(State (Running 6) child c,[w])).
 { change (Some(State (Running 6) child c,[qword 0 (word(top-8)) 5])=Some(State (Running 6) child c,[w])).
   now rewrite word_fits. }
 destruct (loop n child c Count ltac:(lia)) as [v [Body [Zero [Stack Memory]]]].
 assert (Link:read_word (mem v) (top-8)=5).
 { rewrite Memory,<-SP;apply pushed_return_word;unfold word64;lia. }
 set (back:=LinkedCalls.returning v).
 assert (Ret:run 1 (ScalarBytes.fetch 0 code) (State (Running 10) v c)=Some(State (Returned 5) back c,[])).
 { change (Some(State (Returned (word(read_word (mem v) (word(regs v 4%nat))))) back c,@nil store)=Some(State (Returned 5) back c,[])).
   rewrite Stack,SP,(word_fits _ Fit),Link;reflexivity. }
 pose proof (run_append _ _ _ _ _ Enter _ _ _ Body) as Called.
 pose proof (run_append _ _ _ _ _ Called _ _ _ Ret) as First.
 set (allowed:=fun x=>top-8<=x<top).
 assert (Safe:confined allowed [w]).
 { constructor;[intros x H;change (top-8<=x<top-8+8) in H;unfold allowed;lia|constructor]. }
 assert (Apart:forall x,0<=x<0+Z.of_nat(length code) -> ~allowed x).
 { change (forall x,0<=x<11 -> ~(top-8<=x<top));lia. }
 pose proof (run_lift _ _ _ _ _ _ _ First Safe Image Apart) as F.
 pose proof (Cutpoint.terminal_exact _ _ (Cutpoint.outside_terminal 0 _) (1+2*S n+1)%nat (2*S n+2)%nat _ _ _
   ltac:(lia) F eq_refl) as Seen.
 assert (NewSP:regs back 4%nat=top).
 { change (word(regs v 4%nat+8)=top);rewrite Stack,SP;replace (top-8+8) with top by ring.
   apply word_fits;unfold word64 in *;lia. }
 assert (Keep:preserved (StackFrame.outside top 8) (mem s) (mem back)).
 { change (preserved (StackFrame.outside top 8) (mem s) (mem v));rewrite Memory.
   exact (StackFrame.push_preserves s 5 top 8 eq_refl Fit ltac:(lia)). }
 pose proof (StackFrame.read_outside top 8 _ _ top 8 Keep ltac:(unfold FlatMemory.disjoint;lia)) as Outer.
 change (read_word (mem back) top=read_word (mem s) top) in Outer.
 set (last:=LinkedCalls.returning back);set (dest:=word(read_word (mem s) top)).
 assert (Out:run 1 (ScalarBytes.fetch 0 code) (State (Running 5) back c)=Some(State (Returned dest) last c,[])).
 { change (Some(State (Returned (word(read_word (mem back) (word(regs back 4%nat))))) last c,@nil store)=Some(State (Returned dest) last c,[])).
   rewrite NewSP,(word_fits top ltac:(unfold word64 in *;lia)),Outer;reflexivity. }
 assert (Code:mapped (mem back) 0 code).
 { intros i I;rewrite Keep;[exact (Image _ I)|apply Apart;lia]. }
 pose proof (run_lift _ _ allowed _ _ _ _ Out (Forall_nil _) Code Apart) as Exit.
 pose proof (Cutpoint.terminal_exact _ _ (Cutpoint.outside_terminal 0 _) 1%nat (2*S n+2)%nat _ _ _
   ltac:(lia) Exit eq_refl) as Final.
 exists (State (Returned dest) last c);split.
 - unfold execute;rewrite Seen;cbn [bind loc cpu_state cf app];rewrite Final;reflexivity.
 - split;[reflexivity|split;[exact Zero|split;[|exact Keep]]].
   change (word(regs back 4%nat+8)=top+8);now rewrite NewSP,word_fits.
Qed.
