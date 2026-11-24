From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.ScalarBytes execution.MappedFetch execution.LinkedRun execution.InstructionRoute
 memory.ByteMemory memory.FlatMemory memory.WriteTrace memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Rows Image Return RejectDispatch.
Import ListNotations. Local Open Scope Z_scope.

Definition status : list line := [(574,2%nat,Test32 0);(576,2%nat,Branch ScalarBytes.Equal 9)].
Definition more : list line := [(578,3%nat,Test 12);(581,6%nat,Branch ScalarBytes.Unequal (56-587))].
Definition epilogue : list line := [(587,7%nat,Add64 4 960);(594,2%nat,RestoreG 15);
 (596,2%nat,RestoreG 14);(598,2%nat,RestoreG 13);(600,2%nat,RestoreG 12);
 (602,1%nat,RestoreG 3);(603,1%nat,ScalarBytes.Ret)].
Definition bound text := linked text status /\ linked text more /\ linked text epilogue.

Lemma status_step o text s c : linked text status ->
 run 2 (ScalarBytes.fetch o text) (State (Running 574) s c)=
 Some(State (Running (if regs s 0%nat mod 2^32=?0 then 587 else 578))
       (with_zf s (regs s 0%nat mod 2^32=?0)) (Some false),[]).
Proof.
 intros Code;apply (checked _ _ _ Code);cbn [status follow loc step cpu_state cf eval_condition flag with_zf option_map].
 destruct (_=?0);reflexivity.
Qed.
Lemma more_step o text s c : linked text more ->
 run 2 (ScalarBytes.fetch o text) (State (Running 578) s c)=
 Some(State (Running (if word(regs s 12%nat)=?0 then 587 else 56))
       (with_zf s (word(regs s 12%nat)=?0)) (Some false),[]).
Proof.
 intro Code;apply (checked _ _ _ Code);cbn [more follow loc step cpu_state cf eval_condition flag with_zf option_map].
 destruct (_=?0);reflexivity.
Qed.
Lemma restore o text e s c : linked text epilogue -> placement e -> regs s 4%nat=Rows.frame e ->
 exists t,run 7 (ScalarBytes.fetch o text) (State (Running 587) s c)=Some(t,[]) /\
 loc t=Returned (word (read_word (mem s) (sp e))) /\ regs(cpu_state t) 4%nat=sp e+8 /\
 regs(cpu_state t) 0%nat=regs s 0%nat /\ mem(cpu_state t)=mem s.
Proof.
 intros Code P SP;destruct(stack_ok _ P) as [[L U] _];unfold Rows.frame in SP;fold (sp e) in SP.
 eexists;split;[apply (checked _ _ _ Code);reflexivity|].
 cbn [epilogue follow loc cpu_state cf step option_map eval_condition flag with_zf pop caller_step stack_step
   set set_regs with_words apply_stack regs mem result_regs result_mem target_ip].
 unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite SP.
 repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end.
 repeat split;try lia;replace (sp e-1000+960+8+8+8+8+8) with (sp e) by ring;reflexivity.
Qed.

Definition stopping p := (regs(machine p) 0%nat mod 2^32=?0) || (word(regs(machine p) 12%nat)=?0).
Definition leave entry text p := if stopping p
 then returning entry (length text) 11 p else segment entry text 4 p.
Definition post entry e p q := accounted e (writable e) q /\ log q=log p /\
 mem(machine q)=mem(machine p) /\ regs(machine q) 0%nat=regs(machine p) 0%nat /\
 if stopping p then ip q=read_word (mem e) (sp e) /\ regs(machine q) 4%nat=sp e+8
 else ip q=entry+offset Choose /\ regs(machine q) 4%nat=Rows.frame e.

Lemma saved_return e p : placement e -> accounted e (writable e) p ->
 word(read_word (mem(machine p)) (sp e))=read_word (mem e) (sp e).
Proof.
 intros Place [W M]. assert (Same:read_word (mem(machine p)) (sp e)=read_word (mem e) (sp e)).
 { apply preserved_read with (outside:=fun x=>~writable e x).
   - intros x X;rewrite M;apply (WriteTrace.frame _ _ W),X.
   - intros k K;change (0<=k<8) in K;intros [Stack|[Scratch|Output]];
       destruct (scratch_stack _ Place), (out_stack _ Place);unfold span in *;lia. }
 rewrite Same;apply word_fits,read_word_bound,(initial_cpu _ Place).
Qed.

Theorem next bias pc text e p : bound text -> placement e ->
 mapped (mem e) (bias+pc) text ->
 (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text)->~writable e x) ->
 RejectDispatch.continued bias pc e p ->
 exists q,leave (bias+pc) text p=Some q /\ post (bias+pc) e p q.
Proof.
 intros [Status [More End]] Place Image Apart [PC [SP [Acc Left]]].
 set (o:=bias+pc) in *. change (ip p=o+574) in PC.
 pose proof (status_step o text (machine p) (carry p) Status) as First.
 pose proof (image_after _ _ _ _ _ Acc Image Apart) as Mapped.
 set (zero:=(regs(machine p) 0%nat mod 2^32=?0)) in *.
 set (empty:=(word(regs(machine p) 12%nat)=?0)) in *.
 assert (Done:forall n s c,(n<=4)%nat -> regs s 4%nat=Rows.frame e -> regs s 0%nat=regs(machine p) 0%nat ->
    mem s=mem(machine p) ->
    run n (ScalarBytes.fetch o text) (State (Running 574) (machine p) (carry p))=Some(State (Running 587) s c,[]) ->
    exists q,returning o (length text) 11 p=Some q /\ accounted e (writable e) q /\ log q=log p /\
       mem(machine q)=mem(machine p) /\ regs(machine q) 0%nat=regs(machine p) 0%nat /\
       ip q=read_word (mem e) (sp e) /\ regs(machine q) 4%nat=sp e+8).
 { intros n s c N S A Mem Head.
   destruct (restore o text e s c End Place S) as [t [T [Ret [Stack [AX Flat]]]]].
   pose proof(run_append _ _ _ _ _ Head _ _ _ T) as Full.
   pose proof (run_lift _ _ _ _ _ _ _ Full (Forall_nil (permits (writable e))) Mapped Apart) as F.
   exists (LinkedRun.finish o p (t,[]));split.
   - unfold returning;rewrite PC;replace (o+574-o) with 574 by ring.
     rewrite (until_exact o (length text) (n+7) 11 _ _ _ _ ltac:(lia) F Ret);reflexivity.
   - split;[exact (proj2 (at_segment _ _ _ _ _ _ _ _ _ Acc PC Mapped Apart Full (Forall_nil _)))|].
     cbn [LinkedRun.finish machine ip log];rewrite app_nil_r,Flat,Mem,AX,A.
     unfold absolute;rewrite Ret,Mem,(saved_return e p Place Acc);auto. }
 unfold leave,post,stopping;fold zero empty. destruct zero eqn:Zero.
 - cbn [orb];exact (Done 2%nat (with_zf (machine p) true) (Some false) ltac:(lia) SP eq_refl eq_refl First).
 - pose proof (more_step o text (with_zf (machine p) false) (Some false) More) as Second.
   cbn [with_zf regs] in Second;fold empty in Second.
   pose proof(run_append _ _ _ _ _ First _ _ _ Second) as Both.
   destruct empty;cbn [orb].
   + exact (Done 4%nat (with_zf (with_zf (machine p) false) true) (Some false) ltac:(lia) SP eq_refl eq_refl Both).
   + destruct(at_segment _ _ _ _ _ _ 574 _ _ Acc PC Mapped Apart Both (Forall_nil _)) as [Reach Paid].
     eexists;split;[exact Reach|split;[exact Paid|]]. cbn [LinkedRun.finish log ip machine loc cpu_state with_zf regs mem absolute].
     rewrite app_nil_r;repeat split;try reflexivity;exact SP.
Qed.
