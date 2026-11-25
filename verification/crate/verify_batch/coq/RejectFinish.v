From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 abi.SysV execution.ScalarBytes execution.MappedFetch execution.LinkedRun execution.InstructionRoute
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
Definition callee_saved e s := forall r,In r sysv_saved -> regs s r=regs e r.

Lemma pop_value e m i r : placement e -> CallerSpills.saved e m ->
 nth_error Image.saved i=Some r -> read_word m (sp e-8*(1+Z.of_nat i))=regs e r.
Proof.
 intros P Saved N;assert (I:(i<5)%nat).
 { change (i<length Image.saved)%nat;apply (proj1(nth_error_Some _ _));congruence. }
 rewrite <- (spilled_word _ (mem e) (sp e) Image.saved i r (proj1(initial_cpu _ P)) N).
 apply preserved_read with (outside:=fun x=>sp e-40<=x<sp e);[apply Saved|intros k K;change (0<=k<8) in K;lia].
Qed.

Lemma restore o text e s c : linked text epilogue -> placement e -> regs s 4%nat=Rows.frame e -> StageEntry.saved_caller e s ->
 exists t,run 7 (ScalarBytes.fetch o text) (State (Running 587) s c)=Some(t,[]) /\
 loc t=Returned (word (read_word (mem s) (sp e))) /\ regs(cpu_state t) 4%nat=sp e+8 /\
 regs(cpu_state t) 0%nat=regs s 0%nat /\ mem(cpu_state t)=mem s /\ callee_saved e (cpu_state t).
Proof.
 intros Code P SP [Saved BP];destruct(stack_ok _ P) as [[L U] _];unfold Rows.frame in SP;fold (sp e) in SP.
 eexists;split;[apply (checked _ _ _ Code);reflexivity|].
 cbn [epilogue follow loc cpu_state cf step option_map eval_condition flag with_zf pop caller_step stack_step
   set set_regs with_words apply_stack regs mem result_regs result_mem target_ip].
 unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite SP.
 repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end.
 repeat split;try lia;try (replace (sp e-1000+960+8+8+8+8+8) with (sp e) by ring;reflexivity).
 unfold callee_saved;intros r R;cbn [sysv_saved In] in R.
 destruct R as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
 all: cbn [regs set set_regs with_words pop apply_stack stack_step caller_step result_regs result_mem target_ip mem];
   unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite ?SP;
   repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end.
 all: try exact BP.
 all: match goal with |-read_word _ ?a=regs _ ?r =>
   let i:=eval vm_compute in (match r with 3%nat=>0%nat|12%nat=>1%nat|13%nat=>2%nat|14%nat=>3%nat|_=>4%nat end) in
   replace a with (sp e-8*(1+Z.of_nat i)) by ring;exact (pop_value _ _ i r P Saved eq_refl) end.
Qed.

Definition stopping p := (regs(machine p) 0%nat mod 2^32=?0) || (word(regs(machine p) 12%nat)=?0).
Definition leave entry text p := if stopping p
 then returning entry (length text) 11 p else segment entry text 4 p.
Definition post entry e p q := accounted e (writable e) q /\ log q=log p /\
 mem(machine q)=mem(machine p) /\ regs(machine q) 0%nat=regs(machine p) 0%nat /\
 if stopping p then ip q=read_word (mem e) (sp e) /\ regs(machine q) 4%nat=sp e+8 /\ callee_saved e (machine q)
 else ip q=entry+offset Choose /\ regs(machine q) 4%nat=Rows.frame e /\
   machine q=with_zf (machine p) false /\ carry q=Some false /\ StageEntry.saved_caller e (machine q).

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

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem next bias pc text e p : bound text -> placement e ->
 mapped (mem e) (bias+pc) text ->
 (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text)->~writable e x) ->
 RejectDispatch.continued bias pc e p -> StageEntry.saved_caller e (machine p) ->
 exists q,leave (bias+pc) text p=Some q /\ post (bias+pc) e p q.
Proof.
 intros [Status [More End]] Place Image Apart [PC [SP [Acc Left]]] Saved.
 set (o:=bias+pc) in *. change (ip p=o+574) in PC.
 pose proof (status_step o text (machine p) (carry p) Status) as First.
 pose proof (image_after _ _ _ _ _ Acc Image Apart) as Mapped.
 set (zero:=(regs(machine p) 0%nat mod 2^32=?0)) in *.
 set (empty:=(word(regs(machine p) 12%nat)=?0)) in *.
 assert (Done:forall n s c,(n<=4)%nat -> regs s 4%nat=Rows.frame e -> regs s 0%nat=regs(machine p) 0%nat ->
    mem s=mem(machine p) -> StageEntry.saved_caller e s ->
    run n (ScalarBytes.fetch o text) (State (Running 574) (machine p) (carry p))=Some(State (Running 587) s c,[]) ->
    exists q,returning o (length text) 11 p=Some q /\ accounted e (writable e) q /\ log q=log p /\
       mem(machine q)=mem(machine p) /\ regs(machine q) 0%nat=regs(machine p) 0%nat /\
       ip q=read_word (mem e) (sp e) /\ regs(machine q) 4%nat=sp e+8 /\ callee_saved e (machine q)).
 { intros n s c N S A Mem Kept Head.
   destruct (restore o text e s c End Place S Kept) as [t [T [Ret [Stack [AX [Flat Regs]]]]]].
   pose proof(run_append _ _ _ _ _ Head _ _ _ T) as Full.
   pose proof (run_lift _ _ _ _ _ _ _ Full (Forall_nil (permits (writable e))) Mapped Apart) as F.
   exists (LinkedRun.finish o p (t,[]));split.
   - unfold returning;rewrite PC;replace (o+574-o) with 574 by ring.
     rewrite (until_exact o (length text) (n+7) 11 _ _ _ _ ltac:(lia) F Ret);reflexivity.
   - split;[exact (proj2 (at_segment _ _ _ _ _ _ _ _ _ Acc PC Mapped Apart Full (Forall_nil _)))|].
     cbn [LinkedRun.finish machine ip log];rewrite app_nil_r,Flat,Mem,AX,A.
     unfold absolute;rewrite Ret,Mem,(saved_return e p Place Acc);repeat apply conj;assumption || reflexivity. }
 unfold leave,post,stopping;fold zero empty. destruct zero eqn:Zero.
 - cbn [orb];exact (Done 2%nat (with_zf (machine p) true) (Some false) ltac:(lia) SP eq_refl eq_refl Saved First).
 - pose proof (more_step o text (with_zf (machine p) false) (Some false) More) as Second.
   cbn [with_zf regs] in Second;fold empty in Second.
   pose proof(run_append _ _ _ _ _ First _ _ _ Second) as Both.
   destruct empty;cbn [orb].
   + exact (Done 4%nat (with_zf (with_zf (machine p) false) true) (Some false) ltac:(lia) SP eq_refl eq_refl Saved Both).
   + destruct(at_segment _ _ _ _ _ _ 574 _ _ Acc PC Mapped Apart Both (Forall_nil _)) as [Reach Paid].
     eexists;split;[exact Reach|split;[exact Paid|]]. cbn [LinkedRun.finish log ip machine loc cpu_state with_zf regs mem absolute].
     rewrite app_nil_r;split;[reflexivity|split;[reflexivity|split;[reflexivity|split;[reflexivity|split;[exact SP|]]]]].
     split;[reflexivity|split;[reflexivity|exact Saved]].
Qed.
End Iteration.
