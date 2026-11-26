From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls
 execution.LinkedRun execution.ScalarBytes execution.InstructionRoute execution.CursorSegment execution.MappedFetch abi.RegisterSpill memory.ByteMemory memory.FlatMemory abi.SysV.
From Ed25519Simd.KeyTable Require Frame.
Import ListNotations. Local Open Scope Z_scope.

Definition path:list line:=[(1947,4%nat,Compare32 15 8);(1951,2%nat,Branch Equal (1982-1953));
 (1982,4%nat,LeaG 4 (Address 5 None (-40)));(1986,2%nat,RestoreG 15);(1988,2%nat,RestoreG 14);
 (1990,2%nat,RestoreG 13);(1992,2%nat,RestoreG 12);(1994,1%nat,RestoreG 3);(1995,1%nat,RestoreG 5);
 (1996,3%nat,ZeroUpper);(1999,1%nat,Ret)].
Definition execute base text:=segment base text 11.

Lemma raw text o s c t rs back : linked text path -> regs s 15%nat=8 -> regs s 5%nat=t-8 -> 48<=t -> t+8<=2^64 ->
 (forall i r,nth_error Frame.saved_regs i=Some r -> read_word (mem s) (t-8*(1+Z.of_nat i))=rs r) ->
 word64 back -> read_word (mem s) t=back ->
 exists last,MappedFetch.run 11 (ScalarBytes.fetch o text) (State(Running 1947) s c)=Some(last,[]) /\
 loc last=Returned back /\ regs(cpu_state last) 4%nat=word(t+8) /\ mem(cpu_state last)=mem s /\
 forall r,In r sysv_saved -> regs(cpu_state last) r=rs r.
Proof.
 intros Linked Last BP Low High Slots Back Link;eexists;split.
 - apply (InstructionRoute.checked _ _ _ Linked);cbn [path follow loc cpu_state cf step eval_condition flag with_zf option_map];rewrite Last;reflexivity.
 - cbn [path follow loc cpu_state cf step eval_condition flag with_zf option_map];rewrite ?Last;
   cbn [loc cpu_state pop caller_step stack_step target_ip result_regs result_mem apply_stack advance_rsp stack_top
    effective set set_regs with_words with_zf regs mem put Nat.eqb].
   unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite BP.
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64;lia)) end.
   repeat split;try lia.
   + match goal with |-Returned(word(read_word _ ?a))=_=>replace a with t by ring end;now rewrite Link,word_fits.
   + f_equal;ring.
   + intros r K;destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
     all: match goal with |- read_word _ ?a = ?f ?r =>
       let i:=(eval compute in (match r with 5%nat=>0%nat|3%nat=>1%nat|12%nat=>2%nat|13%nat=>3%nat|14%nat=>4%nat|_=>5%nat end)) in
       rewrite <-(Slots i r eq_refl);f_equal;ring end.
Qed.

Theorem checked root allowed base text sp pt dst entry last :
 linked text path -> available root allowed base text -> CursorSegment.valid_cursor root allowed last ->
 ip last=base+1947 -> regs(machine last) 15%nat=8 -> regs(machine last) 5%nat=sp-8 ->
 48<=sp -> sp+8<=2^64 -> well_formed(machine entry) ->
 (forall x,sp-48<=x<sp+8 -> Frame.keep sp pt dst x) ->
 preserved (Frame.keep sp pt dst) (Frame.saved sp entry) (mem(machine last)) ->
 exists q,execute base text last=Some q /\ ip q=read_word (mem(machine entry)) sp /\
 CursorSegment.valid_cursor root allowed q /\ regs(machine q) 4%nat=word(sp+8) /\
 (forall r,In r sysv_saved -> regs(machine q) r=regs(machine entry) r) /\ mem(machine q)=mem(machine last).
Proof.
 intros Return Image State PC Digit BP Low High W Slots Kept.
 set (back:=read_word (mem(machine entry)) sp).
 assert (LinkFit:word64 back) by (apply read_word_bound;exact (proj2(proj2 W))).
 assert (Slot:forall i r,nth_error Frame.saved_regs i=Some r ->
    read_word (mem(machine last)) (sp-8*(1+Z.of_nat i))=regs(machine entry) r).
 { intros i r I;assert ((i<6)%nat) by (change 6%nat with (length Frame.saved_regs);apply nth_error_Some;rewrite I;discriminate).
   rewrite <-(spilled_word _ (mem(machine entry)) sp _ _ _ (proj1 W) I).
   apply preserved_read with (outside:=Frame.keep sp pt dst);[exact Kept|].
   intros b B;change (0<=b<8) in B;apply Slots;lia. }
 assert (Link:read_word (mem(machine last)) sp=back).
 { unfold back;transitivity (read_word (Frame.saved sp entry) sp).
   - apply preserved_read with (outside:=Frame.keep sp pt dst);[exact Kept|intros b B;change (0<=b<8) in B;apply Slots;lia].
   - apply preserved_read with (outside:=fun x=>sp<=x);[intros x X;apply outside_spill;now right|intros b B;change (0<=b<8) in B;lia]. }
 destruct(raw text base (machine last) (carry last) sp (regs(machine entry)) back Return Digit BP
   Low High Slot LinkFit Link) as [t [Run [Exit [Top [Mem Regs]]]]].
 destruct(CursorSegment.checked root allowed allowed base text 11 last 1947 _ _ Image (fun _ X=>X)
   State PC Run (Forall_nil _)) as [Step [Valid _]].
 eexists;split;[exact Step|]. split;[cbn [finish ip];unfold absolute;now rewrite Exit|].
 exact (conj Valid (conj Top (conj Regs Mem))).
Qed.
