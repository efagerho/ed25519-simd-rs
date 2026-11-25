From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch execution.ScalarWords execution.InstructionRoute memory.WriteTrace memory.ByteMemory memory.FlatMemory abi.SysV.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableContents TableParentFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition path:list line:=[(1947,4%nat,Compare32 15 8);(1951,2%nat,Branch Equal (1982-1953));
 (1982,4%nat,LeaG 4 (Address 5 None (-40)));(1986,2%nat,RestoreG 15);(1988,2%nat,RestoreG 14);
 (1990,2%nat,RestoreG 13);(1992,2%nat,RestoreG 12);(1994,1%nat,RestoreG 3);(1995,1%nat,RestoreG 5);
 (1996,3%nat,ZeroUpper);(1999,1%nat,Ret)].
Lemma linked_path:linked TableFrame.text path.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias:=segment (TableFrame.base bias) TableFrame.text 11.
Definition back bias:=bias+TableEntry.site+185.
Lemma raw o s c t rs back : regs s 15%nat=8 -> regs s 5%nat=t-8 -> 48<=t -> t+8<2^64 ->
 (forall i r,nth_error TableFrame.saved_regs i=Some r -> read_word (mem s) (t-8*(1+Z.of_nat i))=rs r) ->
 word64 back -> read_word (mem s) t=back ->
 exists last,run 11 (ScalarBytes.fetch o TableFrame.text) (State(Running 1947) s c)=Some(last,[]) /\
 loc last=Returned back /\ regs(cpu_state last) 4%nat=t+8 /\ mem(cpu_state last)=mem s /\
 forall r,In r sysv_saved -> regs(cpu_state last) r=rs r.
Proof.
 intros Last BP Low High Slots Back Link;eexists;split.
 - apply (InstructionRoute.checked _ _ _ linked_path);cbn [path follow loc cpu_state cf step eval_condition flag with_zf option_map];rewrite Last;reflexivity.
 - cbn [path follow loc cpu_state cf step eval_condition flag with_zf option_map];rewrite ?Last;
   cbn [loc cpu_state pop caller_step stack_step target_ip result_regs result_mem apply_stack advance_rsp stack_top
    effective set set_regs with_words with_zf regs mem put Nat.eqb].
   unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite BP.
   repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64;lia)) end.
   repeat split;try lia.
   + match goal with |-Returned(word(read_word _ ?a))=_=>replace a with t by ring end;now rewrite Link,word_fits.
   + intros r K;destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
     all: match goal with |- read_word _ ?a = ?f ?r =>
       let i:=(eval compute in (match r with 5%nat=>0%nat|3%nat=>1%nat|12%nat=>2%nat|13%nat=>3%nat|14%nat=>4%nat|_=>5%nat end)) in
       rewrite <-(Slots i r eq_refl);f_equal;ring end.
Qed.
Record returned pol bias e caller q:Prop:=ReturnedTable {
 pc:ip q=back bias;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 stack:regs(machine q) 4%nat=TableEntry.frame pol e+8;
 registers:forall r,In r sysv_saved -> regs(machine q) r=regs(machine caller) r;
 parent:TableParentFrame.retained pol bias e (machine caller) (machine q);
 contents:TableContents.contents e (TableRowMeaning.point e (machine caller)) (machine q)
}.

Theorem checked pol bias e caller p : placement e -> loaded pol bias (mem e) (writable e) -> well_formed(machine caller) ->
 TableRounds.at_multiple pol bias e 8 p -> TableParentFrame.retained pol bias e (machine caller) (machine p) ->
 TableContents.contents e (TableRowMeaning.point e (machine caller)) (machine p) ->
 exists q,execute bias p=Some q /\ returned pol bias e caller q /\ mem(machine q)=mem(machine p) /\ log q=log p.
Proof.
 intros P I CW [PC Acc W Ptr] K Rows;set (t:=TableEntry.frame pol e) in *.
 destruct(stack_ok _ P) as [[SL SH] _].
 assert (B:48<=t /\ t+8<2^64) by (unfold t,TableEntry.frame,common_top,Rows.frame,sp in *;destruct pol;lia).
 assert (Fit:word64(back bias)) by (destruct(proj1(symbols _ _ _ _ I _ _ (in_common pol))) as [L H];
    change (Z.of_nat(length PrepareChunk.CommonBytes.symbol_bytes)) with 290 in H;unfold word64,back,TableEntry.site;lia).
 destruct(raw (TableFrame.base bias) (machine p) (LinkedRun.carry p) t (regs(machine caller)) (back bias)
   (TableMultiple.multiple _ _ _ _ Ptr) (TableMultiple.frame_pointer _ _ _ _ Ptr) (proj1 B) (proj2 B)
   (fun i r=>TableParentFrame.saved pol bias e (machine caller) (machine p) i r P K CW) Fit (TableParentFrame.link _ _ _ _ _ P K Fit))
  as [last [Run [Dest [SP [Mem SysV]]]]].
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(at_segment _ _ p _ _ 11 1947 _ _ Acc PC Map Sep Run (Forall_nil _)) as [Next Paid].
 eexists;split;[exact Next|split;[constructor|split;[exact Mem|apply app_nil_r]]].
 - cbn [LinkedRun.finish ip];unfold absolute;now rewrite Dest.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ W Next).
 - exact SP.
 - exact SysV.
 - unfold TableParentFrame.retained;cbn [LinkedRun.finish machine];now rewrite Mem.
 - apply (TableContents.preserve _ _ (machine p));[intros x X;cbn [LinkedRun.finish machine];now rewrite Mem|exact Rows].
Qed.

Definition observe pol bias e p ks:=bind (TableRounds.observe pol bias e p ks) (fun '(a,bank)=>
 option_map (fun q=>(q,bank)) (execute bias a)).
Theorem from_eligible pol bias e before p ks:placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q bank,observe pol bias e p ks=Some(q,bank) /\ returned pol bias e p q.
Proof.
 intros P I Al E Live;destruct(TableContents.checked _ _ _ _ _ ks P I Al E Live) as [z [bank [Round [Z [Kept Rows]]]]].
 destruct(checked _ _ _ _ _ P I (EligibleLanes.words _ _ _ _ _ E) Z Kept Rows) as [q [Run [Q _]]].
 exists q,bank;split;[unfold observe;rewrite Round;cbn [bind];now rewrite Run|exact Q].
Qed.
