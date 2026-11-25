From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute execution.ScalarWords memory.ByteMemory memory.FlatMemory memory.WriteTrace abi.SysV.
From Ed25519Simd.CachedAdd Require CachedAddBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableAddLayout TablePackRows.
Import ListNotations. Local Open Scope Z_scope.
Definition delta:=TableAddLayout.origin-(TableEntry.origin+1974).
Definition code:list line:=[(1947,4%nat,Compare32 15 8);(1951,2%nat,Branch Equal (1982-1953));
 (1953,3%nat,CopyG 7 12);(1956,3%nat,CopyG 6 4);(1959,5%nat,Imm32 2 1);(1964,5%nat,Imm32 1 1);(1969,5%nat,CallRelative delta)].
Lemma image:linked TableFrame.text code.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition enter bias:=segment (TableFrame.base bias) TableFrame.text 7.
Record entry pol bias e p q:Prop:=Entry {
 address:ip q=bias+TableAddLayout.origin;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 arguments:CachedAddBytes.concrete_entry true true (TableAddLayout.layout pol bias e) TableAddLayout.size TableAddLayout.pad
    (regs(machine q)) (vectors(machine q)) (mem(machine q));
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 pushed:mem(machine q)=store_word (mem(machine p)) (TableAddLayout.stage pol e-8) (TableAddLayout.back bias)
}.
Theorem checked pol bias e digit p : placement e -> loaded pol bias (mem e) (writable e) -> 1<=digit<8 ->
 ip p=TableFrame.base bias+1947 -> accounted e (writable e) p -> well_formed(machine p) -> TableMultiple.pointers pol e digit (machine p) ->
 exists q,enter bias p=Some q /\ entry pol bias e p q.
Proof.
 intros P I D PC Acc W Ptr;set (o:=TableFrame.base bias) in *;set (s:=machine p) in *;set (a:=TableAddLayout.stage pol e).
 pose proof(TableMultiple.multiple _ _ _ _ Ptr) as Digit;pose proof(TableMultiple.source _ _ _ _ Ptr) as Pt;
 pose proof(TableMultiple.stack _ _ _ _ Ptr) as SP;change (regs s 4%nat=a) in SP.
 pose proof(TableAddLayout.stack pol e) as Depth;fold a in Depth;destruct(stack_ok _ P) as [[Low High] _].
 assert (Bound:word(regs s 4%nat-8)=a-8) by (rewrite SP;apply word_fits;unfold word64;lia).
 assert (Dest:word64(bias+TableAddLayout.origin)) by exact (mapped_word _ _ _ I _ _ (TableAddLayout.image pol) ltac:(vm_compute;reflexivity)).
 set (args:=set (set (set (set (with_zf s false) 7 (TableEntry.point e)) 6 a) 2 1) 1 1).
 set (callee:=push args (TableAddLayout.back bias));set (w:=qword (word(o+1969)) (a-8) (TableAddLayout.back bias)).
 assert (Run:run 7 (ScalarBytes.fetch o TableFrame.text) (State(Running 1947) s (LinkedRun.carry p))=
    Some(State(Running(TableAddLayout.origin-TableEntry.origin)) callee (Some true),[w])).
 { apply (InstructionRoute.checked _ _ _ image);cbn [code follow step loc cpu_state cf option_map app eval_condition with_zf flag set set_regs regs put Nat.eqb].
   rewrite Digit,(Z.mod_small digit (2^32)) by lia;change (8 mod 2^32) with 8.
   rewrite (proj2(Z.eqb_neq digit 8) ltac:(lia)),(proj2(Z.ltb_lt digit 8) ltac:(lia)).
   replace (o+(1969+Z.of_nat 5+delta)) with (bias+TableAddLayout.origin) by (unfold o,TableFrame.base,delta;ring).
   rewrite (word_fits _ Dest);replace (bias+TableAddLayout.origin-o) with (TableAddLayout.origin-TableEntry.origin) by (unfold o,TableFrame.base;ring).
   rewrite Bound,SP,Pt;reflexivity. }
 assert (Safe:confined (writable e) [w]) by (constructor;[intros x X;change (a-8<=x<a-8+8) in X;left;unfold span;lia|constructor]).
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [Map Sep].
 destruct(at_segment _ _ p o TableFrame.text 7 1947 _ _ Acc PC Map Sep Run Safe) as [Next Paid].
 set(q:=LinkedRun.finish o p (State(Running(TableAddLayout.origin-TableEntry.origin)) callee (Some true),[w])) in *.
 pose proof(segment_wf _ _ _ p q W Next) as WF.
 assert (G:regs callee=put (regs args) 4 (a-8)) by (unfold callee,args;cbn [push push_words with_words regs set set_regs with_zf put Nat.eqb];now rewrite Bound).
 assert (M:mem callee=store_word (mem s) (a-8) (TableAddLayout.back bias)) by
   (unfold callee,args;cbn [push push_words with_words regs set set_regs with_zf mem put Nat.eqb];now rewrite Bound).
 exists q;split;[exact Next|constructor];change (machine q) with callee.
 - change (o+(TableAddLayout.origin-TableEntry.origin)=bias+TableAddLayout.origin);unfold o,TableFrame.base;ring.
 - exact Paid.
 - exact WF.
 - constructor;[apply TableAddLayout.valid;assumption|exact (proj2(proj2 WF))|exact (proj1 WF)|exact (proj1(proj2 WF))| | | | | |].
   + rewrite G,TableAddLayout.entry_sp;reflexivity.
   + rewrite G;reflexivity.
   + rewrite G;reflexivity.
   + rewrite G;reflexivity.
   + rewrite G;reflexivity.
   + rewrite M,TableAddLayout.entry_sp;apply write_read_word,TableAddLayout.continuation with (pol:=pol) (e:=e);exact I.
 - intros r K;rewrite G;destruct K as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity.
 - exact M.
Qed.
