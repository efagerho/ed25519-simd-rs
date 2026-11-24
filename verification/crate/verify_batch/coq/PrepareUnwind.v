From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics
 execution.WordBounds execution.ScalarBytes execution.MappedFetch execution.InstructionRoute
 memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.PrepareChunk Require CommonBytes StrictBytes.
From Ed25519Simd.VerifyBatch Require Import PrepareNative.
Import ListNotations. Local Open Scope Z_scope.

Definition common_reject : list line :=
 [(65,2%nat,Test32 0);(67,6%nat,Branch Equal 187);(260,4%nat,Add64 4 64);
  (264,2%nat,RestoreG 15);(266,2%nat,RestoreG 14);(268,2%nat,RestoreG 13);
  (270,2%nat,RestoreG 12);(272,1%nat,RestoreG 3);(273,1%nat,ScalarBytes.Ret)].
Definition strict_reject : list line :=
 [(9,2%nat,Test32 0);(11,2%nat,Branch Equal 22);(35,1%nat,RestoreG 3);(36,1%nat,ScalarBytes.Ret)].

Lemma common_bytes : linked CommonBytes.symbol_bytes common_reject.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma strict_bytes : linked StrictBytes.symbol_bytes strict_reject.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition returned top (s:cpu) last :=
 loc last=Returned (word (read_word (mem s) top)) /\ regs (cpu_state last) 4%nat=top+8 /\
 regs (cpu_state last) 0%nat=regs s 0%nat /\ mem (cpu_state last)=mem s.

Local Ltac unwind image route sp zero :=
 lazymatch goal with |-exists t,_=>eexists end;split;
 [apply (checked _ _ _ image);cbn [at_pc route follow step loc cpu_state cf option_map eval_condition flag with_zf];
  rewrite zero;reflexivity|];
 unfold returned;cbn [at_pc route follow step loc cpu_state cf option_map eval_condition flag with_zf];
 rewrite ?zero;cbn [loc cpu_state step pop caller_step stack_step result_regs result_mem target_ip
             set set_regs with_words apply_stack regs with_zf flag mem advance_rsp stack_top put Nat.eqb];rewrite sp;
 unfold stack_top,advance_rsp,put;cbn [Nat.eqb];rewrite ?sp;
 repeat match goal with |-context[word ?a]=>rewrite (word_fits a ltac:(unfold word64 in *;lia)) end;
 repeat split;try reflexivity;try (repeat f_equal;ring);try lia.

Lemma common_returns slide s c top : 112<=top -> top+8<2^64 ->
 regs s 4%nat=top-104 -> regs s 0%nat mod 2^32=0 ->
 exists last,run 9 (ScalarBytes.fetch (slide+common) CommonBytes.symbol_bytes) (at_pc 65 s c)=Some(last,[]) /\
 returned top s last /\ regs (cpu_state last) 13%nat=read_word (mem s) (top-24) /\
 regs (cpu_state last) 14%nat=read_word (mem s) (top-32) /\
 regs (cpu_state last) 12%nat=read_word (mem s) (top-16).
Proof. intros L H SP Zero. unwind common_bytes common_reject SP Zero;f_equal;ring. Qed.

Lemma strict_returns slide s c top : 8<=top -> top+8<2^64 ->
 regs s 4%nat=top-8 -> regs s 0%nat mod 2^32=0 ->
 exists last,run 4 (ScalarBytes.fetch (slide+strict) StrictBytes.symbol_bytes) (at_pc 9 s c)=Some(last,[]) /\
 returned top s last /\ regs (cpu_state last) 13%nat=regs s 13%nat /\
 regs (cpu_state last) 14%nat=regs s 14%nat /\ regs(cpu_state last) 12%nat=regs s 12%nat.
Proof. intros L H SP Zero. unwind strict_bytes strict_reject SP Zero. Qed.

From Machine Require Import execution.LinkedRun memory.FlatMemory memory.MemoryGeometry.
From Machine Require execution.ScalarRefinement.
From Ed25519Simd.VerifyBatch Require Import Policy Rows Image Return LoadedImage BatchScalar.

Definition leave_strict pol bias (p:cursor) := match pol with
 | Zip215=>Some p | Dalek=>segment (bias+PrepareNative.strict) StrictBytes.symbol_bytes 4 p end.
Definition unwind pol bias p :=
 bind (segment (bias+PrepareNative.common) CommonBytes.symbol_bytes 9 p) (leave_strict pol bias).
Definition prepared_again entry e p q := ip q=word(entry+offset Prepared) /\
 regs(machine q) 4%nat=Rows.frame e /\ regs(machine q) 0%nat=regs(machine p) 0%nat /\
 mem(machine q)=mem(machine p) /\ log q=log p /\ Prologue.output_registers e (machine q) /\
 regs(machine q) 12%nat=Prologue.rows_left (regs e 6%nat).

Theorem rejected pol bias entry e p :
 Return.placement e -> loaded pol bias (mem e) (writable e) ->
 BatchScalar.post pol bias entry e p -> regs(machine p) 0%nat mod 2^32=0 ->
 exists q,unwind pol bias p=Some q /\ prepared_again entry e p q.
Proof.
 intros Place Image [IP [SP [Acc [[Root Shim] [[Count [Out Left]] _]]]]] Zero.
 destruct (stack_ok _ Place) as [[Low High] _].
 set (top:=common_top pol e) in *.
 assert (Limits:112<=top /\ top+8<2^64) by
   (unfold top,common_top,Rows.frame,sp in *;destruct pol;lia).
 destruct(common_returns bias (machine p) (carry p) top (proj1 Limits) (proj2 Limits) SP Zero)
   as [last [Run [[Ret [Stack [Eax Flat]]] [C [O R12]]]]].
 destruct (mapped_now _ _ _ Image _ _ _ Acc (in_common _)) as [Map Sep].
 destruct (at_segment _ _ _ _ _ _ 65 _ _ Acc IP Map Sep Run (Forall_nil _)) as [Next Paid].
 set (q:=LinkedRun.finish (bias+PrepareNative.common) p (last,[])) in *.
 assert (PC:ip q=word (read_word (mem(machine p)) top)).
 { unfold q;cbn [LinkedRun.finish ip];unfold absolute;rewrite Ret;reflexivity. }
 assert (Log:log q=log p) by (unfold q;cbn [LinkedRun.finish log];apply app_nil_r).
 assert (Outputs:Prologue.output_registers e (machine q)) by
   (split;[exact (eq_trans C Count)|exact (eq_trans O Out)]).
 unfold unwind;rewrite Next;cbn [bind]. fold q. destruct pol.
 - exists q;split;[reflexivity|]. unfold prepared_again;split;[|split;[|exact (conj Eax (conj Flat (conj Log (conj Outputs (eq_trans R12 Left)))))]].
   + unfold top,common_top in PC;rewrite Z.sub_0_r,Root,ScalarRefinement.word_idempotent in PC;exact PC.
   + change (regs(cpu_state last) 4%nat=Rows.frame e);rewrite Stack;unfold top,common_top;ring.
 - assert (Strict:ip q=bias+PrepareNative.strict+9).
   { unfold top in PC;rewrite PC,Shim,ScalarRefinement.word_idempotent;apply word_fits.
     destruct(proj1(symbols _ _ _ _ Image _ _ in_strict)) as [L U].
     change (Z.of_nat(length StrictBytes.symbol_bytes)) with 37 in U;unfold word64;lia. }
   set (outer:=Rows.frame e-8).
   destruct(strict_returns bias (machine q) (carry q) outer ltac:(unfold outer,Rows.frame,sp in *;lia)
     ltac:(unfold outer,Rows.frame,sp in *;lia)
     ltac:(change (regs(cpu_state last) 4%nat=outer-8);rewrite Stack;unfold outer,top,common_top;ring)
     ltac:(change (regs(cpu_state last) 0%nat mod 2^32=0);now rewrite Eax)) as [endst [End [[Back [Top [AX M]]] [N [D L12]]]]].
   destruct(mapped_now _ _ _ Image _ _ _ Paid in_strict) as [Mapped Apart].
   destruct(at_segment _ _ _ _ _ _ 9 _ _ Paid Strict Mapped Apart End (Forall_nil _)) as [After _].
   exists (LinkedRun.finish (bias+PrepareNative.strict) q (endst,[]));split;[exact After|].
   unfold prepared_again;cbn [LinkedRun.finish ip machine log];unfold absolute;rewrite Back.
   change (mem(machine q)=mem(machine p)) in Flat;unfold outer;rewrite Flat,Root,ScalarRefinement.word_idempotent.
   repeat split;[rewrite Top;unfold outer;ring|rewrite AX;exact Eax|now rewrite M|now rewrite app_nil_r,Log|rewrite N;exact (proj1 Outputs)|rewrite D;exact (proj2 Outputs)|rewrite L12;exact (eq_trans R12 Left)].
Qed.
