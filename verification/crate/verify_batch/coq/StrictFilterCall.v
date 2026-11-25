From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.DalekPostHash Require FilterBytes.
From Ed25519Simd.PrepareChunk Require StrictBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require PreparedReturn.
Import ListNotations. Local Open Scope Z_scope.

Definition path:list line:=[(9,2%nat,Test32 0);(11,2%nat,Branch Equal (35-13));(13,3%nat,CopyG 7 3);
 (16,4%nat,LeaG 6 (Address 3 None 64));(20,5%nat,CallRelative (FilterBytes.address-(PrepareNative.strict+25)))].
Lemma code : linked StrictBytes.symbol_bytes path.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma in_filter: In (FilterBytes.address,FilterBytes.symbol_bytes) (children Dalek).
Proof. apply in_or_app;right;do 3 right;left;reflexivity. Qed.
Definition execute bias:=segment (bias+PrepareNative.strict) StrictBytes.symbol_bytes 5.
Definition slot e:=common_top Dalek e.
Definition link bias:=bias+PrepareNative.strict+25.
Definition event bias e:=qword (word(bias+PrepareNative.strict+20)) (slot e) (link bias).
Record entry bias e p q:Prop:=Entry {
 pc:ip q=bias+FilterBytes.address; writes:accounted e (writable e) q; words:well_formed(machine q);
 stack:regs(machine q) 4%nat=slot e; keys:regs(machine q) 7%nat=PrepareOutputs.dest e;
 flags:regs(machine q) 6%nat=PrepareOutputs.dest e+64;
 back:read_word (mem(machine q)) (slot e)=link bias;
 memory_after:mem(machine q)=commit (mem(machine p)) (event bias e);
 history:log q=log p++[event bias e];
 caller_registers:forall g,g<>4%nat -> g<>7%nat -> g<>6%nat -> regs(machine q) g=regs(machine p) g
}.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked bias outer e p : placement e -> loaded Dalek bias (mem e) (writable e) ->
 PreparedReturn.result Dalek bias outer e p -> exists q,execute bias p=Some q /\ entry bias e p q.
Proof.
 intros P I Done;set (o:=bias+PrepareNative.strict);set (s:=machine p);set (d:=PrepareOutputs.dest e).
 pose proof(PreparedReturn.strict_arg _ _ _ _ _ Done eq_refl) as BX;fold s d in BX.
 pose proof(PreparedReturn.stack _ _ _ _ _ Done) as SP;fold s in SP;fold (slot e) in SP.
 pose proof(PreparedReturn.success _ _ _ _ _ Done) as AX;fold s in AX.
 pose proof(mapped_word _ _ _ I _ _ in_filter ltac:(vm_compute;reflexivity)) as Target.
 destruct(stack_ok _ P) as [[Low High] _].
 assert (Safe:word64(slot e) /\ word64(d+64)) by (unfold slot,d,PrepareOutputs.dest,common_top,Rows.frame,sp,word64 in *;split;lia).
 assert (Back:word64(link bias)) by (destruct(proj1(symbols _ _ _ _ I _ _ in_strict)) as [L H];
    change (Z.of_nat(length StrictBytes.symbol_bytes)) with 37 in H;change (0<=bias+PrepareNative.strict+25<2^64);lia).
 set (arg:=set (set (with_zf s false) 7 d) 6 (d+64)).
 set (child:=push arg (link bias)).
 assert (Step:run 5 (ScalarBytes.fetch o StrictBytes.symbol_bytes) (State(Running 9) s (LinkedRun.carry p))=
     Some(State(Running(FilterBytes.address-PrepareNative.strict)) child (Some false),[event bias e])).
 { apply (InstructionRoute.checked _ _ _ code);cbn [path follow loc cpu_state cf step option_map eval_condition flag with_zf];rewrite AX.
   cbn [loc cpu_state cf with_zf flag option_map step set set_regs effective regs put Nat.eqb];rewrite BX,Z.add_0_r,(word_fits _ (proj2 Safe)),SP.
   replace (slot e+8-8) with (slot e) by ring;rewrite (word_fits _ (proj1 Safe)).
   replace (o+(20+Z.of_nat 5+(FilterBytes.address-(PrepareNative.strict+25)))) with (bias+FilterBytes.address) by (unfold o;ring).
   rewrite (word_fits _ Target);replace (bias+FilterBytes.address-o) with (FilterBytes.address-PrepareNative.strict) by (unfold o;ring);reflexivity. }
 assert (W:confined (writable e) [event bias e]) by (constructor;[intros x X;left;change (slot e<=x<slot e+8) in X;
    unfold slot,common_top,Rows.frame,sp,span in *;lia|constructor]).
 pose proof(PreparedReturn.writes _ _ _ _ _ Done) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc in_strict) as [Map Sep].
 destruct(at_segment _ _ p o _ 5 9 _ _ Acc (PreparedReturn.pc _ _ _ _ _ Done) Map Sep Step W) as [End Paid].
 assert (Top:word(regs arg 4%nat-8)=slot e) by (change (word(regs s 4%nat-8)=slot e);rewrite SP;
    replace (slot e+8-8) with (slot e) by ring;apply word_fits,Safe).
 eexists;split;[exact End|constructor].
 - cbn [LinkedRun.finish absolute loc ip];unfold o;ring.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ (PreparedReturn.words _ _ _ _ _ Done) End).
 - exact Top.
 - reflexivity.
 - reflexivity.
 - change (read_word (store_word (mem arg) (word(regs arg 4%nat-8)) (link bias)) (slot e)=link bias);
    rewrite Top;apply write_read_word,Back.
 - change (store_word (mem arg) (word(regs arg 4%nat-8)) (link bias)=commit (mem s) (event bias e));now rewrite Top.
 - reflexivity.
 - intros g R D S;change (put (put (put (regs s) 7 d) 6 (d+64)) 4 (word(regs arg 4%nat-8)) g=regs s g).
   unfold put;now rewrite (proj2(Nat.eqb_neq 4 g) ltac:(lia)),(proj2(Nat.eqb_neq 6 g) ltac:(lia)),(proj2(Nat.eqb_neq 7 g) ltac:(lia)).
Qed.
End Iteration.
