From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.WordSemantics
 execution.WordBounds execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory
 memory.WriteTrace memory.MemoryGeometry execution.VectorProcedure.
From Curve25519 Require Import Radix51 Field.
From Ed25519Simd.Decode Require Kernels DecoderBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode DecoderSave.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct.
Import ListNotations. Local Open Scope Z_scope.
Definition text:=DecoderFrame.code.
Definition base bias:=bias+DecoderFrame.origin.
Definition link_slot pol e:=DecoderFrame.top (common_top pol e-112)-8.
Definition set_rhs bias:=segment (base bias) text 1.
Definition square bias:=then_run (set_rhs bias) (DecoderProduct.multiply_call bias).
Definition lea_line:list line:=[(497,7%nat,LeaG 8 (Address 7 None 320))].
Lemma image : linked text lea_line /\ ScalarBytes.decode (skipn 504 text)=Some(5%nat,CallRelative(0xa57-509)).
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition raw signature e s := forall j,(j<8)%nat -> let y:=digits signature e s j in
 split_field y /\ limbs y=original_encoding signature e j mod 2^255 /\
 Z.testbit (regs s 0%nat) (Z.of_nat j)=Z.testbit (original_encoding signature e j) 255.
Definition squared signature pol bias e p := ip p=base bias+509 /\ accounted e (writable e) p /\
 frame signature pol bias e (machine p) /\ raw signature e (machine p) /\
 forall j,(j<8)%nat -> let y:=original_encoding signature e j mod 2^255 in let yy:=vectors(machine p) j in
 field_bound (Kernels.out_bound Kernels.Multiply) yy /\ represents (limbs yy) (y*y) /\ 2<=yy 0%nat.
Lemma depth pol e : sp e-2048<=link_slot pol e<sp e-1000.
Proof. unfold link_slot,DecoderFrame.top;pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia));
 unfold common_top,Rows.frame,sp in *;destruct pol;lia. Qed.

Theorem from_saved signature pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 saved signature bias e p -> frame signature pol bias e (machine p) ->
 (forall j i,(j<8)%nat -> (i<5)%nat -> digits signature e (machine p) j i=vectors(machine p) j i) ->
 exists q,square bias p=Some q /\ squared signature pol bias e q /\
 preserved (other_scratch signature e) (mem(machine p)) (mem(machine q)).
Proof.
 intros P M [PC [Acc [_ Raw]]] [DI [SP [Link [Constants Caller]]]] Data.
 set (s:=machine p) in *;set (o:=base bias) in *;set (stack:=link_slot pol e) in *;change (regs s 4%nat=stack) in SP;change (read_word (mem s) stack=word(o+resume_offset signature)) in Link.
 pose proof(depth pol e) as Deep;fold stack in Deep.
 destruct(Return.stack_ok _ P) as [[Lo Hi] _];destruct(scratch_ok _ P) as [[SL SH] Al].
 assert (Addr:word(regs s 7%nat+0+320)=address signature e) by
  (rewrite DI;unfold address,point,point_offset;destruct signature;rewrite word_fits by (unfold word64;lia);ring).
 set (v:=set s 8 (address signature e)).
 assert (R:run 1 (ScalarBytes.fetch o text) (State (Running 497) s (carry p))=Some(State (Running 504) v (carry p),[])).
 { apply (checked _ _ _ (proj1 image));cbn [lea_line follow loc cf cpu_state step effective option_map];now rewrite Addr. }
 destruct(mapped_now _ _ _ M _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text _ 497 _ _ Acc PC Map Sep R (Forall_nil _)) as [Lea Paid].
 set (mid:=LinkedRun.finish o p (State (Running 504) v (carry p),[])) in *.
 set (child:=push v (o+509));set (args:=DecoderProduct.arguments child).
 assert (V8:regs child 8%nat=address signature e) by reflexivity.
 assert (A:DecoderProduct.readable args child).
 { split;[rewrite V8;unfold address;replace 320 with (5*64) by reflexivity;rewrite Z.mod_add by lia;apply point_aligned,Al|
   split;[rewrite V8;unfold fits64,address,point,point_offset;destruct signature;lia|reflexivity]]. }
 destruct(DecoderProduct.call_at pol bias e 504 args P M ltac:(lia) ltac:(lia) (proj2 image) mid A eq_refl Paid
    ltac:(change (bottom (DecoderProduct.area e)+24<=regs s 4%nat<=ceiling (DecoderProduct.area e));
       change (sp e-16384+24<=regs s 4%nat<=sp e);change (regs s 4%nat=stack) in SP;rewrite SP;lia)) as [q [Call [At Done G Keep YY]]].
 assert (K:forall x,~(stack-24<=x<stack) -> mem(machine q) x=mem s x).
 { intros x X;apply Keep;change (~(regs s 4%nat-24<=x<regs s 4%nat));now rewrite SP. }
 assert (Outside:forall i j k,(i<5)%nat -> (j<8)%nat -> 0<=k<8 ->
   ~(stack-24<=address signature e+64*Z.of_nat i+8*Z.of_nat j+k<stack)).
 { intros;destruct(scratch_stack _ P);unfold disjoint,address,point,point_offset in *;destruct signature;lia. }
 assert (D:forall i j,(i<5)%nat -> (j<8)%nat -> digits signature e (machine q) j i=digits signature e s j i).
 { intros i j I J;apply preserved_read with (outside:=fun x=>~(stack-24<=x<stack));[exact K|intros k B;exact (Outside i j k I J B)]. }
 assert (Inputs:forall j i,(j<8)%nat -> (i<5)%nat -> args j i=digits signature e s j i /\ args j (5+i)%nat=digits signature e s j i).
 { intros j i J I;unfold args,DecoderProduct.arguments.
   rewrite (proj2(Nat.leb_gt 5 i) ltac:(lia)),(proj2(Nat.leb_le 5 (5+i)) ltac:(lia)),
     (proj2(Nat.ltb_lt (5+i) 10) ltac:(lia));cbn [andb].
   split;[symmetry;apply Data;assumption|].
   replace (5+i-5)%nat with i by lia;unfold DecoderProduct.rhs_at,digits;rewrite V8.
   apply preserved_read with (outside:=fun x=>~(stack-8<=x<stack)).
   - intros x X;change (store_word (mem s) (word(regs s 4%nat-8)) (o+509) x=mem s x).
     rewrite SP,word_fits by (unfold word64;lia);apply write_outside;lia.
   - intros k B;pose proof(Outside i j k I J B);lia. }
 assert (C:forall j i,(i<4)%nat -> args j (28+i)%nat=DecoderFrame.constant i).
 { intros j i I;unfold args,DecoderProduct.arguments;rewrite (proj2(Nat.ltb_ge (28+i) 10) ltac:(lia)),andb_false_r;apply Constants,I. }
 exists q;split;[unfold square,then_run,set_rhs;fold o;rewrite Lea;exact Call|].
 split.
 2:{ intros x [X _];apply K;destruct(scratch_stack _ P);unfold span,disjoint in *;lia. }
 split;[exact At|split;[exact Done|split]].
 - unfold frame;split;[rewrite G;exact DI|split;[rewrite G;exact SP|split]].
   + change (read_word (mem(machine q)) stack=word(o+resume_offset signature));rewrite <-Link.
     apply preserved_read with (outside:=fun x=>~(stack-24<=x<stack));[exact K|intros;lia].
   + split.
     * intros i j I;rewrite YY;destruct ((proj2 DecoderProduct.multiplication) no_read no_read (args j) (args j)
       ltac:(reflexivity)) as [_ High];rewrite High by lia;apply C,I.
     * eapply keep_caller;[exact Caller| |].
       -- intros r InReg;rewrite G;change (Instructions.put (regs s) 8 (address signature e) r=regs s r);
          unfold Instructions.put;destruct (Nat.eqb_spec 8 r);[subst;unfold caller_reg in InReg;cbn in InReg;lia|reflexivity].
       -- intros x X;apply K;unfold caller_bytes in X;unfold stack,link_slot,DecoderFrame.top in *;
          pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia));destruct(scratch_stack _ P);
          unfold disjoint,common_top,Rows.frame,sp in *;destruct pol;lia.
 - split;intros j J;destruct(Raw j J) as [B [Y Sign]].
   + split;[intros i I;rewrite D by assumption;apply B,I|split].
     * rewrite <-Y;apply limbs_ext;intros;apply D;assumption.
     * rewrite G;exact Sign.
   + pose proof(DecoderProduct.lane_square (args j) (digits signature e s j) B
       ltac:(intros i I;apply Inputs;assumption) (C j)) as [Bound [Value Positive]].
     split;[intros i I;rewrite YY;apply Bound,I|split;[|rewrite YY;exact Positive]].
     erewrite limbs_ext;[rewrite <-Y;exact Value|intro i;intros;apply YY].
Qed.

Definition square_input bias p incoming:=bind (save_input bias p incoming) (fun '(q,k)=>
 option_map (fun t=>(t,k)) (square bias q)).
Theorem from_setup signature pol bias e p incoming : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> setup signature pol bias e p ->
 exists q k,square_input bias p incoming=Some(q,k) /\ squared signature pol bias e q /\
 preserved (other_scratch signature e) (mem(machine p)) (mem(machine q)).
Proof.
 intros P M Al E;destruct(DecoderSave.from_setup signature _ _ _ _ incoming P M Al E) as [q [k [Setup [Saved [Frame [Data Keep]]]]]].
 destruct(from_saved signature _ _ _ _ P M Saved Frame Data) as [t [Run [Value More]]].
 exists t,k;split;[unfold square_input;rewrite Setup;cbn [bind];now rewrite Run|split;[exact Value|intros x X;now rewrite More,Keep by exact X]].
Qed.
