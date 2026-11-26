From Ed25519Simd.Decode Require NativeProduct.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.WordSemantics
 execution.WordBounds execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory
 memory.WriteTrace memory.MemoryGeometry execution.VectorProcedure.
From Machine Require abi.StackFrame.
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
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition raw signature e s := forall j,(j<8)%nat -> let y:=digits signature e s j in
 radix_digits y /\ limbs y=original_encoding signature e j mod 2^255 /\
 Z.testbit (regs s 0%nat) (Z.of_nat j)=Z.testbit (original_encoding signature e j) 255.
Definition squared signature pol bias e p := ip p=base bias+509 /\ accounted e (writable e) p /\
 frame signature pol bias e (machine p) /\ raw signature e (machine p) /\
 forall j,(j<8)%nat -> let y:=original_encoding signature e j mod 2^255 in let yy:=vectors(machine p) j in
 field_bound (Kernels.out_bound Kernels.Multiply) yy /\ represents (limbs yy) (y*y) /\ 2<=yy 0%nat.
Lemma depth pol e : sp e-2048<=link_slot pol e<sp e-1000.
Proof. unfold link_slot,DecoderFrame.top;pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia));
 unfold common_top,Rows.frame,sp in *;destruct pol;lia. Qed.

(* Layout of the caller-owned data that is live across the multiplication. *)
Record square_layout signature pol e := {
 call_room : bottom (DecoderProduct.area e)+24<=link_slot pol e<=ceiling (DecoderProduct.area e);
 push_fits : word64 (link_slot pol e-8);
 input_apart : disjoint (link_slot pol e-24) 24 (address signature e) 320;
 caller_apart : forall x,caller_bytes pol e x -> StackFrame.outside (link_slot pol e) 24 x
}.

Lemma layout signature pol e : placement e -> square_layout signature pol e.
Proof.
 intro P;pose proof (depth pol e) as Depth;destruct(Return.stack_ok _ P) as [[Lo Hi] _].
 pose proof (scratch_stack _ P) as Apart;constructor.
 - change (sp e-16384+24<=link_slot pol e<=sp e);lia.
 - unfold word64;lia.
 - unfold disjoint,address,point,point_offset in *;destruct signature;lia.
 - intros x X;unfold caller_bytes,StackFrame.outside,link_slot,DecoderFrame.top in *.
   pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia)).
   unfold disjoint,common_top,Rows.frame,sp in *;destruct pol;lia.
Qed.

Lemma digits_kept signature e top depth s t :
 disjoint (top-depth) depth (address signature e) 320 ->
 preserved (StackFrame.outside top depth) (mem s) (mem t) ->
 forall j i,(j<8)%nat -> (i<5)%nat -> digits signature e t j i=digits signature e s j i.
Proof.
 intros Apart Keep j i J I;unfold digits;apply (StackFrame.read_outside _ _ _ _ _ _ Keep).
 change (disjoint (top-depth) depth (address signature e+64*Z.of_nat i+8*Z.of_nat j) 8).
 unfold disjoint in *;lia.
Qed.

Theorem from_saved signature pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 saved signature bias e p -> frame signature pol bias e (machine p) ->
 (forall j i,(j<8)%nat -> (i<5)%nat -> digits signature e (machine p) j i=vectors(machine p) j i) ->
 exists q,square bias p=Some q /\ squared signature pol bias e q /\
 preserved (setup_untouched signature pol e) (mem(machine p)) (mem(machine q)).
Proof.
 intros P M [PC [Acc [_ Raw]]] [DI [SP [Link [Constants Caller]]]] Data.
 set (s:=machine p) in *;set (o:=base bias) in *;set (stack:=link_slot pol e) in *;change (regs s 4%nat=stack) in SP;change (read_word (mem s) stack=word(o+resume_offset signature)) in Link.
 destruct(layout signature pol e P) as [Room Fit Apart Live];fold stack in Room,Fit,Apart,Live.
 destruct(scratch_ok _ P) as [[SL SH] Al].
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
    ltac:(change (bottom (DecoderProduct.area e)+24<=regs s 4%nat<=ceiling (DecoderProduct.area e));now rewrite SP))
   as [q [Call [At Done G Keep YY]]].
 destruct (StackFrame.call_frame v (o+509) (mem(machine q)) stack 24 SP Fit ltac:(lia) Keep)
   as [Pushed [Kept ReturnWord]].
 pose proof (digits_kept signature e stack 24 v child Apart Pushed) as AtPush.
 pose proof (digits_kept signature e stack 24 s (machine q) Apart Kept) as D.
 assert (Inputs:forall j i,(j<8)%nat -> (i<5)%nat -> args j i=digits signature e s j i /\ args j (5+i)%nat=digits signature e s j i).
 { intros j i J I;unfold args,DecoderProduct.arguments.
   rewrite (proj2(Nat.leb_gt 5 i) ltac:(lia)),(proj2(Nat.leb_le 5 (5+i)) ltac:(lia)),
     (proj2(Nat.ltb_lt (5+i) 10) ltac:(lia));cbn [andb].
   split;[symmetry;apply Data;assumption|].
   replace (5+i-5)%nat with i by lia;unfold DecoderProduct.rhs_at,digits;rewrite V8.
   change (digits signature e child j i=digits signature e v j i);exact (AtPush j i J I). }
 assert (C:forall j i,(i<4)%nat -> args j (28+i)%nat=DecoderFrame.constant i).
 { intros j i I;unfold args,DecoderProduct.arguments;rewrite (proj2(Nat.ltb_ge (28+i) 10) ltac:(lia)),andb_false_r;apply Constants,I. }
 exists q;split;[unfold square,then_run,set_rhs;fold o;rewrite Lea;exact Call|].
 split.
 2:{ intros x [X _];apply Kept,X. }
 split;[exact At|split;[exact Done|split]].
 - unfold frame;split;[rewrite G;exact DI|split;[rewrite G;exact SP|split]].
   + exact (eq_trans ReturnWord Link).
   + split.
     * intros i j I;rewrite YY;destruct ((proj2 NativeProduct.multiplication) no_read no_read (args j) (args j)
       ltac:(reflexivity)) as [_ High];rewrite High by lia;apply C,I.
     * eapply keep_caller;[exact Caller| |].
       -- intros r InReg;rewrite G;change (Instructions.put (regs s) 8 (address signature e) r=regs s r);
          unfold Instructions.put;destruct (Nat.eqb_spec 8 r);[subst;unfold caller_reg in InReg;cbn in InReg;lia|reflexivity].
       -- intros x X;apply Kept,Live,X.
 - split;intros j J;destruct(Raw j J) as [B [Y Sign]].
   + split;[intros i I;rewrite D by assumption;apply B,I|split].
     * rewrite <-Y;apply limbs_ext;intros;apply D;assumption.
     * rewrite G;exact Sign.
   + pose proof(NativeProduct.lane_square (args j) (digits signature e s j) (digits_split _ B)
       ltac:(intros i I;apply Inputs;assumption) (C j)) as [Bound [Value Positive]].
     split;[intros i I;rewrite YY;apply Bound,I|split;[|rewrite YY;exact Positive]].
     erewrite limbs_ext;[rewrite <-Y;exact Value|intro i;intros;apply YY].
Qed.

Definition square_input bias p incoming:=bind (save_input bias p incoming) (fun '(q,k)=>
 option_map (fun t=>(t,k)) (square bias q)).
Theorem from_setup signature pol bias e p incoming : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> setup signature pol bias e p ->
 exists q k,square_input bias p incoming=Some(q,k) /\ squared signature pol bias e q /\
 preserved (setup_untouched signature pol e) (mem(machine p)) (mem(machine q)).
Proof.
 intros P M Al E;destruct(DecoderSave.from_setup signature _ _ _ _ incoming P M Al E) as [q [k [Setup [Saved [Frame [Data Keep]]]]]].
 destruct(from_saved signature _ _ _ _ P M Saved Frame Data) as [t [Run [Value More]]].
 exists t,k;split;[unfold square_input;rewrite Setup;cbn [bind];now rewrite Run|split;[exact Value|intros x X;now rewrite More,Keep by exact X]].
Qed.
End Iteration.
