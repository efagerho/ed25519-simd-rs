From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.WordSemantics
 execution.WordBounds execution.MappedFetch execution.InstructionRoute execution.AlignedRows
 memory.ByteMemory memory.FlatMemory memory.WriteTrace memory.MemoryGeometry abi.CallFrame.
From Curve25519 Require Import Radix51 Field.
From Ed25519Simd.Decode Require Kernels DecoderBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode DecoderSave.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct.
From Machine Require execution.VectorProcedure.
Import ListNotations. Local Open Scope Z_scope.
Definition text:=DecoderFrame.code.
Definition base bias:=bias+DecoderFrame.origin.
Definition enter bias:=segment (base bias) text 2.
Definition rhs bias:=segment (base bias) text 5.
Definition bottom pol e:=DecoderFrame.top (common_top pol e-112)-16.
Definition invoke_lines : list line:=[(497,7%nat,LeaG 8 (Address 7 None 320));(504,5%nat,CallRelative (0xa57-509))].
Lemma image : linked text invoke_lines /\ linked text (AlignedRows.route false 0xa57 5 8 0 5) /\
 ScalarBytes.decode (skipn 0xadd text)=Some(1%nat,Ret).
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition raw e s := forall j,(j<8)%nat -> let y:=digits e s j in
 split_field y /\ limbs y=original_key e j mod 2^255 /\
 Z.testbit (regs s 0%nat) (Z.of_nat j)=Z.testbit (original_key e j) 255.
Definition operands pol bias e p :=
 ip p=base bias+0xa79 /\ accounted e (writable e) p /\
 regs(machine p) 4%nat=bottom pol e /\ read_word(mem(machine p)) (bottom pol e)=base bias+509 /\
 regs(machine p) 7%nat=scratch e+1024 /\
 (forall i j,(i<4)%nat -> vectors(machine p) j (28+i)%nat=DecoderFrame.constant i) /\
 raw e (machine p) /\ forall j i,(j<8)%nat -> (i<5)%nat ->
 vectors(machine p) j i=digits e (machine p) j i /\ vectors(machine p) j (5+i)%nat=digits e (machine p) j i.
Lemma depth pol e : sp e-2048<=bottom pol e<sp e-1000.
Proof. unfold bottom,DecoderFrame.top;pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia));
 unfold common_top,Rows.frame,sp in *;destruct pol;lia. Qed.

Theorem prepare pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 saved bias e p -> frame pol e (machine p) ->
 (forall j i,(j<8)%nat -> (i<5)%nat -> digits e (machine p) j i=vectors(machine p) j i) ->
 exists q, bind (enter bias p) (rhs bias)=Some q /\ operands pol bias e q.
Proof.
 intros P M [PC [Acc [_ Raw]]] [DI [SP Constants]] Data;set (o:=base bias) in *;set (s:=machine p) in *.
 pose proof(depth pol e) as Deep;set (sp1:=bottom pol e) in *.
 destruct(Return.stack_ok _ P) as [[Lo Hi] _];destruct(scratch_ok _ P) as [[SL SH] Al].
 assert (G:forall off,0<=off<2984 -> word64(o+off)).
 { intros off H;destruct(proj1(symbols _ _ _ _ M _ _ (decode_in pol))) as [L U].
   change (0<=o) in L;change (o+2984<=2^64) in U;unfold word64;lia. }
 assert (SP1:regs s 4%nat-8=sp1) by (rewrite SP;unfold sp1,bottom;ring).
 assert (Stack:word(regs s 4%nat-8)=sp1) by (rewrite SP1;apply word_fits;unfold word64;lia).
 assert (Addr:word(regs s 7%nat+0+320)=address e) by (rewrite DI;unfold address;rewrite word_fits by (unfold word64;lia);ring).
 set (v:=push (set s 8 (address e)) (o+509)).
 set (w:=qword (word(o+504)) sp1 (o+509)).
 assert (R:run 2 (ScalarBytes.fetch o text) (State (Running 497) s (carry p))=Some(State (Running 0xa57) v (carry p),[w])).
 { apply (checked _ _ _ (proj1 image));cbn [invoke_lines follow loc cf cpu_state step option_map effective].
   rewrite Addr;change (word(o+(504+Z.of_nat 5+(0xa57-509)))) with (word(o+0xa57)).
   rewrite (word_fits _ (G 0xa57 ltac:(lia)));replace (o+0xa57-o) with 0xa57 by ring.
   change (Some(State (Running 0xa57) v (carry p),[qword (word(o+504)) (word(regs s 4%nat-8)) (o+509)])=Some(State (Running 0xa57) v (carry p),[w]));
   now rewrite Stack. }
 destruct(mapped_now _ _ _ M _ _ _ Acc (decode_in pol)) as [Map Sep].
 assert (W:confined (writable e) [w]) by
   (constructor;[intros x X;change (sp1<=x<sp1+8) in X;left;unfold span;lia|constructor]).
 destruct(at_segment _ _ _ o text _ 497 _ _ Acc PC Map Sep R W) as [Enter Paid].
 set (child:=LinkedRun.finish o p (State (Running 0xa57) v (carry p),[w])) in *.
 assert (S4:regs v 4%nat=sp1) by exact Stack.
 assert (Back:read_word (mem v) sp1=o+509) by (rewrite <- S4;apply pushed_return_word,G;lia).
 assert (Y:forall j i,(j<8)%nat -> (i<5)%nat -> digits e v j i=digits e s j i).
 { intros j i J I;unfold digits;apply preserved_read with (outside:=fun x=>~(sp1<=x<sp1+8)).
   - intros x X;change (store_word (mem s) (word(regs s 4%nat-8)) (o+509) x=mem s x);
     rewrite Stack;apply write_outside,X.
   - intros k K;change (0<=k<8) in K;destruct(scratch_stack _ P);unfold address,disjoint in *;lia. }
 assert (Aligned:address e mod 64=0) by (unfold address;replace 1344 with (21*64) by reflexivity;now rewrite Z.mod_add by lia).
 destruct(loads o text 5 0xa57 5 8 0 (address e) v (carry p) (proj1(proj2 image))
   ltac:(change (address e+0=address e);ring) Aligned ltac:(unfold fits64,address;lia))
    as [t [Load [Reg [Mem [_ [Rows Other]]]]]].
 destruct(mapped_now _ _ _ M _ _ _ Paid (decode_in pol)) as [Live Apart].
 destruct(at_segment _ _ _ o text _ 0xa57 _ _ Paid eq_refl Live Apart Load (Forall_nil _)) as [Next Done].
 eexists;split;[unfold enter,rhs;fold o;rewrite Enter;exact Next|].
 split;[reflexivity|split;[exact Done|]];cbn [LinkedRun.finish machine cpu_state];rewrite Reg,Mem.
 split;[exact S4|split;[exact Back|split;[exact DI|split]]].
 - intros i j I;rewrite Other by lia;apply Constants,I.
 - assert (D:forall j i,(j<8)%nat -> (i<5)%nat -> digits e t j i=digits e s j i).
   { intros j i J I;unfold digits at 1;rewrite Mem;exact (Y j i J I). }
   split.
   + intros j J;destruct(Raw j J) as [Bound [Value Sign]];split;
     [intros i I;rewrite D by assumption;apply Bound,I|split;[rewrite <-Value;apply limbs_ext;intros;apply D;assumption|]].
     change (Z.testbit (regs t 0%nat) (Z.of_nat j)=Z.testbit (original_key e j) 255);rewrite Reg;exact Sign.
   + intros j i J I;split;[rewrite Other,D,Data by lia;reflexivity|].
     rewrite Rows by exact I;unfold digits;now rewrite Mem.
Qed.

Definition square bias p:=bind (DecoderProduct.product bias p) (segment (base bias) text 1).
Definition squared pol bias e p :=
 ip p=base bias+509 /\ accounted e (writable e) p /\
 regs(machine p) 4%nat=bottom pol e+8 /\ regs(machine p) 7%nat=scratch e+1024 /\
 raw e (machine p) /\ forall j,(j<8)%nat -> let y:=original_key e j mod 2^255 in
 let yy:=vectors(machine p) j in field_bound (Kernels.out_bound Kernels.Multiply) yy /\
 represents (limbs yy) (y*y) /\ 2<=yy 0%nat.

Theorem from_operands pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 operands pol bias e p -> exists q,square bias p=Some q /\ squared pol bias e q.
Proof.
 intros P M [PC [Acc [SP [Ret [DI [Constants [Raw Inputs]]]]]]];set (s:=machine p) in *;
 set (o:=base bias) in *;set (stack:=bottom pol e) in *;pose proof(depth pol e) as Deep;fold stack in Deep.
 destruct(Return.stack_ok _ P) as [[Lo Hi] _].
 destruct(DecoderProduct.check_product pol bias e P M p PC Acc
   ltac:(unfold VectorProcedure.room,DecoderProduct.area;cbn [VectorProcedure.bottom VectorProcedure.ceiling];fold s;rewrite SP;lia))
   as [t [Product [At A Reg Keep Value]]].
 assert (Slot:regs(machine t) 4%nat=stack) by (rewrite Reg;exact SP).
 assert (R:read_word (mem(machine t)) stack=o+509).
 { rewrite <-Ret;apply preserved_read with (outside:=fun x=>~(stack-16<=x<stack)).
   - intros x X;apply Keep;fold s;now rewrite SP.
   - intros k K;lia. }
 assert (Fit:word64(o+509)).
 { destruct(proj1(symbols _ _ _ _ M _ _ (decode_in pol))) as [L U].
   change (0<=o) in L;change (o+2984<=2^64) in U;unfold word64;lia. }
 set (v:=LinkedCalls.returning (machine t)).
 assert (Back:run 1 (ScalarBytes.fetch o text) (State (Running 0xadd) (machine t) (carry t))=
    Some(State (Returned (o+509)) v (carry t),[])).
 { cbn [run ScalarBytes.fetch loc cpu_state cf];rewrite (proj2(Z.ltb_ge 0xadd 0) ltac:(lia));change (Z.to_nat 0xadd) with 2781%nat;rewrite (proj2(proj2 image)).
   change (Some(State (Returned (word(read_word (mem(machine t)) (word(regs(machine t) 4%nat))))) v (carry t),@nil store)=Some(State (Returned (o+509)) v (carry t),@nil store)).
   rewrite Slot,(word_fits stack ltac:(unfold word64;lia)),R,(word_fits _ Fit);reflexivity. }
 destruct(mapped_now _ _ _ M _ _ _ A (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text _ 0xadd _ _ A At Map Sep Back (Forall_nil _)) as [Next Done].
 eexists;split;[unfold square;rewrite Product;exact Next|].
 split;[reflexivity|split;[exact Done|split]].
 - change (word(regs(machine t) 4%nat+8)=stack+8);rewrite Slot;apply word_fits;unfold word64;lia.
 - split;[change (regs(machine t) 7%nat=scratch e+1024);rewrite Reg;exact DI|split].
   + intros j J;pose proof(Raw j J) as [B [Y Bits]].
     assert (D:forall i,(i<5)%nat -> digits e v j i=digits e s j i).
     { intros i I;unfold digits;change (read_word (mem(machine t)) (address e+64*Z.of_nat i+8*Z.of_nat j)=
           read_word (mem s) (address e+64*Z.of_nat i+8*Z.of_nat j)).
       apply preserved_read with (outside:=fun x=>~(stack-16<=x<stack)).
       - intros x X;apply Keep;fold s;now rewrite SP.
       - intros k K;change (0<=k<8) in K;unfold address;destruct(scratch_stack _ P);unfold disjoint in *;lia. }
     split;[intros i I;change (0<=digits e v j i<=Radix51.split-1);rewrite D by exact I;apply B,I|split].
     * transitivity (limbs (digits e s j));[apply limbs_ext,D|exact Y].
     * change (Z.testbit (regs(machine t) 0%nat) (Z.of_nat j)=Z.testbit (original_key e j) 255);rewrite Reg;exact Bits.
   + intros j J;destruct(Raw j J) as [B [Y _]].
     pose proof(DecoderProduct.lane_square (vectors s j) (digits e s j) B
       ltac:(intros i I;exact (Inputs j i J I)) ltac:(intros i I;exact (Constants i j I))) as H.
     change (field_bound (Kernels.out_bound Kernels.Multiply) (vectors(machine t) j) /\ represents (limbs(vectors(machine t) j))
       ((original_key e j mod 2^255)*(original_key e j mod 2^255)) /\ 2<=vectors(machine t) j 0%nat).
     rewrite Value,<-Y;exact H.
Qed.

Definition from_key bias p incoming:=bind (key_setup bias p incoming) (fun '(q,k)=>
 bind (bind (enter bias q) (rhs bias)) (fun args=>option_map (fun t=>(t,k)) (square bias args))).
Theorem from_decoder pol bias e p incoming : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> entry pol bias e p ->
 exists q k,from_key bias p incoming=Some(q,k) /\ squared pol bias e q.
Proof.
 intros P M Al E;destruct(DecoderSave.from_decoder _ _ _ _ incoming P M Al E) as [q [k [Setup [Saved [Frame Data]]]]].
 destruct(prepare _ _ _ _ P M Saved Frame Data) as [args [Args Operands]].
 destruct(from_operands _ _ _ _ P M Operands) as [t [Run Value]].
 exists t,k;split;[unfold from_key;rewrite Setup;cbn [bind];rewrite Args;cbn [bind];now rewrite Run|exact Value].
Qed.
