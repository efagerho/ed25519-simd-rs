From Ed25519Simd.Decode Require NativeProduct.
From Curve25519 Require Radix51Digits.
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordBounds execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.VectorProcedure
 memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Ed25519Simd.Decode Require Decode Kernels Power HelperBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.Decode Require DecoderKernel.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct RowProduct NativeWords.
Import ListNotations. Local Open Scope Z_scope.

Definition literal i:=0xe20+8*Z.of_nat i.
Definition broadcast i:=let pc:=0xa23+10*Z.of_nat i in
 (pc,10%nat,BroadcastRip (5+i) (DecoderFrame.helper+literal i-(DecoderFrame.origin+pc+10))).
Definition prefix:=map broadcast (seq 0 5)++[(0xa55,2%nat,Jump (0xa79-0xa57))].
Lemma code:linked text prefix.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition rhs (s:cpu) j n:=if ((5<=?n)&&(n<?10))%nat then Radix51Digits.sqrt_limbs (n-5)%nat else vectors s j n.
Definition product s t:=forall j i,vectors t j i=Instructions.run no_read (Kernels.product NativeProduct.kernel) (rhs s j) i.
Definition body bias:=then_run (segment (base bias) text 6) (DecoderProduct.product bias).
Definition execute bias:=wrapped (base bias) text (base bias) text (body bias).

Lemma literal_value pol bias e p i : loaded pol bias (mem e) (writable e) -> accounted e (writable e) p ->
 (i<5)%nat -> read_word (mem(machine p)) (word(bias+DecoderFrame.helper+literal i))=Radix51Digits.sqrt_limbs i.
Proof.
 intros I A N;destruct(mapped_now _ _ _ I _ _ _ A (helper_in pol)) as [Map _].
 apply read_literal with (bs:=HelperBytes.symbol_bytes);[exact Map|exact (proj1(symbols _ _ _ _ I _ _ (helper_in pol)))| | |];
 destruct i as [|[|[|[|[|i]]]]];try lia;vm_compute;discriminate || reflexivity.
Qed.

Lemma preload pol bias e p : loaded pol bias (mem e) (writable e) -> accounted e (writable e) p ->
 exists v,run 6 (ScalarBytes.fetch (base bias) text) (State (Running 0xa23) (machine p) (LinkedRun.carry p))=
   Some(State (Running 0xa79) v (LinkedRun.carry p),[]) /\ regs v=regs(machine p) /\ mem v=mem(machine p) /\
   forall j i,vectors v j i=rhs (machine p) j i.
Proof.
 intros I A;set (s:=machine p).
 eexists;split;[apply (checked _ _ _ code);reflexivity|];split;[reflexivity|split;[reflexivity|]].
 intros j i;cbn [prefix map seq app broadcast follow loc cf cpu_state step option_map regs mem vectors].
 assert (Read:forall n,(n<5)%nat -> read_word (mem s)
   (word(base bias+(0xa23+10*Z.of_nat n+10)+(DecoderFrame.helper+literal n-(DecoderFrame.origin+(0xa23+10*Z.of_nat n)+10))))=Radix51Digits.sqrt_limbs n).
 { intros n N;replace (base bias+(0xa23+10*Z.of_nat n+10)+(DecoderFrame.helper+literal n-(DecoderFrame.origin+(0xa23+10*Z.of_nat n)+10)))
    with (bias+DecoderFrame.helper+literal n) by (unfold base;ring);exact (literal_value _ _ _ _ _ I A N). }
 unfold rhs,put;do 10 (destruct i as [|i];[cbn [Nat.eqb Nat.leb Nat.ltb andb Nat.add Nat.sub];first [reflexivity|
    exact (Read 0%nat ltac:(lia))|exact (Read 1%nat ltac:(lia))|exact (Read 2%nat ltac:(lia))|
    exact (Read 3%nat ltac:(lia))|exact (Read 4%nat ltac:(lia))]|]);reflexivity.
Qed.

Lemma inside pol bias e : placement e -> loaded pol bias (mem e) (writable e) ->
 guarded e (writable e) (DecoderProduct.area e) (base bias+0xa23) (base bias+0xadd) 16
   (fun _=>True) product (body bias).
Proof.
 intros P I p _ PC Acc Space;set (o:=base bias) in *.
 destruct(preload _ _ _ _ I Acc) as [v [Run [G [M V]]]].
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 6 0xa23 _ _ Acc PC Map Sep Run (Forall_nil _)) as [Start Paid].
 set (mid:=LinkedRun.finish o p (State (Running 0xa79) v (LinkedRun.carry p),[])) in *.
 destruct(DecoderProduct.check_product _ _ _ P I mid eq_refl Paid
   ltac:(change (room (DecoderProduct.area e) 16 v);unfold room;rewrite G;exact Space))
   as [q [Call [At Safe Reg Keep Out]]].
 exists q;split;[unfold body,then_run;fold o;rewrite Start;exact Call|constructor].
 - exact At.
 - exact Safe.
 - intro r;rewrite Reg;exact (f_equal (fun rs=>rs r) G).
 - intros x X;rewrite Keep;[exact (f_equal (fun m=>m x) M)|change (~(regs v 4%nat-16<=x<regs v 4%nat));now rewrite G].
 - intros j i;rewrite (Out j);apply Instructions.run_ext;[reflexivity|exact (V j)].
Qed.

Theorem called pol bias e : placement e -> loaded pol bias (mem e) (writable e) ->
 guarded e (writable e) (DecoderProduct.area e) (base bias+1119) (base bias+1124) 24
  (fun _=>True) product (execute bias).
Proof.
 intros P I;set (o:=base bias).
 apply (invoke_effect _ _ _ o text 1119 (0xa23-1124) o text 0xadd 16 (fun _=>True) product product).
 - intros s t V;exact V.
 - apply DecoderProduct.stack,P.
 - lia.
 - exact (DecoderProduct.placed _ _ _ I DecoderKernel.Carry).
 - exact (DecoderProduct.placed _ _ _ I DecoderKernel.Carry).
 - lia.
 - vm_compute;reflexivity.
 - lia.
 - vm_compute;reflexivity.
 - replace (o+(1119+5)+(0xa23-1124)) with (o+0xa23) by ring.
   exact (DecoderProduct.address_fits _ _ _ I DecoderKernel.Carry 0xa23 ltac:(change (0<=0xa23<2984);lia)).
 - exact (DecoderProduct.address_fits _ _ _ I DecoderKernel.Carry 1124 ltac:(change (0<=1124<2984);lia)).
 - replace (o+(1119+5)+(0xa23-1124)) with (o+0xa23) by ring;exact (inside _ _ _ P I).
Qed.

Lemma words bias : NativeWords.words(execute bias).
Proof. unfold execute,body,DecoderProduct.product,DecoderProduct.columns,DecoderProduct.native;
 repeat first [apply NativeWords.sequence|apply NativeWords.call|apply NativeWords.block]. Qed.

Lemma multiplied s t : RowProduct.constants s -> product s t ->
 RowProduct.constants t /\ forall j i,(i<5)%nat -> vectors t j i=
 Power.apply_kernel NativeProduct.kernel Kernels.Multiply (vectors s j) Radix51Digits.sqrt_limbs i.
Proof.
 intros C V;split.
 - intros i j N;rewrite (V j (28+i)%nat);destruct((proj2 NativeProduct.multiplication) no_read no_read (rhs s j) (rhs s j) ltac:(reflexivity)) as [_ High].
   rewrite High by lia;unfold rhs;rewrite (proj2(Nat.ltb_ge (28+i) 10) ltac:(lia)),Bool.andb_false_r;apply C,N.
 - intros j i N;rewrite (V j i);apply NativeProduct.lane_product.
   + intros k K;unfold rhs;rewrite (proj2(Nat.leb_gt 5 k) ltac:(lia)),(proj2(Nat.ltb_lt (5+k) 10) ltac:(lia)),
      (proj2(Nat.leb_le 5 (5+k)) ltac:(lia));cbn [andb];replace (5+k-5)%nat with k by lia;auto.
   + intros k K;unfold rhs;rewrite (proj2(Nat.ltb_ge (28+k) 10) ltac:(lia)),Bool.andb_false_r;apply C,K.
   + exact N.
Qed.
