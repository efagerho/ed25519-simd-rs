From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions isa.QwordRegister execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.MemoryGeometry.
From Machine Require execution.MaskedResult execution.MaskTransfer.
From Curve25519 Require Import Radix51.
From Curve25519 Require Radix51Digits.
From Ed25519Simd.Decode Require Scale.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame RootParity RowProduct MaskSegment.
Import ListNotations. Local Open Scope Z_scope.
Module MR:=MaskedResult.
Definition prep:list line:=[(1253,10%nat,BroadcastRip 20 (0xba0-1263));(1263,6%nat,QwordOp(Alu(21%nat,Add 29 29)))].
Definition subs:=map (fun i=>MR.Subtract i 3 (if (i=?0)%nat then 20 else 21) i) (seq 0 5).
Definition execute bias p bank:=bind (RootParity.execute bias p bank) (fun '(r,k)=>
 bind (segment (base bias) text 2 r) (fun t=>MR.execute (base bias) subs t k)).
Lemma images:linked text prep /\ MR.assemble 1269 subs=Some(MaskSegment.bytes 1269 30) /\ length(MaskSegment.bytes 1269 30)=30%nat.
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition bias_low:=2*(radix-19).
Definition bias_high:=Arithmetic.vpaddq (radix-1) (radix-1).
Definition biases s:=vector_dest (vector_dest s 20 (fun _=>bias_low)) 21 (fun j=>Arithmetic.vpaddq (vectors s j 29%nat) (vectors s j 29%nat)).
Definition adjusted s j i:=if RootParity.need_sign s j then Arithmetic.vpsubq
 (if (i=?0)%nat then bias_low else bias_high) (vectors s j i) else vectors s j i.

Lemma apply_sign s bank o : (forall j,vectors s j 29%nat=radix-1) ->
 exists v,MR.evaluate o (biases s) bank subs=Some(v,bank) /\
 (forall j i,(i<5)%nat -> vectors v j i=if bank 3%nat j then Arithmetic.vpsubq
  (if (i=?0)%nat then bias_low else bias_high) (vectors s j i) else vectors s j i) /\
 forall j r,(28<=r)%nat -> vectors v j r=vectors s j r.
Proof.
 intros C;eexists;split;[reflexivity|split].
 - intros j [|[|[|[|[|i]]]]] N;try lia;
   cbn [subs seq map MR.evaluate bind MR.step MR.merge biases vector_dest vectors put Nat.eqb orb];
   rewrite ?(C j);destruct(bank 3%nat j);reflexivity.
 - intros j r H;cbn [subs seq map MR.evaluate bind MR.step MR.merge biases vector_dest vectors put Nat.eqb orb];unfold put.
   do 22 (destruct r as [|r];[lia|]);reflexivity.
Qed.

Theorem checked pol bias e p bank : loaded pol bias (mem e) (writable e) -> ip p=base bias+1163 ->
 accounted e (writable e) p -> well_formed(machine p) -> RowProduct.constants(machine p) ->
 exists q out,execute bias p bank=Some(q,out) /\ ip q=base bias+1299 /\ accounted e (writable e) q /\
 well_formed(machine q) /\ regs(machine q)=regs(machine p) /\ mem(machine q)=mem(machine p) /\ log q=log p /\
 RowProduct.constants(machine q) /\ forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine q) j i=adjusted (machine p) j i.
Proof.
 intros I PC Acc W C;set (o:=base bias) in *;set (s:=machine p) in *.
 destruct(RootParity.checked pol bias e p bank I PC Acc W (fun j=>C 0%nat j ltac:(lia)))
  as [r [k [Parity [At [Paid [WR [RG [RM [RL [Unmoved Signs]]]]]]]]]].
 set (vr:=machine r) in *.
 assert (Mask:forall j,vectors vr j 29%nat=radix-1) by
  (intro j;rewrite Unmoved by discriminate;exact (C 1%nat j ltac:(lia))).
 destruct(mapped_now _ _ _ I _ _ _ Paid (decode_in pol)) as [Map Sep].
 pose proof(read_literal bias DecoderFrame.origin text 0xba0 bias_low (mem vr) Map
    (proj1(symbols _ _ _ _ I _ _ (decode_in pol))) ltac:(lia) ltac:(change (2984<=2984);lia) ltac:(vm_compute;reflexivity)) as Lit.
 assert (Run:run 2 (ScalarBytes.fetch o text) (State (Running 1253) vr (LinkedRun.carry r))=
  Some(State (Running 1269) (biases vr) (LinkedRun.carry r),[])).
 { apply (checked _ _ _ (proj1 images));cbn [prep follow step loc cpu_state qword_op cf option_map bits].
   replace (o+(1253+Z.of_nat 10)+(0xba0-1263)) with (bias+DecoderFrame.origin+0xba0) by (unfold o,base;ring);rewrite Lit;reflexivity. }
 destruct(at_segment _ _ _ o text 2 1253 _ _ Paid At Map Sep Run (Forall_nil _)) as [Start More].
 set (mid:=LinkedRun.finish o r (State (Running 1269) (biases vr) (LinkedRun.carry r),[])) in *.
 pose proof(segment_wf _ _ _ _ _ WR Start) as WM.
 destruct(apply_sign vr k o Mask) as [v [Eval [Digits High]]].
 destruct(MaskSegment.checked pol bias e 1269 30 subs mid k v k I ltac:(lia) ltac:(change (1299<2984);lia)
   (proj2(proj2 images)) (proj1(proj2 images)) eq_refl More WM Eval) as [q [Sub [V [End [Done [WF [G [M Log]]]]]]]].
 exists q,k;split;[unfold execute;fold o;rewrite Parity;cbn [bind];rewrite Start;exact Sub|split;[exact End|split;[exact Done|split;[exact WF|]]]].
 split;[rewrite G;exact RG|split;[rewrite M;exact RM|split]].
 - rewrite Log;change (log r++[]=log p);now rewrite app_nil_r.
 - split.
   + intros i j N;rewrite V,High,Unmoved by lia;apply C,N.
   + intros j i J N;rewrite V,(Digits j i N),Signs,Unmoved by lia;reflexivity.
Qed.

Lemma sign_math s j : Radix51Digits.bounded (vectors s j) -> forall i,(i<5)%nat ->
 adjusted s j i=if xorb (Radix51Digits.canonical_odd (vectors s j)) (Z.testbit (regs s 9%nat) (Z.of_nat j))
 then Radix51Digits.neg_digits (vectors s j) i else vectors s j i.
Proof.
 intros B i N;unfold adjusted,RootParity.need_sign;rewrite Scale.parity_after_ok by exact B.
 destruct(xorb _ _);[|reflexivity].
 pose proof (f_equal (fun h=>h i) (Scale.native_neg_ok _ B)) as Neg.
 change (Scale.native_neg (vectors s j) i=Radix51Digits.finite (Radix51Digits.neg_digits (vectors s j)) i) in Neg.
 unfold Scale.native_neg in Neg;now rewrite !Radix51Digits.finite_at in Neg by exact N.
Qed.
