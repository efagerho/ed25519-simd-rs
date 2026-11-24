From Coq Require Import ZArith List Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarBytes
 execution.WordSemantics execution.WordBounds execution.VectorProcedure memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.Decode Require Power Kernels DecoderBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderProduct DecoderFrame NativeWords.
Local Open Scope Z_scope.

Lemma ext k op x y a b :
 (forall i,(i<5)%nat -> x i=a i) -> (forall i,(i<5)%nat -> y i=b i) ->
 forall i,Power.apply_kernel k op x y i=Power.apply_kernel k op a b i.
Proof.
 intros X Y;apply Instructions.run_ext;[reflexivity|].
 intro n;unfold Power.feed;destruct(Kernels.constant n);[reflexivity|].
 destruct(Nat.ltb_spec n 5);[apply X;lia|];destruct(Nat.ltb_spec n 10);[apply Y;lia|reflexivity].
Qed.

(* The multiply entry loads five rows through R8 after the CALL push. Its
   operand is the caller's live memory, including when it is on the stack. *)
Definition constants s:=forall i j,(i<4)%nat -> vectors s j (28+i)%nat=DecoderFrame.constant i.
Record result pol bias e pc p q : Prop:=Result {
 at_return:ip q=base bias+(pc+5);
 write_log:accounted e (writable e) q;
 machine_words:well_formed(machine q);
 registers:forall r,regs(machine q) r=regs(machine p) r;
 frame:preserved (fun x=>~(link_slot pol e-24<=x<link_slot pol e)) (mem(machine p)) (mem(machine q));
 constants_after:constants(machine q);
 limbs_after:forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine q) j i=
   Power.apply_kernel DecoderProduct.kernel Kernels.Multiply (vectors(machine p) j)
       (row (machine p) (regs(machine p) 8%nat) j) i
}.

Theorem called pol bias e pc p : placement e -> loaded pol bias (mem e) (writable e) ->
 0<=pc -> pc+5<2984 -> ScalarBytes.decode (skipn (Z.to_nat pc) text)=Some(5%nat,CallRelative(0xa57-(pc+5))) ->
 ip p=base bias+pc -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 4%nat=link_slot pol e -> constants(machine p) ->
 let a:=regs(machine p) 8%nat in a mod 64=0 -> fits64 a 320 ->
 (forall x,a<=x<a+320 -> ~(link_slot pol e-8<=x<link_slot pol e)) ->
 exists q,DecoderProduct.multiply_call bias p=Some q /\ result pol bias e pc p q.
Proof.
 intros P I Pos In Call PC Acc W SP C a Al Fit Sep.
 set (s:=machine p) in *;set (o:=base bias);set (st:=link_slot pol e) in *.
 set (v:=push s (o+(pc+5)));set (args:=DecoderProduct.arguments v).
 pose proof(depth pol e) as Depth;fold st in Depth;destruct(Return.stack_ok _ P) as [[Lo Hi] _].
 assert (R8:regs v 8%nat=a) by reflexivity.
 assert (Need:DecoderProduct.readable args v) by (rewrite <-R8 in Al,Fit;exact (conj Al (conj Fit (fun _ _=>eq_refl)))).
 destruct(DecoderProduct.call_at pol bias e pc args P I Pos In Call p Need PC Acc ltac:(change (sp e-16384+24<=regs s 4%nat<=sp e);rewrite SP;lia))
  as [q [Run [At Safe G Keep Out]]].
 assert (Args:forall j i,(j<8)%nat -> (i<5)%nat ->
  args j i=vectors s j i /\ args j (5+i)%nat=row s a j i).
 { intros j i J N;unfold args,DecoderProduct.arguments.
   rewrite (proj2(Nat.leb_gt 5 i) ltac:(lia)),(proj2(Nat.leb_le 5 (5+i)) ltac:(lia)),
     (proj2(Nat.ltb_lt (5+i) 10) ltac:(lia));cbn [andb];split;[reflexivity|].
   replace (5+i-5)%nat with i by lia;unfold DecoderProduct.rhs_at,row;rewrite R8.
   apply preserved_read with (outside:=fun x=>a<=x<a+320).
   - intros x X;change (store_word (mem s) (word(regs s 4%nat-8)) (o+(pc+5)) x=mem s x).
     rewrite SP,word_fits by (unfold word64;lia);apply write_outside;specialize(Sep x X);lia.
   - intros k B;change (0<=k<8) in B;lia. }
 assert (High:forall i j,(i<4)%nat -> args j (28+i)%nat=DecoderFrame.constant i).
 { intros i j N;unfold args,DecoderProduct.arguments;rewrite (proj2(Nat.ltb_ge (28+i) 10) ltac:(lia)),Bool.andb_false_r;apply C,N. }
 exists q;split;[exact Run|constructor].
 - exact At.
 - exact Safe.
 - exact (proj1(NativeWords.kernels bias) _ _ W Run).
 - exact G.
 - intros x X;apply Keep;change (~(regs s 4%nat-24<=x<regs s 4%nat));now rewrite SP.
 - intros i j N;rewrite (Out j (28+i)%nat).
   destruct((proj2 DecoderProduct.multiplication) no_read no_read (args j) (args j) ltac:(reflexivity)) as [_ Survive].
   rewrite Survive by lia;apply High,N.
 - intros j i J N;rewrite (Out j i);apply DecoderProduct.lane_product;[intros k B;apply Args;assumption|intros k B;apply High,B|exact N].
Qed.
