From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions isa.QwordRegister execution.WordSemantics execution.LinkedCalls
 execution.LinkedRun execution.WordBounds execution.ScalarBytes execution.ScalarWords execution.MappedFetch
 execution.InstructionRoute execution.VectorProcedure execution.VectorSpills
 memory.ByteMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require execution.VectorWindow.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Import Scale.
From Curve25519 Require Import Radix51Digits.
From Ed25519Simd.Decode Require HelperBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare SetupTail.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderKernel DecoderProduct.
Import ListNotations. Local Open Scope Z_scope.

Definition prefix:list line:=[(509,10%nat,BroadcastRip 25 (DecoderFrame.helper+0xe18-(DecoderFrame.origin+519)));
 (519,6%nat,QwordOp(Alu(26%nat,Add 25 25)));(525,10%nat,QwordOp(SubRip 5 0 (0xb80-535)))].
Definition halves i:=let src:=if Nat.eqb i 0 then 5%nat else i in let hi:=(15+i)%nat in let lo:=(10+i)%nat in
 [Compute(hi,Xor hi hi);Compute(hi,Madd true src 26);Compute(lo,Mul src 25);Compute(lo,And lo 29)].
Definition difference_row i:=let lo:=(10+i)%nat in
 (if Nat.eqb i 0 then [Compute(i,Add i 30)] else [Compute(lo,Add lo (14+i));Compute(i,Add i 31)])++
 [Spill lo i;Compute(i,Sub i lo)].
Definition actions:=flat_map halves (seq 0 5)++[Compute(10%nat,Madd false 19 28)]++flat_map difference_row (seq 0 5).
Lemma bound : linked text prefix /\ linked text (VectorSpills.route 7 535 actions) /\ forallb (admissible 5) actions=true.
Proof. repeat split;repeat constructor;vm_compute;discriminate || reflexivity. Qed.

Definition feed (h:nat->Z):=put (put (put h 25 121666) 26 (Arithmetic.vpaddq 121666 121666)) 5 (Arithmetic.vpsubq (h 0%nat) 1).
Lemma projection h old : (forall i,(i<4)%nat -> h (28+i)%nat=DecoderFrame.constant i) ->
 forall i,(i<5)%nat -> let out:=fold_left lane actions (View (feed h) old) in
 rows out i=Scale.scaled h i /\ registers out i=Scale.difference h i.
Proof.
 intros C i I;pose proof(C 0%nat ltac:(lia)) as C28;pose proof(C 1%nat ltac:(lia)) as C29;
 pose proof(C 2%nat ltac:(lia)) as C30;pose proof(C 3%nat ltac:(lia)) as C31.
 change (h 28%nat=19) in C28;change (h 29%nat=radix-1) in C29.
 change (h 30%nat=(radix-19)*1024) in C30;change (h 31%nat=(radix-1)*1024) in C31.
 destruct i as [|[|[|[|[|i]]]]];try lia;
 cbv beta iota zeta delta [actions halves difference_row seq flat_map app fold_left lane registers rows
   feed put Nat.eqb bits Scale.scaled Scale.difference Scale.low Scale.high Scale.scale_input Logic.vpxorq Nat.add];
 rewrite !Z.lxor_nilpotent,?C28,?C29,?C30,?C31;split;reflexivity.
Qed.

Lemma read_literal bias a bs off value m : mapped m (bias+a) bs -> fits64 (bias+a) (Z.of_nat(length bs)) ->
 0<=off -> off+8<=Z.of_nat(length bs) -> read_word (fun x=>nth (Z.to_nat x) bs 0) off=value ->
 read_word m (word(bias+a+off))=value.
Proof.
 intros Map [L H] Pos Ext Value;rewrite word_fits by (unfold word64;lia).
 unfold read_word;rewrite (DecoderFrame.literal_read _ _ _ 8 Map off Pos Ext);exact Value.
Qed.

Definition prep s:=vector_dest (vector_dest (vector_dest s 25 (fun _=>121666)) 26
 (fun _=>Arithmetic.vpaddq 121666 121666)) 5 (fun j=>Arithmetic.vpsubq (vectors s j 0%nat) 1).
Lemma initial pol bias e p : loaded pol bias (mem e) (writable e) -> accounted e (writable e) p ->
 run 3 (ScalarBytes.fetch (base bias) text) (State (Running 509) (machine p) (LinkedRun.carry p))=
 Some(State (Running 535) (prep (machine p)) (LinkedRun.carry p),[]).
Proof.
 intros I Acc;set (s:=machine p).
 destruct(mapped_now _ _ _ I _ _ _ Acc (helper_in pol)) as [Helper _].
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Decoder _].
 pose proof(read_literal bias DecoderFrame.helper HelperBytes.symbol_bytes 0xe18 121666 (mem s) Helper
    (proj1(symbols _ _ _ _ I _ _ (helper_in pol))) ltac:(lia) ltac:(vm_compute;discriminate || reflexivity) ltac:(vm_compute;reflexivity)) as Scale.
 pose proof(read_literal bias DecoderFrame.origin text 0xb80 1 (mem s) Decoder
    (proj1(symbols _ _ _ _ I _ _ (decode_in pol))) ltac:(lia) ltac:(vm_compute;discriminate || reflexivity) ltac:(vm_compute;reflexivity)) as One.
 apply (checked _ _ _ (proj1 bound));cbn [prefix follow loc cf cpu_state step qword_op option_map bits vector_dest vectors mem put Nat.eqb app].
 change (509+Z.of_nat 10) with 519;change (519+Z.of_nat 6) with 525;change (525+Z.of_nat 10) with 535.
 replace (base bias+519+(DecoderFrame.helper+0xe18-(DecoderFrame.origin+519))) with (bias+DecoderFrame.helper+0xe18) by (unfold base;ring).
 replace (base bias+535+(0xb80-535)) with (bias+DecoderFrame.origin+0xb80) by (unfold base;ring).
 rewrite Scale,One;reflexivity.
Qed.

Definition row s ptr j i:=read_word (mem s) (ptr+64*Z.of_nat i+8*Z.of_nat j).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem at_scale signature pol bias e p : placement e -> loaded pol bias (mem e) (writable e) ->
 squared signature pol bias e p -> well_formed(machine p) ->
 exists q,step_at bias 43 p=Some q /\ (forall j i,(j<8)%nat -> (i<5)%nat ->
 row (machine q) (point e signature) j i=Scale.scaled (vectors(machine p) j) i /\
 vectors(machine q) j i=Scale.difference (vectors(machine p) j) i) /\
 preserved (fun x=>~(point e signature<=x<point e signature+320)) (mem(machine p)) (mem(machine q)).
Proof.
 intros P M [PC [Acc [[DI [_ [_ [C Env]]]] Rest]]] W.
 set (o:=base bias);set (a:=point e signature) in *;set (s:=machine p) in *.
 pose proof(initial _ _ _ _ M Acc) as Start;fold s o in Start.
 set (mid:=prep s) in *.
 assert (WM:well_formed mid).
 { pose proof(run_steps _ _ _ _ _ _ Start) as Steps.
   assert (F:forall u ws v,ScalarBytes.steps o text u ws v -> well_formed(cpu_state u) -> well_formed(cpu_state v)).
   { intros u ws v S;induction S;intro Before;[exact Before|apply IHS;eapply fetched_wf;eassumption]. }
   exact (F _ _ _ Steps W). }
 destruct(scratch_ok _ P) as [[L H] Align].
 assert (Al:a mod 64=0) by (apply point_aligned,Align).
 assert (Fit:fits64 a 320) by (unfold a,point,point_offset,fits64;destruct signature;lia).
 destruct(VectorWindow.execute o text 7 0 320 a 40 535 779 mid (LinkedRun.carry p) ltac:(vm_compute;reflexivity) DI Al
    ltac:(unfold fits64 in Fit;lia) (proj2 Fit)) as [t [ws [Run [G Safe]]]].
 pose proof(run_append _ 3 _ _ _ Start 40 _ _ Run) as All.
 assert (Bound:confined (writable e) ws).
 { apply Forall_impl with (P:=permits (VectorWindow.interval a 0 320));[|exact Safe].
   intros w V x X;specialize(V x X);right;left;unfold VectorWindow.interval,span,a,point,point_offset in *;destruct signature;lia. }
 destruct(mapped_now _ _ _ M _ _ _ Acc (decode_in pol)) as [Map Away].
 destruct(at_segment _ _ _ o text 43 509 _ _ Acc PC Map Away All Bound) as [Next Paid].
 eexists;split;[exact Next|split].
 2:{ pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)) as Mem.
     change (mem t=WriteTrace.replay (mem s) ws) in Mem;intros x X;change (mem t x=mem s x);rewrite Mem.
     apply (WriteTrace.frame _ _ Safe);unfold VectorWindow.interval;lia. }
 intros j i J I;set (old:=row mid a j).
 pose proof(VectorSpills.execute o text 7 a 5 j actions 535 mid (LinkedRun.carry p) _ ws (View (feed (vectors s j)) old)
   (proj1(proj2 bound)) (proj2(proj2 bound)) J WM DI Al Fit
    ltac:(split;[intro r;reflexivity|intros;reflexivity]) Run) as [Regs Rows].
 destruct(projection (vectors s j) old ltac:(intros k K;apply C,K) i I) as [U Diff].
 split;[rewrite <-U;apply Rows,I|rewrite <-Diff;apply Regs].
Qed.
End Iteration.
