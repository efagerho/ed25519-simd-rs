From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.MaskedResult
 memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.Decode Require Scale.
From Curve25519 Require Radix51Digits.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterCompare.
Local Open Scope Z_scope.

Definition execute phase bias p ks:=bind (FilterColumns.execute phase bias p ks) (fun '(a,k)=>
 bind (FilterCarry.execute bias a) (fun b=>FilterCompare.execute bias b k)).
Definition matched phase s j:=Radix51Digits.high_test (Scale.reduced (FilterColumns.differences phase s j)) 0.
Lemma same_test a b : (forall i,(i<5)%nat -> a i=b i) ->
 Radix51Digits.high_test (Scale.reduced a) 0=Radix51Digits.high_test (Scale.reduced b) 0.
Proof. intro E;unfold Radix51Digits.high_test,Scale.reduced;now rewrite !E by lia. Qed.

Record result phase bias e p q k:Prop:=Result {
 pc:ip q=bias+FilterLoad.site+(FilterCompare.start phase+34); writes:accounted e (writable e) q; words:well_formed(machine q);
 regs_after:forall r,regs(machine q) r=regs(machine p) r;
 memory_after:preserved (fun x=>~(StrictFilterCall.slot e-16<=x<StrictFilterCall.slot e-8)) (mem(machine p)) (mem(machine q));
 equal_zero:forall j,k 1%nat j=((j<?8)%nat && matched phase (machine p) j)%bool;
 saved_lo:phase=false -> forall j i,(j<8)%nat -> (i<5)%nat -> vectors(machine q) j (15+i)%nat=FilterColumns.cell (machine p) j 0 i;
 high_regs:forall j r,(20<=r)%nat -> vectors(machine q) j r=vectors(machine p) j r
}.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem checked phase bias e p ks : placement e -> loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+FilterLoad.site+Z.of_nat(FilterColumns.offset phase) -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 4%nat=StrictFilterCall.slot e-8 -> FilterCarry.constants(machine p) ->
 exists q k,execute phase bias p ks=Some(q,k) /\ result phase bias e p q k.
Proof.
 intros P I PC Acc W SP C;destruct(FilterColumns.checked _ _ _ _ ks I PC Acc W) as [a [ak [A Col]]].
 pose proof(FilterColumns.state _ _ _ _ _ Col) as U.
 assert (Regs:forall j r,(20<=r)%nat -> vectors(machine a) j r=vectors(machine p) j r)
   by (intros j r High;apply (FilterColumns.prior _ _ _ _ _ Col);unfold FilterColumns.kept;destruct phase;lia).
 assert (CA:FilterCarry.constants(machine a)) by (intros i j N;rewrite Regs by lia;apply C,N).
 assert (SA:regs(machine a) 4%nat=StrictFilterCall.slot e-8) by (now rewrite (registers_after _ _ _ _ U)).
 destruct(FilterCarry.checked _ _ _ _ P I (FilterColumns.pc _ _ _ _ _ Col) (accounted_after _ _ _ _ U) (words_after _ _ _ _ U) SA CA)
  as [b [B Carry]].
 destruct(FilterCompare.checked _ _ _ _ ak I (FilterCarry.pc _ _ _ _ _ Carry) (FilterCarry.writes _ _ _ _ _ Carry)
     (FilterCarry.words _ _ _ _ _ Carry) ltac:(intro j;rewrite (FilterCarry.kept _ _ _ _ _ Carry) by lia;exact (CA 1%nat j ltac:(lia))))
  as [q [k [Z Compare]]].
 exists q,k;split;[unfold execute;rewrite A;cbn [bind];now rewrite B|constructor].
 - exact (FilterCompare.pc _ _ _ _ _ _ Compare).
 - exact (FilterCompare.writes _ _ _ _ _ _ Compare).
 - exact (FilterCompare.words _ _ _ _ _ _ Compare).
 - intro r;rewrite (FilterCompare.registers _ _ _ _ _ _ Compare),(FilterCarry.registers _ _ _ _ _ Carry),(registers_after _ _ _ _ U);reflexivity.
 - intros x X;rewrite (FilterCompare.memory_after _ _ _ _ _ _ Compare),(FilterCarry.memory_after _ _ _ _ _ Carry),(MaskedResult.memory_after _ _ _ _ U);
   [reflexivity|rewrite SA;lia].
 - intro j;rewrite (FilterCompare.equal_zero _ _ _ _ _ _ Compare);destruct(Nat.ltb_spec j 8) as [J|];[|reflexivity].
   cbn [andb];unfold matched;transitivity (Radix51Digits.high_test (Scale.reduced (vectors(machine a) j)) 0).
   + unfold Radix51Digits.high_test;now rewrite !(FilterCarry.reduced _ _ _ _ _ Carry) by lia.
   + apply same_test;intros i N;apply (proj1(FilterColumns.limbs _ _ _ _ _ Col i j N J)).
 - intros -> j i J N;rewrite (FilterCompare.high_regs _ _ _ _ _ _ Compare),(FilterCarry.kept _ _ _ _ _ Carry) by lia;
   exact (proj2(FilterColumns.limbs _ _ _ _ _ Col i j N J) eq_refl).
 - intros j r High;rewrite (FilterCompare.high_regs _ _ _ _ _ _ Compare),(FilterCarry.kept _ _ _ _ _ Carry) by lia;apply Regs,High.
Qed.
End Iteration.
