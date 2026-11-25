From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions isa.VectorMoves execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.Sha512Challenge Require ObjectBytes Output.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require HashLengths.
Import ListNotations. Local Open Scope Z_scope.

Definition callee:=Sha512Challenge.ObjectBytes.address.
Definition path pc:list line:=[(415,8%nat,VectorMove(VectorMoves.Output 0 4 704));(423,4%nat,LeaG 7 (Address 4 None 0));
 (427,7%nat,LeaG 6 (Address 15 None 256));(434,3%nat,CopyG 2 15);(437,8%nat,LeaG 1 (Address 4 None 640));
 (445,8%nat,LeaG 8 (Address 4 None 704));(453,5%nat,CallRelative(callee-(pc+458)))].
Definition bound pc text:=HashLengths.bound text /\ linked text (path pc) /\ (458<List.length text)%nat.
Lemma in_image pol:In (callee,Sha512Challenge.ObjectBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 3 right;left;reflexivity. Qed.
Definition send o text:=segment o text 7.
Definition execute bias pc text p ks:=bind (HashLengths.execute (bias+pc) text p ks) (fun '(a,ak)=>option_map (fun q=>(q,ak)) (send (bias+pc) text a)).
Definition length_store o top s:=vector (word(o+415)) (top+704) (fun j=>vectors s j 0%nat).
Definition link_store o top:=qword (word(o+453)) (top-8) (o+458).

Lemma raw bias pc text s c top dst : linked text (path pc) -> regs s 4%nat=top -> regs s 15%nat=dst ->
 8<=top -> top+768<2^64 -> word64(dst+256) -> word64(bias+callee) ->
 let o:=bias+pc in let len:=length_store o top s in let ret:=link_store o top in
 exists last,run 7 (ScalarBytes.fetch o text) (State(Running 415) s c)=Some(last,[len;ret]) /\
 loc last=Running(callee-pc) /\ regs(cpu_state last) 4%nat=top-8 /\
 regs(cpu_state last) 7%nat=top /\ regs(cpu_state last) 6%nat=dst+256 /\ regs(cpu_state last) 2%nat=dst /\
 regs(cpu_state last) 1%nat=top+640 /\ regs(cpu_state last) 8%nat=top+704 /\
 mem(cpu_state last)=commit (commit (mem s) len) ret.
Proof.
 intros Code SP Scratch L H D Target o len ret;eexists;split;[apply (InstructionRoute.checked _ _ _ Code)|].
 all: cbn [path follow step loc cpu_state cf option_map push push_words regs effective set set_regs with_words mem put Nat.eqb app];rewrite ?SP,?Scratch,?Z.add_0_r.
 all: repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
 all: replace (o+(453+Z.of_nat 5+(callee-(pc+458)))) with (bias+callee) by (unfold o;ring).
 all: rewrite ?(word_fits _ Target);replace (bias+callee-o) with (callee-pc) by (unfold o;ring);repeat split;reflexivity.
Qed.

Record entry bias pc e p q:Prop:=Entry {
 target:ip q=bias+callee; writes:accounted e (writable e) q; words:well_formed(machine q);
 args:let s:=machine q in let t:=Rows.frame e in regs s 4%nat=t-8 /\ regs s 7%nat=t /\ regs s 6%nat=scratch e+256 /\
   regs s 2%nat=scratch e /\ regs s 1%nat=t+640 /\ regs s 8%nat=t+704;
 back:read_word (mem(machine q)) (Rows.frame e-8)=bias+pc+458;
 lengths:forall j,(j<8)%nat -> Sha512Challenge.Output.message_length (machine q) j=HashLengths.length e (machine p) j;
 messages:forall j,(j<8)%nat -> read_word (mem(machine q)) (regs(machine q) 1%nat+8*Z.of_nat j)=
    descriptor (mem e) (regs e 7%nat) (TailCopy.row_index e j) 16;
 other_bytes:preserved (fun x=>~span (Rows.frame e-8) 8 x /\ ~span (Rows.frame e+704) 64 x) (mem(machine p)) (mem(machine q))
}.
Theorem checked pol bias pc text e p ks : bound pc text -> placement e -> loaded pol bias (mem e) (writable e) ->
 MemoryGeometry.fits64 (bias+pc) (Z.of_nat(List.length text)) -> mapped (mem e) (bias+pc) text ->
 (forall x,bias+pc<=x<bias+pc+Z.of_nat(List.length text) -> ~writable e x) ->
 ip p=bias+pc+385 -> regs(machine p) 0%nat=1 -> regs(machine p) 4%nat=Rows.frame e -> regs(machine p) 15%nat=scratch e ->
 accounted e (writable e) p -> well_formed(machine p) -> WrapperInputs.layout e (mem(machine p)) ->
 exists q bank,execute bias pc text p ks=Some(q,bank) /\ entry bias pc e p q.
Proof.
 intros [Lengths [Call Extent]] P I Fit Image Sep PC AX SP DS Acc W Layout;set (o:=bias+pc) in *;set (t:=Rows.frame e) in *.
 destruct(HashLengths.checked o text e p ks Lengths P Fit Image Sep PC AX SP Acc W Layout) as [a [ak [Ready [AP [A V]]]]].
 pose proof(MaskedResult.registers_after _ _ _ _ A) as G;change (regs(machine a)=regs(machine p)) in G.
 pose proof(MaskedResult.memory_after _ _ _ _ A) as M;change (mem(machine a)=mem(machine p)) in M.
 pose proof(MaskedResult.accounted_after _ _ _ _ A) as Paid.
 destruct(stack_ok _ P) as [[L H] _];destruct(scratch_ok _ P) as [[D End] _].
 assert (T:8<=t /\ t+768<2^64) by (unfold t,Rows.frame,sp in *;lia).
 destruct(raw bias pc text (machine a) (LinkedRun.carry a) t (scratch e) Call ltac:(now rewrite G) ltac:(now rewrite G)
    (proj1 T) (proj2 T) ltac:(unfold word64;lia) (mapped_word _ _ _ I _ _ (in_image pol) ltac:(vm_compute;reflexivity)))
   as [last [Run [Next [Stack [DI [SI [DX [CX [R8 Bytes]]]]]]]]];fold o in Run,Bytes.
 set (ws:=[length_store o t (machine a);link_store o t]) in *.
 assert (StoreSafe:confined (writable e) ws).
 { constructor;[intros x X;left;change (t+704<=x<t+704+64) in X|constructor;[intros x X;left;change (t-8<=x<t-8+8) in X|constructor]];
    unfold t,span,Rows.frame,sp in *;lia. }
 destruct(at_segment _ _ a o text 7 415 _ ws Paid AP (image_after e (writable e) a o text Paid Image Sep) Sep Run StoreSafe) as [Sent All].
 assert (Outside:preserved (fun x=>~span (t-8) 8 x /\ ~span (t+704) 64 x) (mem(machine p)) (mem(cpu_state last))).
 { intros x [B K];rewrite Bytes;unfold link_store,length_store,commit;cbn [qword vector address size payload];rewrite !write_outside by (unfold span in *;lia);now rewrite M. }
 eexists;exists ak;split;[unfold execute;fold o;rewrite Ready;cbn [bind];unfold send;now rewrite Sent|constructor].
 - cbn [LinkedRun.finish ip];unfold absolute;rewrite Next;unfold o;ring.
 - exact All.
 - exact (segment_wf _ _ _ _ _ (MaskedResult.words_after _ _ _ _ A) Sent).
 - exact (conj Stack (conj DI (conj SI (conj DX (conj CX R8))))).
 - cbn [LinkedRun.finish machine];rewrite Bytes;apply write_read_word;unfold word64;destruct Fit;change (0<=o+458<2^64);lia.
 - intros j J;unfold Sha512Challenge.Output.message_length;cbn [LinkedRun.finish machine];rewrite R8,Bytes.
   transitivity (read_word (commit (mem(machine a)) (length_store o t (machine a))) (t+704+8*Z.of_nat j)).
   + apply preserved_read with (outside:=fun x=>~span (t-8) 8 x);[intros x X;apply write_outside,X|intros k K;change (0<=k<8) in K;unfold span;lia].
   + rewrite <- (V j J);exact (write_read_vector (mem(machine a)) (t+704) (fun i=>vectors(machine a) i 0%nat) j J (proj1(proj2(MaskedResult.words_after _ _ _ _ A)) j 0%nat J)).
 - intros j J;cbn [LinkedRun.finish machine];rewrite CX;transitivity (read_word (mem(machine p)) (t+640+8*Z.of_nat j));[|exact (WrapperInputs.message _ _ Layout false j J)].
   apply preserved_read with (outside:=fun x=>~span (t-8) 8 x /\ ~span (t+704) 64 x);[exact Outside|].
   intros k K;change (0<=k<8) in K;unfold span;lia.
 - exact Outside.
Qed.
