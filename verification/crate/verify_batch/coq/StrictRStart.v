From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.MappedFetch execution.ScalarBytes execution.ScalarWords execution.MaskedResult execution.InstructionRoute
 memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require execution.MaskTransfer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require CandidateEntry.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc := (ScoreSetup.callee Dalek).
Local Notation text := (ScoreSetup.code Dalek).
Definition probe:=[LoadLowQ 0 1 0;TestBytes 1 0 0].
Definition combine:list line:=[(58,3%nat,And32 12 0);(61,6%nat,Branch Equal 487)].
Lemma image:assemble 44 probe=Some(firstn 10(skipn 44 text)) /\
 MaskTransfer.encoding (MaskTransfer.ToEax 1)=firstn 4(skipn 54 text) /\ linked text combine.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition execute bias score ks:=let o:=bias+pc in bind (MaskedResult.execute o probe score ks) (fun '(a,k)=>
 bind (MaskTransfer.tick (MaskTransfer.ToEax 1) a k) (fun '(b,k')=>
 option_map (fun t=>(t,k')) (segment o text 2 b))).

Definition selected s ks:=let '(u,k):=(ScalarBytes.vector_dest s 0
  (fun j=>if (j=?0)%nat then read_word (mem s) (word(regs s 1%nat+0)) else 0),ks) in
 set_mask k 1 64 (fun j=>let b:=word_byte (vectors u (j/8)%nat 0%nat) (Z.of_nat (j mod 8)) in negb(Z.land b b=?0)).
Lemma probe_value s ks : exists v,evaluate 0 s ks probe=Some(v,selected s ks) /\ forall o,evaluate o s ks probe=Some(v,selected s ks).
Proof. eexists;split;reflexivity. Qed.
Lemma predicate s ks j : well_formed s -> (j<8)%nat ->
 selected s ks 1%nat j=negb(mem s (regs s 1%nat+Z.of_nat j)=?0).
Proof.
 intros W J;unfold selected,set_mask;cbn [put Nat.eqb ScalarBytes.vector_dest vectors].
 rewrite (proj2(Nat.ltb_lt j 64) ltac:(lia)),(Nat.div_small j 8 J),(Nat.mod_small j 8 J);cbn [Nat.eqb andb].
 rewrite Z.land_diag,Z.add_0_r,(word_fits _ (proj1 W 1%nat)),read_word_byte by (exact (proj2(proj2 W)) || lia);reflexivity.
Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record inputs e s:Prop:=Inputs {
 ptr:regs s 1%nat=Rows.frame e+856;
 rows:forall j,(j<8)%nat -> let b:=mem s (Rows.frame e+856+Z.of_nat j) in
   (b=0 \/ b=1) /\ (b=1 <-> HashLayout.eligible Dalek e j);
 valid:forall j,(j<8)%nat -> Z.testbit (regs s 12%nat) (Z.of_nat j)=true <-> RootDecision.decodes true e j
}.
Lemma from_call bias parent e h r child score : placement e -> ScoreStart.reached Dalek bias parent e h r child score ->
 inputs e (machine score).
Proof.
 intros P Ready;pose proof(CandidateEntry.unchanged _ _ _ _ _ _ _ _ P Ready) as M.
 destruct Ready as [Entry [f [_ [F [_ S]]]]];destruct(ScoreStart.arguments _ _ _ _ _ S) as [_ [Mask [_ [_ [_ [_ [_ CX]]]]]]].
 pose proof(ScoreCall.args _ _ _ _ _ _ _ Entry) as Args;destruct Args as [_ [_ [_ [_ [Flags _]]]]].
 constructor.
 - rewrite CX,(ScoreFrame.gpr _ _ _ _ _ F 1) by discriminate;exact Flags.
 - intros j J;cbv zeta;rewrite M by (right;lia);exact (ScoreCall.lanes _ _ _ _ _ _ _ Entry j J).
 - intros j J;rewrite Mask,(ScoreFrame.gpr _ _ _ _ _ F 2) by discriminate;change 256 with (2^8).
   rewrite Z.mod_pow2_bits_low by lia;exact (ScoreCall.validity _ _ _ _ _ _ _ Entry j J).
Qed.

Definition keep s k:=Z.land (regs s 12%nat) (MaskTransfer.mask16 (k 1%nat)) mod 2^32.
Lemma keep_bits e s ks j : inputs e s -> well_formed s -> (j<8)%nat ->
 Z.testbit (keep s (selected s ks)) (Z.of_nat j)=true <-> HashLayout.eligible Dalek e j.
Proof.
 intros I W J;unfold keep;rewrite Z.mod_pow2_bits_low,Z.land_spec by lia.
 rewrite (proj2(MaskTransfer.kmov_value _) j ltac:(lia)),(predicate _ _ _ W J),(ptr _ _ I).
 destruct(rows _ _ I j J) as [[B|B] On];rewrite B in *;cbn [Z.eqb negb].
 - rewrite andb_false_r;intuition discriminate.
 - rewrite andb_true_r,(valid _ _ I j J);split;[intro;apply On;reflexivity|intro E].
   apply (proj2(RootDecision.signed_encoding true e j));exact (proj1(proj2 E)).
Qed.

Record reached bias e score t:Prop:=Reached {
 address:ip t=bias+pc+67; writes:accounted e (writable e) t; words:well_formed(machine t);
 memory:mem(machine t)=mem(machine score); store_log:log t=log score;
 mask_byte:0<=regs(machine t) 12%nat<256;
 eligible:forall j,(j<8)%nat -> Z.testbit (regs(machine t) 12%nat) (Z.of_nat j)=true <-> HashLayout.eligible Dalek e j;
 unchanged_regs:forall g,g<>0%nat -> g<>12%nat -> regs(machine t) g=regs(machine score) g
}.

Theorem checked bias parent e h r child score ks : placement e -> loaded Dalek bias (mem e) (writable e) ->
 HashLayout.active Dalek e -> ScoreStart.reached Dalek bias parent e h r child score ->
 exists t k,execute bias score ks=Some(t,k) /\ reached bias e score t.
Proof.
 intros P I Live Ready;pose proof(from_call _ _ _ _ _ _ _ P Ready) as Inputs.
 destruct Ready as [_ [f [_ [_ [_ S]]]]];set (s:=machine score);set (o:=bias+pc).
 pose proof(ScoreStart.writes _ _ _ _ _ S) as Acc;pose proof(ScoreStart.words _ _ _ _ _ S) as W.
 destruct(mapped_now _ _ _ I _ _ _ Acc (ScoreSetup.image Dalek)) as [Map Sep].
 destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek))) as [L H];fold o in L,H,Map,Sep;change (o+584<=2^64) in H.
 pose proof(ScoreStart.pc _ _ _ _ _ S) as PC;change (ip score=o+44) in PC.
 destruct(probe_value s ks) as [v [_ Eval]];set (k:=selected s ks).
 destruct(mapped_slice o text e (writable e) score ks 44 10 probe v k L H Map PC Acc W ltac:(change (54<584)%nat;lia)
   (proj1 image) (Eval o)) as [a [A [Apc [V U]]]];change (ip a=o+54) in Apc.
 pose proof(accounted_after _ _ _ _ U) as Paid;pose proof(registers_after _ _ _ _ U) as G;pose proof(memory_after _ _ _ _ U) as M.
 set (m:=MaskTransfer.mask16 (k 1%nat)).
 assert (Read:mapped (mem(machine a)) (ip a) (MaskTransfer.encoding(MaskTransfer.ToEax 1))).
 { rewrite M,Apc;apply MaskTransfer.subimage with (text:=text) (off:=54%nat);[exact Map|change (54+4<=584)%nat;lia|symmetry;exact(proj1(proj2 image))]. }
 set (b:=Cursor (word(ip a+4)) (set (machine a) 0 m) (carry a) (log a)).
 assert (KM:MaskTransfer.tick (MaskTransfer.ToEax 1) a k=Some(b,k)) by exact (MaskTransfer.fetched (MaskTransfer.ToEax 1) a k eq_refl Read).
 assert (At:ip b=o+58) by (change (word(ip a+4)=o+58);rewrite Apc,word_fits by (unfold word64;lia);ring).
 assert (WB:well_formed(machine b)) by (apply set_wf;[exact(words_after _ _ _ _ U)|pose proof(proj1(MaskTransfer.kmov_value (k 1%nat)));unfold m,word64;lia]).
 set (mask:=keep s k).
 assert (NZ:mask<>0).
 { destruct Live as [j [J On]];pose proof(proj2(keep_bits _ _ ks _ Inputs W J) On) as Bit;fold s k mask in Bit;intro Z;rewrite Z,Z.bits_0 in Bit;discriminate. }
 set (last:=with_zf (set (machine b) 12 mask) false).
 assert (Run:run 2 (ScalarBytes.fetch o text) (State(Running 58) (machine b) (carry b))=
   Some(State(Running 67) last (Some false),[])).
 { apply (InstructionRoute.checked _ _ _ (proj2(proj2 image)));cbn [combine follow loc cpu_state cf ScalarBytes.step option_map app
    eval_condition flag with_zf set set_regs with_words put regs machine b Nat.eqb].
   rewrite G;fold s;fold m;change (Z.land (regs s 12%nat) m mod 2^32) with mask;rewrite (proj2(Z.eqb_neq _ _) NZ);reflexivity. }
 destruct(at_segment _ _ b o text 2 58 _ _ Paid At ltac:(change (mapped (mem(machine a)) o text);now rewrite M) Sep Run (Forall_nil _)) as [Step Paid2].
 eexists;exists k;split;[unfold execute;fold o;rewrite A;cbn [bind];rewrite KM;cbn [bind];now rewrite Step|constructor].
 - reflexivity.
 - exact Paid2.
 - exact (segment_wf _ _ _ _ _ WB Step).
 - exact M.
 - change (log a++[]=log score);rewrite app_nil_r;apply (history _ _ _ _ U).
 - change (0<=mask<256);unfold mask,keep;rewrite Z.land_comm.
   assert (B:0<=regs s 12%nat<256) by
    (unfold s;rewrite (proj1(proj2(ScoreStart.arguments _ _ _ _ _ S)));apply Z.mod_pos_bound;lia).
   pose proof(EligibleLanes.masked_byte (MaskTransfer.mask16 (k 1%nat)) _ B);rewrite Z.mod_small by lia;assumption.
 - intros j J;exact (keep_bits _ _ ks _ Inputs W J).
 - intros g A0 A12;change (put (put (regs(machine a)) 0 m) 12 mask g=regs(machine score) g).
   unfold put;rewrite G;destruct(Nat.eqb_spec 12 g), (Nat.eqb_spec 0 g);congruence.
Qed.
End Iteration.
