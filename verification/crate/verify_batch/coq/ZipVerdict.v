From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords
 execution.StoreHistory execution.InstructionRoute execution.MappedFetch execution.WordBounds memory.ByteMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require ZipTorsion.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Zip215).
Local Notation text:=(ScoreSetup.code Zip215).
Definition path:list line:=[(62,3%nat,And32 0 12);(65,3%nat,CopyG 7 13);(68,3%nat,CopyG 6 14);(71,3%nat,CopyG 2 15)].
Lemma image:linked text path.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition intersect bias:=segment (bias+pc) text 4.
Definition execute bias p:=bind (intersect bias p) (ScoreTail.execute Zip215 bias).
Definition verdict e s j:=
 (mem s (Rows.frame e+856+Z.of_nat j)=1 /\ Z.testbit (regs s 0%nat) (Z.of_nat j)=true).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record result bias parent e q:Prop:=Result {
 entry:exists t mask,ScoreTail.entry bias parent e t q mask;
 lane:forall j,(j<8)%nat -> (verdict e (machine q) j <-> signature_accepts Zip215 (HashLayout.row e j));
 flag_byte:forall j,(j<8)%nat -> let b:=mem(machine q) (Rows.frame e+856+Z.of_nat j) in b=0 \/ b=1;
 mask_byte:0<=regs(machine q) 0%nat<256
}.

Theorem checked bias parent e caller p:placement e -> loaded Zip215 bias (mem e) (writable e) ->
 ZipTorsion.result bias parent e caller p -> exists q,execute bias p=Some q /\ result bias parent e q.
Proof.
 intros P I Before;set(s:=machine p);set(o:=bias+pc).
 set(m:=Z.land (regs s 0%nat) (regs s 12%nat) mod 2^32).
 set(v:=set (set (set (with_zf (set s 0 m) (m=?0)) 7 (regs s 13%nat)) 6 (regs s 14%nat)) 2 (regs s 15%nat)).
 assert (Run:run 4 (ScalarBytes.fetch o text) (State(Running 62) s (carry p))=Some(State(Running 74) v (Some false),[])).
 { apply (InstructionRoute.checked _ _ _ image);reflexivity. }
 pose proof(ZipTorsion.writes _ _ _ _ _ Before) as Prior;destruct(mapped_now _ _ _ I _ _ _ Prior (ScoreSetup.image Zip215)) as [Map Sep].
 destruct(at_segment _ _ p o text 4 62 _ _ Prior (ZipTorsion.back _ _ _ _ _ Before) Map Sep Run (Forall_nil _)) as [Step Paid].
 set(t:=LinkedRun.finish o p (State(Running 74) v (Some false),[])) in *.
 assert (Args:ScoreTail.arguments e m (machine t)) by (split;[reflexivity|exact (ZipTorsion.outputs _ _ _ _ _ Before)]).
 assert (Frame:ScoreSaved.frame bias parent e caller (machine t)) by
   (eapply ScoreSaved.keep;[exact (ZipTorsion.frame _ _ _ _ _ Before)|reflexivity|intros x X;reflexivity]).
 destruct(ScoreTail.checked Zip215 bias parent e caller t m P I eq_refl Paid
   (segment_wf _ _ _ _ _ (ZipTorsion.words _ _ _ _ _ Before) Step) Frame Args) as [q [Ret Tail]].
 assert (AX:regs(machine q) 0%nat=m) by exact(proj1(ScoreTail.args _ _ _ _ _ _ Tail)).
 assert (Mem:mem(machine q)=mem s) by exact(ScoreTail.memory _ _ _ _ _ _ Tail).
 pose proof(ZipTorsion.byte _ _ _ _ _ Before) as Byte;fold s in Byte.
 pose proof(EligibleLanes.masked_byte (regs s 12%nat) (regs s 0%nat) Byte) as Lim;rewrite Z.land_comm in Lim.
 exists q;split;[unfold execute,intersect;fold o;rewrite Step;exact Ret|constructor].
 - exists t,m;exact Tail.
 - intros j J;unfold verdict;rewrite Mem,AX;unfold m;rewrite Z.mod_pow2_bits_low,Z.land_spec,andb_true_iff by lia.
   destruct(ZipTorsion.flags _ _ _ _ _ Before j J) as [_ On];fold s in On;rewrite On;split.
   + intros [Eligible [B _]];apply (proj1(ZipTorsion.accepts _ _ _ _ _ Before j J Eligible));exact B.
   + intro Accept;pose proof(Optimized.accepted_eligible _ _ Accept) as Eligible.
     split;[exact Eligible|split;[exact (proj2(ZipTorsion.accepts _ _ _ _ _ Before j J Eligible) Accept)|]].
     apply (proj2(ZipTorsion.valid _ _ _ _ _ Before j J)),(proj2(RootDecision.signed_encoding true e j)).
     exact (proj1(proj2 Eligible)).
 - intros j J;cbv zeta;rewrite Mem;exact (proj1(ZipTorsion.flags _ _ _ _ _ Before j J)).
 - rewrite AX;unfold m;rewrite Z.mod_small by lia;exact Lim.
Qed.
End Iteration.
