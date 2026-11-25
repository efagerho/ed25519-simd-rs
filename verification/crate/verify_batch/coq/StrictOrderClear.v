From Coq Require Import ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Curve25519.group Require Import Affine.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictOrderReturn.
Local Open Scope Z_scope.

Definition eligible e j:=StrictRCanonical.eligible e j /\
 exists R,Policy.decodes (BatchDecode.original_encoding true e j) R /\ multiple 8 R<>identity.

Lemma eligible_point e j : StrictRCanonical.eligible e j ->
 exists R,Policy.decodes (BatchDecode.original_encoding true e j) R.
Proof. intros [[_ [Decoded _]] _];exact Decoded. Qed.

Lemma bit_clear e j (live weak:bool) :
 (live=true <-> StrictRCanonical.eligible e j) ->
 (forall R,Policy.decodes (BatchDecode.original_encoding true e j) R -> (weak=true <-> multiple 8 R=identity)) ->
 (live && negb weak=true <-> eligible e j).
Proof.
 intros Lane Order;split.
 - intros Both;apply andb_true_iff in Both as [L U];pose proof(proj1 Lane L) as On;split;[exact On|].
   destruct(eligible_point _ _ On) as [R D];exists R;split;[exact D|intro Bad].
   rewrite (proj2(Order R D) Bad) in U;discriminate.
 - intros [On [R [D Strong]]];apply andb_true_iff;split;[exact (proj2 Lane On)|].
   destruct weak;[exfalso;apply Strong,(proj1(Order R D));reflexivity|reflexivity].
Qed.
Record result bias e p q:Prop:=Result {
 pc:ip q=bias+ScoreSetup.callee Dalek+(if regs(machine q) 12%nat=?0 then 554 else 181);
 writes:accounted e (writable e) q; words:well_formed(machine q);
 memory:mem(machine q)=mem(machine p); history:log q=log p;
 gprs:forall g,g<>0%nat -> g<>12%nat -> regs(machine q) g=regs(machine p) g;
 mask_byte:0<=regs(machine q) 12%nat<256;
 lane:forall j,(j<8)%nat -> (Z.testbit (regs(machine q) 12%nat) (Z.of_nat j)=true <-> eligible e j);
 continues:regs(machine q) 12%nat<>0 <-> exists j,(j<8)%nat /\ eligible e j
}.
Theorem checked bias e y canonical child ret :
 loaded Dalek bias (mem e) (writable e) -> StrictRCanonical.result bias e y canonical ->
 StrictRCall.result e bias canonical child -> StrictOrderReturn.result bias e child ret ->
 exists q,StrictRClear.execute bias ret=Some q /\ result bias e ret q.
Proof.
 intros I C Call R;destruct(StrictRClear.checked true bias e ret I (StrictOrderReturn.address _ _ _ _ R)
    (StrictOrderReturn.writes _ _ _ _ R) (StrictOrderReturn.words _ _ _ _ R)) as [q [Run [Dest [Paid [W [M [Log [Mask K]]]]]]]].
 assert (Old:regs(machine ret) 12%nat=regs(machine canonical) 12%nat).
 { rewrite (StrictOrderReturn.gprs _ _ _ _ R) by discriminate;exact (StrictRCall.mask _ _ _ _ Call). }
 assert (Byte:0<=regs(machine q) 12%nat<256).
 { rewrite Mask,Old;apply StrictRClear.bounded,(StrictRCanonical.mask_byte _ _ _ _ C). }
 assert (Bits:forall j,(j<8)%nat -> (Z.testbit (regs(machine q) 12%nat) (Z.of_nat j)=true <-> eligible e j)).
 { intros j J;rewrite Mask,Old,StrictRClear.bits by exact J.
   apply bit_clear;[exact (StrictRCanonical.lane _ _ _ _ C j J)|intros P Dec;exact (StrictOrderReturn.weak _ _ _ _ R j P J Dec)]. }
 exists q;split;[exact Run|constructor];[rewrite Mask;exact Dest|exact Paid|exact W|exact M|exact Log|exact K|exact Byte|exact Bits|].
 exact (StrictRCanonical.nonempty _ _ Byte Bits).
Qed.
