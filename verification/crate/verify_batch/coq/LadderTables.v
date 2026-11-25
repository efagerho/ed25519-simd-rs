From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.WriteTrace memory.FlatMemory memory.ByteMemory.
From Curve25519.group Require Import Affine PrimeField Decompression.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require LadderEntry Tables.
Local Open Scope Z_scope.

(* Invalid lanes select the read-only identity table. For every decodable
   key the original compressed bytes determine the point uniquely. *)
Definition decoded w :=
 let y:=residue (w mod 2^255) in let sign:=Z.testbit w 255 in
 match decode y sign as v return
  (match v with Some x=>on_curve x y /\ has_sign sign x | None=>forall x,~on_curve x y end -> point) with
 | Some x=>fun H=>Point x y (proj1 H) | None=>fun _=>identity end (decode_correct y sign).
Lemma choice w : Policy.decodes w (decoded w) \/ ((forall P,~Policy.decodes w P) /\ decoded w=identity).
Proof.
 unfold decoded;set (y:=residue (w mod 2^255));generalize(decode_correct y (Z.testbit w 255)).
 destruct(decode y (Z.testbit w 255)) as [x|];intro H.
 - left;split;[reflexivity|apply H].
 - right;split;[|reflexivity];intros P [Y _];apply (H (Affine.x P));unfold y;rewrite <-Y;apply on_edwards.
Qed.
Definition key e j:=decoded (BatchDecode.original_encoding false e j).

Lemma static_now pol bias e t addr len : loaded pol bias (mem e) (writable e) -> accounted e (writable e) t ->
 In (addr,len) static_tables -> forall a,bias+addr<=a -> a+8<=bias+addr+len ->
 read_word (mem(machine t)) a=read_word (mem e) a.
Proof.
 intros I [Safe Replay] Static a Low High;apply preserved_read with (outside:=extent bias addr len).
 - intros x X;rewrite Replay;apply (WriteTrace.frame _ _ Safe);apply (immutable _ _ _ _ I);right;exists addr,len;auto.
 - intros k K;change (0<=k<8) in K;unfold extent;lia.
Qed.

Theorem supplied pol bias e p t : loaded pol bias (mem e) (writable e) -> Tables.mapped e bias -> Candidate.constants e ->
 LadderEntry.entry pol bias e p t -> valid_tables (machine t) generator (key e).
Proof.
 intros I Map [Base Id] E.
 destruct Map as [[Bptr _] [Iptr _]];pose proof(LadderEntry.writes _ _ _ _ _ E) as Paid.
 destruct(LadderEntry.arguments _ _ _ _ _ E) as [_ [_ [Ptr [Barg _]]]].
 pose proof(LadderEntry.operands _ _ _ _ _ E) as Data.
 intros j aff digit J D;unfold table_row,table_address.
 destruct aff.
 - rewrite Barg;specialize(Base digit D);cbv zeta in Base|-*.
   assert (Read:forall i,(i<15)%nat ->
     read_word (mem(machine t)) (regs e 9%nat+120*(136+digit)+8*Z.of_nat i)=
     read_word (mem e) (regs e 9%nat+120*(136+digit)+8*Z.of_nat i)).
   { intros i K;apply (static_now _ _ _ _ BaseTable.address (273*120) I Paid);[left;reflexivity| |];rewrite Bptr;unfold legal_index in D;lia. }
   split;[intros i K;rewrite Read by exact K;apply Base,K|].
   erewrite Candidate.row_ext;[exact (proj2 Base)|exact Read].
 - rewrite Ptr;pose proof(ScoreBuffers.selected _ _ Data j J) as [Local Original].
   set (w:=BatchDecode.original_encoding false e j);destruct(choice w) as [A|[Bad Fallback]].
   + rewrite (Local (proj2(RootDecision.signed_encoding false e j) (ex_intro _ _ A))).
     destruct(ScoreBuffers.table _ _ Data j digit J D) as [Bound R];split;[exact Bound|apply R;exact A].
   + rewrite (Original ltac:(intros Dec;destruct(proj1(RootDecision.signed_encoding false e j) Dec) as [P H];exact (Bad _ H))).
     unfold key;fold w;rewrite Fallback;specialize(Id digit D);cbv zeta in Id|-*.
     assert (Read:forall i,(i<20)%nat ->
       read_word (mem(machine t)) (regs e 8%nat+160*(8+digit)+8*Z.of_nat i)=
       read_word (mem e) (regs e 8%nat+160*(8+digit)+8*Z.of_nat i)).
     { intros i K;apply (static_now _ _ _ _ IdentityTable.address 2720 I Paid);[right;left;reflexivity| |];
       rewrite Iptr;unfold legal_index in D;lia. }
     split;[intros i K;rewrite Read by exact K;apply Id,K|].
     erewrite Candidate.row_ext;[exact (proj2 Id)|exact Read].
Qed.
