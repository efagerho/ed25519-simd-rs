From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.VectorProcedure
 execution.MappedFetch execution.WordBounds execution.WordSemantics execution.MaskTransfer memory.ByteMemory memory.FlatMemory.
From Machine Require abi.FramePointer.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Limbs.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictAxis StrictMatchState PointCompare.
Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).
Definition arithmetic bias:=then_run (StrictOperands.execute bias) (StrictSeeded.execute bias).
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition claim vertical e (bit:nat->bool):=forall j A R,(j<8)%nat -> HashLayout.eligible Dalek e j ->
 decodes (little_endian(key_bytes(HashLayout.row e j))) A -> decodes (BatchDecode.original_encoding true e j) R ->
 (bit j=true <-> StrictAxis.matches vertical e j A R).

Theorem compute vertical bias parent e caller p:placement e -> loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+pc+StrictOperands.start vertical -> accounted e (writable e) p -> well_formed(machine p) ->
 StrictMatchState.context bias parent e caller (machine p) ->
 exists q,arithmetic bias p=Some q /\ ip q=bias+pc+PointCompare.start(PointCompare.Signature vertical) /\
 accounted e (writable e) q /\ well_formed(machine q) /\ StrictMatchState.context bias parent e caller (machine q) /\
 regs(machine q) 12%nat=regs(machine p) 12%nat /\ claim vertical e (fun j=>Limbs.high_test(vectors(machine q) j) 0).
Proof.
 intros P I PC Acc W Context;destruct(StrictOperands.checked vertical bias e p P I PC
   (StrictMatchState.r_ptr _ _ _ _ _ Context) (StrictMatchState.product _ _ _ _ _ Context) Acc W)
   as [u [Load [At [Paid [Wu [G [M [Inputs High]]]]]]]].
 assert (SP:regs(machine u) 4%nat=ScoreFrame.buffer e) by (rewrite G;exact(StrictMatchState.rsp _ _ _ _ _ Context)).
 assert (Space:room (DecoderProduct.area e) 16 (machine u)).
 { unfold room,DecoderProduct.area;cbn [bottom ceiling];rewrite SP;pose proof(Z.mod_pos_bound (ScoreFrame.top e-48) 64 ltac:(lia)).
   unfold ScoreFrame.buffer,FramePointer.bottom,ScoreFrame.top,Rows.frame,sp in *;lia. }
 destruct(StrictSeeded.checked vertical bias e P I u At Paid Space) as [v [Calc [Finish End Reg Outside Vec]]].
 assert (Constants:forall j,StrictMatchMath.constants(vectors(machine u) j)).
 { intros j i K;rewrite High by lia;apply (StrictMatchState.constants _ _ _ _ _ Context),K. }
 exists v;split;[unfold arithmetic,then_run;now rewrite Load|split;[destruct vertical;exact Finish|split;[exact End|split]]].
 - exact (StrictSeeded.wf _ _ _ Wu Calc).
 - split.
   + apply(StrictMatchState.preserve _ _ _ _ _ _ P Context).
     * intros r _;now rewrite Reg,G.
     * intros x X;rewrite Outside;[now rewrite M|now rewrite SP].
     * intro j;rewrite Vec;apply StrictMatchMath.keeps_constants,Constants.
   + split;[now rewrite Reg,G|intros j A R J On DA DR;rewrite Vec].
     exact (StrictAxis.checked _ _ _ _ _ _ _ J On DA DR (StrictMatchState.operands _ _ _ _ _ Context)
      Inputs (StrictMatchState.constants _ _ _ _ _ Context j) (Constants j)).
Qed.

Definition execute vertical bias p bank:=bind (arithmetic bias p) (fun v=>
 bind (PointCompare.execute (PointCompare.Signature vertical) bias v bank) (fun '(q,k)=>MaskTransfer.tick (ToEax 1) q k)).
Definition finish (vertical:bool):=if vertical then 389 else 549.
Record result vertical bias parent e caller p q:Prop:=Result {
 address:ip q=bias+pc+finish vertical; writes:accounted e (writable e) q; words:well_formed(machine q);
 context:StrictMatchState.context bias parent e caller (machine q);
 active:regs(machine q) 12%nat=regs(machine p) 12%nat; mask_byte:0<=regs(machine q) 0%nat<256;
 coordinates:claim vertical e (fun j=>Z.testbit (regs(machine q) 0%nat) (Z.of_nat j))
}.

Theorem checked vertical bias parent e caller p bank:placement e -> loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+pc+StrictOperands.start vertical -> accounted e (writable e) p -> well_formed(machine p) ->
 StrictMatchState.context bias parent e caller (machine p) ->
 exists q k,execute vertical bias p bank=Some(q,k) /\ result vertical bias parent e caller p q.
Proof.
 intros P I PC Acc W C;destruct(compute _ _ _ _ _ _ P I PC Acc W C) as [v [Calc [At [Paid [Wv [Ctx [Live Match]]]]]]].
 set(site:=PointCompare.Signature vertical);fold site in At.
 assert (Radix:forall j,vectors(machine v) j 29%nat=radix-1) by (intro j;exact(StrictMatchState.constants _ _ _ _ _ Ctx j 1%nat ltac:(lia))).
 destruct(PointCompare.checked site bias e v bank I At Paid Wv Radix) as [u [k [Cmp Q]]].
 set(off:=PointCompare.start site+34);set(o:=bias+pc).
 assert (Loc:ip u=o+off) by exact (PointCompare.pc _ _ _ _ _ _ Q).
 destruct(mapped_now _ _ _ I _ _ _ (PointCompare.writes _ _ _ _ _ _ Q) (ScoreSetup.image Dalek)) as [Map _].
 assert (Read:mapped (mem(machine u)) (ip u) (MaskTransfer.encoding(ToEax 1))).
 { rewrite Loc;destruct vertical;[apply subimage with (text:=text)(off:=385%nat)|apply subimage with (text:=text)(off:=545%nat)];
     first [exact Map|vm_compute;discriminate || reflexivity || lia]. }
 set(m:=mask16(k 1%nat));set(a:=Cursor (word(ip u+4)) (set (machine u) 0 m) (carry u) (log u)).
 assert (Move:MaskTransfer.tick (ToEax 1) u k=Some(a,k)) by exact (MaskTransfer.fetched (ToEax 1) u k eq_refl Read).
 assert (Byte:0<=m<256).
 { apply low_mask_byte;intros j J;rewrite (PointCompare.equal_zero _ _ _ _ _ _ Q),(proj2(Nat.ltb_ge _ _) J);reflexivity. }
 exists a,k;split;[unfold execute;fold site;rewrite Calc;cbn [bind];rewrite Cmp;exact Move|constructor].
 - change (word(ip u+4)=o+finish vertical);rewrite Loc;destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek))) as [L H].
   fold o in L,H;change (o+584<=2^64) in H;destruct vertical;change off with 385 || change off with 545;rewrite word_fits by (unfold word64;lia);unfold finish;ring.
 - exact (PointCompare.writes _ _ _ _ _ _ Q).
 - apply set_wf;[exact (PointCompare.words _ _ _ _ _ _ Q)|unfold word64;lia].
 - apply (StrictMatchState.preserve _ _ _ _ _ _ P Ctx).
   + intros g Kept;change (put (regs(machine u)) 0 m g=regs(machine v) g);rewrite (PointCompare.registers _ _ _ _ _ _ Q).
     unfold put;destruct(Nat.eqb_spec 0 g);[subst;unfold StrictMatchState.kept in Kept;simpl in Kept;intuition discriminate|reflexivity].
   + intros x _;change (mem(machine u) x=mem(machine v) x);now rewrite (PointCompare.memory_after _ _ _ _ _ _ Q).
   + intros j i K;change (vectors(machine u) j (28+i)%nat=DecoderFrame.constant i);
     rewrite (PointCompare.high_regs _ _ _ _ _ _ Q) by lia;apply (StrictMatchState.constants _ _ _ _ _ Ctx),K.
 - change (regs(machine u) 12%nat=regs(machine p) 12%nat);rewrite (PointCompare.registers _ _ _ _ _ _ Q);exact Live.
 - exact Byte.
 - intros j A R J On DA DR;change (Z.testbit m (Z.of_nat j)=true <-> StrictAxis.matches vertical e j A R);unfold m;
   rewrite (proj2(kmov_value _) j ltac:(lia)),(PointCompare.equal_zero _ _ _ _ _ _ Q),(proj2(Nat.ltb_lt _ _) J).
   exact (Match j A R J On DA DR).
Qed.
End Iteration.
