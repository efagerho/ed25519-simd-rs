From Coq Require Import ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.FlatMemory memory.ByteMemory.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Dalek Require Masks.
From Ed25519Simd.DalekPostHash Require Keys Caller.
From Ed25519Simd.FullLadder Require Operands.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519 Require Import Optimized.
From Ed25519Simd.VerifyBatch Require FilterScreen.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Lemma row bias outer e prep p j P d :
 placement e -> PreparedReturn.result Dalek bias outer e prep -> StrictFilterCall.entry bias e prep p ->
 (j<8)%nat -> -8<=d<=8 -> PointEncoding.decodes (BatchDecode.original_encoding false e j) P ->
 let v:=Operands.table_row (FilterRows.view e (machine p)) j false d in
 (forall i,(i<20)%nat -> 0<=v i<2^52) /\ represents_cache (scalar_cache false v) (scale d P).
Proof.
 intros Pl Done Call J D Dec v;pose proof(PreparedReturn.key_tables _ _ _ _ _ Done j d J D) as [Bound Cache].
 assert (Same:preserved (fun x=>~span (StrictFilterCall.slot e) 8 x) (mem(machine prep)) (mem(machine p))) by
   (intros x X;rewrite (StrictFilterCall.memory_after _ _ _ _ Call);apply write_outside,X).
 destruct (PreparedReturn.selected _ _ _ _ _ Done j J) as [Good _].
 assert (A:FilterRows.ptr e (machine p) j=scratch e+PrepareChunk.Caller.table_offset j).
 { rewrite <-Good;[|exists (Affine.x P);destruct Dec as [Y _];unfold RootDecision.decodes;rewrite <-Y;apply on_edwards].
   apply preserved_read with (outside:=fun x=>~span (StrictFilterCall.slot e) 8 x);[exact Same|].
   intros k K;change (0<=k<8) in K;unfold span,PrepareOutputs.dest,StrictFilterCall.slot,BatchScalar.common_top;lia. }
 assert (Eq:forall i,(i<20)%nat -> v i=PreparedTables.row e (machine prep) j d i).
 { intros i N;change (read_word (mem(machine p)) (FilterRows.ptr e (machine p) j+160*(8+d)+8*Z.of_nat i)=PreparedTables.row e (machine prep) j d i);
   rewrite A;apply preserved_read with (outside:=fun x=>~span (StrictFilterCall.slot e) 8 x);[exact Same|].
   intros k K;change (0<=k<8) in K;destruct(scratch_stack _ Pl);unfold span,PrepareChunk.Caller.table_offset,PrepareChunk.Caller.tables_offset,
    PrepareChunk.Caller.table_stride,StrictFilterCall.slot,BatchScalar.common_top,Rows.frame,sp in *;lia. }
 split;[intros i N;rewrite Eq by exact N;apply Bound,N|].
 replace (scalar_cache false v) with (scalar_cache false (PreparedTables.row e (machine prep) j d));[apply Cache,Dec|].
 unfold scalar_cache,cache_from_fields;f_equal;try match goal with |-Some _=Some _=>f_equal end;apply Radix51.limbs_ext;intros;symmetry;apply Eq;lia.
Qed.
Lemma strict_bit s j : (j<8)%nat -> DalekPostHash.Keys.filter_keys s (fun _=>true) j=
 negb(DalekPostHash.Keys.first s j && DalekPostHash.Keys.second s j).
Proof.
 intro J;unfold DalekPostHash.Keys.filter_keys;destruct(Masks.byte (DalekPostHash.Keys.first s)=?0) eqn:E;[|reflexivity].
 apply Z.eqb_eq in E;rewrite <-(Masks.byte_bit (DalekPostHash.Keys.first s) j J),E,Z.bits_0;reflexivity.
Qed.
Theorem weak bias outer e prep p j P : placement e -> PreparedReturn.result Dalek bias outer e prep ->
 StrictFilterCall.entry bias e prep p -> (j<8)%nat -> PointEncoding.decodes (BatchDecode.original_encoding false e j) P ->
 (FilterScreen.weak e (machine p) j=false <-> multiple 8 P<>identity).
Proof.
 intros Pl Done Call J Dec;destruct(row bias outer e prep p j P 8 Pl Done Call J ltac:(lia) Dec) as [B R].
 pose proof(DalekPostHash.Keys.filter_lane_correct (FilterRows.view e (machine p)) P (fun _=>true) j B R J) as Valid.
 rewrite strict_bit,negb_true_iff in Valid by exact J;unfold FilterScreen.weak;tauto.
Qed.

Definition eligible e j:=Optimized.eligible_input Dalek (read_input (mem e) (regs e 7%nat) (BatchWindow.row e j)).
Theorem enabled bias outer e prep p j : placement e -> PreparedReturn.result Dalek bias outer e prep ->
 StrictFilterCall.entry bias e prep p -> (j<8)%nat ->
 (EligibleLanes.candidate e j /\ FilterScreen.weak e (machine p) j=false <-> eligible e j).
Proof.
 intros Pl Done Call J;unfold EligibleLanes.candidate,eligible,Optimized.eligible_input;rewrite !RootDecision.signed_encoding.
 split.
 - intros [[S [[A DA] R]] Strong];split;[exact S|split;[exact R|exists A;split;[exact DA|intros _;apply (proj1(weak _ _ _ _ _ _ _ Pl Done Call J DA)),Strong]]].
 - intros [S [R [A [DA Strong]]]];split;[split;[exact S|split;[exists A;exact DA|exact R]]|].
   apply (proj2(weak _ _ _ _ _ _ _ Pl Done Call J DA)),Strong;reflexivity.
Qed.
End Iteration.
