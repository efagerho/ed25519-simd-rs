From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.KeyTable Require NativeTable.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require EligibleLanes DecodedKey PrepareOutputs.
Local Open Scope Z_scope.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem input pol bias e d t : placement e -> EligibleLanes.checked_trace pol bias e d t ->
 DecodedRows.geometry false e (TableEntry.point_words e (machine(EligibleLanes.stopped t))).
Proof.
 intros P [D E];pose proof(DecoderReturn.decoded _ _ _ _ _ D) as Pair;pose proof(PairReturn.key_result _ _ _ _ Pair) as Key.
 apply (DecodedRows.keep false e (machine(KeyReturn.returned(PairReturn.key(DecoderReturn.points(EligibleLanes.decoded t))))));
 [|apply (DecodedKey.checked pol bias);assumption].
 intros x X;pose proof(KeySquare.depth pol e);destruct(scratch_stack _ P);
 rewrite (EligibleLanes.memory_after _ _ _ _ _ E);unfold EligibleLanes.store_at,commit;cbn [size address payload];
 rewrite write_outside,(DecoderReturn.memory_after _ _ _ _ _ D);
 try rewrite (FinishTrace.frame _ _ _ _ _ _ (PairReturn.signature_result _ _ _ _ Pair)),(PairReturn.call_memory _ _ _ _ Pair).
 all: try reflexivity;unfold ExtendedPoint.protected,BatchDecode.point,BatchDecode.point_offset,span,Rows.frame,sp,disjoint in *;lia.
Qed.

Definition row e s j d i:=read_word (mem s) (scratch e+PrepareChunk.Caller.table_offset j+160*(8+d)+8*Z.of_nat i).
Definition table e s:=forall j d,(j<8)%nat -> -8<=d<=8 ->
 let v:=row e s j d in (forall i,(i<20)%nat -> 0<=v i<2^52) /\
 forall P,PointEncoding.decodes (BatchDecode.original_encoding false e j) P -> represents_cache (scalar_cache false v) (scale d P).

Lemma keep e s t : preserved (span (TableEntry.tables e) 21760) (mem s) (mem t) -> table e s -> table e t.
Proof.
 intros M Tab j d J D;destruct(Tab j d J D) as [B R];cbv zeta.
 assert (E:forall i,(i<20)%nat -> row e t j d i=row e s j d i).
 { intros i I;unfold row;apply preserved_read with (outside:=span (TableEntry.tables e) 21760);[exact M|].
   intros k K;change (0<=k<8) in K;unfold span,TableEntry.tables,PrepareChunk.Caller.table_offset,PrepareChunk.Caller.tables_offset,PrepareChunk.Caller.table_stride;lia. }
 split;[intros i I;rewrite E by exact I;exact (B i I)|rewrite (NativeTable.cache_ext _ _ E);exact R].
Qed.

Theorem meaning e w s : DecodedRows.geometry false e w -> NativeTable.contents (TableEntry.tables e) w (mem s) -> table e s.
Proof.
 intros [Bounds [_ Seed]] Table j d J D.
 pose proof (NativeTable.signed_entry (TableEntry.tables e) w (mem s) j d Table Bounds J D) as [B R].
 assert (E:forall i,row e s j d i=read_word (mem s) (KeyTable.Audit.slot (TableEntry.tables e) j d i)).
 { intros i;unfold row,KeyTable.Audit.slot,NativeTable.slot,TableEntry.tables,PrepareChunk.Caller.table_offset,
    PrepareChunk.Caller.tables_offset,PrepareChunk.Caller.table_stride;f_equal;ring. }
 split;[intros i I;rewrite E;apply B,I|].
 intros P Dec;rewrite (NativeTable.cache_ext _ _ (fun i _=>E i));apply R,Seed;assumption.
Qed.
End Iteration.
