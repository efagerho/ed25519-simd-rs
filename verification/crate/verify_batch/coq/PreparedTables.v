From Coq Require Import ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.KeyTable Require Correct.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require EligibleLanes DecodedKey TableContents PrepareOutputs.
Local Open Scope Z_scope.

Theorem input pol bias e d t : placement e -> EligibleLanes.checked_trace pol bias e d t ->
 DecodedRows.geometry false e (TableRowMeaning.point e (machine(EligibleLanes.stopped t))).
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
 forall P,Policy.decodes (BatchDecode.original_encoding false e j) P -> represents_cache (scalar_cache false v) (scale d P).

Lemma stored e s j d sign i: row e s j (if sign:bool then d else -d) i=TableRowMeaning.stored e d sign s j i.
Proof.
 unfold row,TableRowMeaning.stored,TablePackRows.row,TableMultiple.pos,TableMultiple.neg,TableIdentity.first,TableEntry.tables,
   PrepareChunk.Caller.table_offset,PrepareChunk.Caller.tables_offset,PrepareChunk.Caller.table_stride;destruct sign;f_equal;ring.
Qed.
Lemma cache_ext a b : (forall i,(i<20)%nat -> a i=b i) -> scalar_cache false a=scalar_cache false b.
Proof.
 intro E;unfold scalar_cache,cache_from_fields;f_equal;try match goal with |-Some _=Some _=>f_equal end;
 apply Radix51.limbs_ext;intros;apply E;lia.
Qed.

Lemma keep e s t : preserved (span (TableEntry.tables e) 21760) (mem s) (mem t) -> table e s -> table e t.
Proof.
 intros M Tab j d J D;destruct(Tab j d J D) as [B R];cbv zeta.
 assert (E:forall i,(i<20)%nat -> row e t j d i=row e s j d i).
 { intros i I;unfold row;apply preserved_read with (outside:=span (TableEntry.tables e) 21760);[exact M|].
   intros k K;change (0<=k<8) in K;unfold span,TableEntry.tables,PrepareChunk.Caller.table_offset,PrepareChunk.Caller.tables_offset,PrepareChunk.Caller.table_stride;lia. }
 split;[intros i I;rewrite E by exact I;exact (B i I)|rewrite (cache_ext _ _ E);exact R].
Qed.

Theorem meaning e w s : DecodedRows.geometry false e w -> TableContents.contents e w s -> table e s.
Proof.
 intros [Bound Seed] [Center Rows] j d J D;cbv zeta.
 destruct (Z.eq_dec d 0) as [->|NZ].
 - assert (E:forall i,(i<20)%nat -> row e s j 0 i=KeyTable.Image.identity_word (Z.of_nat i)) by
     (intros i N;rewrite (stored e s j 0 true i);apply Center;assumption).
   split;[intros i N;rewrite E by exact N;do 20 (destruct i as [|i];[vm_compute;easy|]);lia|].
   intros P Dec;rewrite (cache_ext _ _ E);exact KeyTable.Correct.identity_rep.
 - set (k:=Z.abs d);set (sign:=(0<?d)).
   assert (Dg:d=(if sign then k else -k)) by (unfold sign,k;destruct(Z.ltb_spec 0 d);[rewrite Z.abs_eq by lia|rewrite Z.abs_neq by lia];lia).
   assert (Same:forall i,row e s j d i=TableRowMeaning.stored e k sign s j i) by (intro i;rewrite Dg at 1;apply stored).
   destruct(Rows Bound k sign j ltac:(unfold k;lia) J) as [B R].
   split;[intros i I;rewrite Same;apply B,I|].
   intros P Dec;rewrite (cache_ext _ _ (fun i _=>Same i)).
   specialize(R P (Seed j P J Dec));destruct sign;[now rewrite Dg|rewrite Dg;now rewrite <-KeyTable.Correct.negative_scale].
Qed.
