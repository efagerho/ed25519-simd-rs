From Coq Require Import List ZArith Lia Bool.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.FlatMemory memory.ByteMemory memory.MemoryGeometry.
From Curve25519 Require Import Radix51.
From Curve25519.group Require Import Affine Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.PrepareChunk Require Staging Composition Dispatch Caller.
From Ed25519Simd.PostHash Require Product.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.VerifyBatch Require Import Policy Lane Digest Rows Prepare Hash.
Import ListNotations. Local Open Scope Z_scope.
Module D := Ed25519Simd.Radix16.Audit.
Module F := Ed25519Simd.FullLadder.Audit.

(* Both decoded entries align down after saving six GPRs. The candidate saves
   two more and reserves 520 bytes. K's digits start immediately above the
   reducer's and the ladder's return-address slot. *)
Definition point_addr c := let a:=stack_base c-8-48 in a-a mod 64-1280.
Definition k_addr c := point_addr c-8-16-520.
Definition s_addr c := scratch c+512.
Definition ptrs c := stack_base c+768.
Definition fixed c := regs(entry c) 9%nat.
Definition fallback c := regs(entry c) 8%nat.
Definition full c := negb(strict(mode c)).
Definition reducer c flat := with_words (entry c) (fun r=> match r with
 | 4%nat=>k_addr c-8 | 7%nat=>k_addr c | 6%nat=>stack_base c | _=>regs(entry c) r end) flat.
Definition copy m a n src := write_bytes m a n (fun off=>src(a+off)).
Definition ladder_flat c mid := copy (copy (mem(filter_state c)) (s_addr c) 512 (mem(scalar_out c)))
  (k_addr c) 512 (mem mid).
Definition ladder_with c flat := with_words (entry c) (fun r=> match r with
 | 4%nat=>k_addr c-8 | 7%nat=>point_addr c | 6%nat=>ptrs c | 2%nat=>fixed c
 | 1%nat=>s_addr c | 8%nat=>k_addr c | 9%nat=>FullLadder.Native.bits (full c)
 | _=>regs(entry c) r end) flat.
Definition ladder c mid := ladder_with c (ladder_flat c mid).

Definition table_preserved c a n :=
 disjoint (s_addr c) 512 a n /\ disjoint (k_addr c) 512 a n.
Definition static_preserved c a n :=
 disjoint (ptrs c) 64 a n /\ disjoint (scratch c+3584) 21760 a n /\
 disjoint (stack_base c+512) 256 a n.
Definition possible c a := a=fallback c \/ exists j,(j<8)%nat /\ a=scratch c+3584+2720*Z.of_nat j.

Record buffers c : Prop := {
  digit_buffers : disjoint (s_addr c) 512 (k_addr c) 512;
  pointer_buffer : table_preserved c (ptrs c) 64;
  key_buffer : forall t,possible c t -> table_preserved c t 2720;
  fixed_buffer : table_preserved c (fixed c) (273*120);
  base_private : static_preserved c (fixed c) (273*120);
  identity_private : static_preserved c (fallback c) 2720
}.
Definition static_table e a aff P := forall d,legal_index aff d ->
 let row i:=read_word (mem e) (a+(if aff then 120*(136+d) else 160*(8+d))+8*Z.of_nat i) in
 (forall i,(i<(if aff then 15 else 20))%nat -> 0<=row i<2^52) /\
 represents_cache (scalar_cache aff row) (scale d P).
Definition constants e := static_table e (regs e 9%nat) true generator /\
                          static_table e (regs e 8%nat) false identity.

Lemma selected_possible c j : (j<8)%nat ->
 possible c (Dispatch.selected_ptr (p c) (Composition.decoded(p c)) j).
Proof.
 intro J;unfold Dispatch.selected_ptr;destruct(Dispatch.bit _ _);[right;exists j;split;auto|left;reflexivity].
 unfold Caller.table_offset,Caller.tables_offset,Caller.table_stride,scratch;ring.
Qed.
Local Opaque Composition.decoded Composition.filter_entry Staging.scalar_run.
Lemma preserved_word c mid a n off : table_preserved c a n -> 0<=off -> off+8<=n ->
 read_word (ladder_flat c mid) (a+off) = read_word (mem(filter_state c)) (a+off).
Proof.
 intros [S K] L U;apply Staging.read_block;intros b B. unfold ladder_flat,copy,disjoint in *.
 rewrite !write_outside by lia. reflexivity.
Qed.
Lemma selected_pointer c mid j : Prepare.placement c -> buffers c -> (j<8)%nat ->
 SA.key_table (ladder c mid) j=Dispatch.selected_ptr (p c) (Composition.decoded(p c)) j.
Proof.
 intros P Geom J. change (read_word (ladder_flat c mid) (ptrs c+8*Z.of_nat j)=_)
  || unfold SA.key_table.
 rewrite (preserved_word c mid (ptrs c) 64) by (auto using pointer_buffer;lia).
 apply Composition.pointer_value;[exact (proj1(prepare_placement _ P))|exact J].
Qed.

Lemma static_word c a n off : Prepare.placement c -> ready c=true -> static_preserved c a n ->
 0<=off -> off+8<=n -> read_word (mem(filter_state c)) (a+off)=read_word (mem(entry c)) (a+off).
Proof.
 intros P Ready [Pointers [Tables Rows]] L U.
 destruct (proj2(prepared _ P) Ready) as [_ [[ws [Run [_ [Outside _]]]] _]].
 assert (Ws:Composition.writes=ws) by (unfold Composition.writes;now rewrite Run).
 apply Staging.read_block;intros k K.
 change (FlatMemory.write_bytes (Composition.table_memory (p c) (temp c))
   (ptrs c) 64 (vector_byte (Dispatch.selected_ptr (p c) (Composition.decoded (p c)))) (a+off+k)=mem(entry c)(a+off+k)).
 rewrite write_outside by (unfold disjoint in *;lia).
 unfold Composition.table_memory,KeyTable.Audit.table_view;rewrite Ws,Outside.
 - change (staged_rows (entry c) (first c) (live c) (a+off+k)=mem(entry c)(a+off+k)).
   unfold staged_rows;apply matrix_out;unfold disjoint,stack_base in *;lia.
 - change (a+off+k<scratch c+3584 \/ scratch c+3584+21760<=a+off+k).
   unfold disjoint in *;lia.
Qed.

Lemma row_ext (f g:nat->Z) (aff:bool) : (forall i,(i<(if aff then 15 else 20))%nat -> f i=g i) ->
 scalar_cache aff f=scalar_cache aff g.
Proof.
 intros H;unfold scalar_cache,cache_from_fields;destruct aff;f_equal;
 try match goal with |- Some _=Some _=>f_equal end; apply limbs_ext;intros;apply H;lia.
Qed.

Local Opaque ladder_flat.
Lemma supplied_tables c mid keys : Prepare.placement c -> ready c=true -> buffers c -> constants (entry c) ->
 key_selection c keys -> valid_tables (ladder c mid) generator keys.
Proof.
 intros P On G [Base Id] Keys j aff d J Legal.
 destruct (proj2(prepared _ P) On) as [_ [_ [Built _]]].
 pose proof(selected_pointer c mid j P G J) as Ptr.
 set (t:=Dispatch.selected_ptr (p c) (Composition.decoded (p c)) j) in *.
 assert (Tbl:ptrs c=Staging.selected(p c)) by reflexivity.
 assert (KeyPtr:read_word (mem(filter_state c)) (ptrs c+8*Z.of_nat j)=t)
  by (rewrite Tbl;apply Composition.pointer_value;[exact(proj1(prepare_placement _ P))|exact J]).
 specialize(Keys j J). unfold table_row,table_address.
 destruct aff.
 - specialize(Base d Legal). cbn zeta in *. set (a:=120*(136+d)).
   assert (Eq:forall i,(i<15)%nat ->
     read_word (mem(ladder c mid)) (fixed c+a+8*Z.of_nat i)=
     read_word (mem(entry c)) (fixed c+a+8*Z.of_nat i)).
   { intros i I;change (mem(ladder c mid)) with (ladder_flat c mid).
     replace (fixed c+a+8*Z.of_nat i) with (fixed c+(a+8*Z.of_nat i)) by ring.
     unfold legal_index in Legal; cbn in Legal. unfold a.
     rewrite (preserved_word c mid (fixed c) (273*120)) by (auto using fixed_buffer;lia).
     apply (static_word c (fixed c) (273*120));auto using base_private;lia. }
   change (regs (ladder c mid) 2%nat) with (fixed c);fold a.
   destruct Base as [B R];split;[intros;rewrite Eq by assumption;apply B;assumption|].
   erewrite row_ext with (g:=fun i=>read_word (mem(entry c)) (fixed c+a+8*Z.of_nat i));
    [exact R|exact Eq].
 - change (read_word (ladder_flat c mid) (ptrs c+8*Z.of_nat j)=t) in Ptr. change (mem(ladder c mid)) with (ladder_flat c mid). change (regs(ladder c mid) 6%nat) with (ptrs c). rewrite Ptr. set (a:=160*(8+d)).
   assert (Eq:forall i,(i<20)%nat -> read_word (ladder_flat c mid) (t+a+8*Z.of_nat i)=
       Composition.selected_row (p c) (temp c) (entry c) j d i).
   { intros i I. unfold Composition.selected_row,table_row,table_address.
     change (read_word (ladder_flat c mid) (t+a+8*Z.of_nat i)=
       read_word (mem(filter_state c)) (read_word (mem(filter_state c)) (ptrs c+8*Z.of_nat j)+a+8*Z.of_nat i)).
     rewrite KeyPtr. replace (t+a+8*Z.of_nat i) with (t+(a+8*Z.of_nat i)) by ring.
     apply (preserved_word c mid t 2720);[exact (key_buffer c G t (selected_possible c j J))| |];
       unfold legal_index in Legal;unfold a;lia. }
   assert (Row:(forall i,(i<20)%nat -> 0<=Composition.selected_row (p c) (temp c) (entry c) j d i<2^52) /\
      represents_cache (scalar_cache false (Composition.selected_row (p c) (temp c) (entry c) j d))
         (scale d (keys j))).
   { destruct (Composition.returned_bit (p c) false j) eqn:Dec.
     - apply Built;auto.
     - rewrite Keys. change (Dispatch.bit (Dispatch.key_mask (Composition.decoded(p c))) j=false) in Dec.
       assert (T:t=fallback c) by (unfold t,Dispatch.selected_ptr;rewrite Dec;reflexivity).
       assert (Alias:forall i,(i<20)%nat -> Composition.selected_row (p c) (temp c) (entry c) j d i=
           read_word (mem(entry c)) (fallback c+a+8*Z.of_nat i)).
       { intros i I;unfold Composition.selected_row,table_row,table_address.
         change (read_word (mem(filter_state c)) (read_word (mem(filter_state c)) (ptrs c+8*Z.of_nat j)+a+8*Z.of_nat i)=
           read_word (mem(entry c)) (fallback c+a+8*Z.of_nat i)).
         rewrite KeyPtr,T. replace (fallback c+a+8*Z.of_nat i) with (fallback c+(a+8*Z.of_nat i)) by ring.
         apply (static_word c (fallback c) 2720);auto using identity_private;unfold a,legal_index in *;lia. }
       destruct (Id d Legal) as [B R]. split;[intros;rewrite Alias by assumption;apply B;assumption|].
       erewrite row_ext with (g:=fun i=>read_word (mem(entry c)) (fallback c+a+8*Z.of_nat i));[exact R|exact Alias]. }
   destruct Row as [B R];split;[intros;rewrite Eq by assumption;apply B;assumption|].
   erewrite row_ext with (g:=Composition.selected_row (p c) (temp c) (entry c) j d);[exact R|exact Eq].
Qed.
