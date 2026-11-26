From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls memory.ByteMemory memory.FlatMemory.
From Curve25519 Require Import SignedRadix16 group.Affine group.Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.StageRound Require Program Audit Object ObjectBytes.
From Ed25519Simd.FullLadder Require Import Program.
From Curve25519.group Require Import DoubleScalar.
Import ListNotations. Local Open Scope Z_scope.
Module S := Ed25519Simd.StageRound.Program.
Module SA := Ed25519Simd.StageRound.Audit.
Module SO := Ed25519Simd.StageRound.Object.

Definition digits s (r lane i:nat) := signed_byte (mem s (regs s r+64*Z.of_nat lane+Z.of_nat i)).
Definition digit_list s r j := map (digits s r j) (seq 0 64).
Definition entry_for pad s n :=
 let sp:=regs s 4%nat+staging pad in
 LinkedCalls.set (LinkedCalls.set (LinkedCalls.set s 4 (sp-8)) 7 sp) 9 (Z.of_nat n).
Definition table_address s j (affine:bool) d :=
 if affine then regs s 2%nat+120*(136+d)
 else read_word (mem s) (regs s 6%nat+8*Z.of_nat j)+160*(8+d).
Definition table_row s j aff d (i:nat) := read_word (mem s) (table_address s j aff d+8*Z.of_nat i).
Definition weight s j n k := match k with
 | S.Base=>digits s 1 j (2*n)%nat+16*digits s 1 j (S (2*n))
 | S.Odd=> -digits s 8 j (S (2*n)) | S.Even=> -digits s 8 j (2*n)%nat end.
Definition affine k := match k with S.Base=>true|_=>false end.
Definition operand_point s B A j n k := scale (weight s j n k) (if affine k then B else A j).
Definition legal_index (aff:bool) d := if aff then -136<=d<=136 else -8<=d<=8.
Definition valid_tables s B A := forall j aff d,(j<8)%nat -> legal_index aff d ->
 let a:=table_row s j aff d in
 (forall i,(i<(if aff then 15 else 20))%nat -> 0<=a i<2^52) /\
 represents_cache (scalar_cache aff a) (scale d (if aff then B else A j)).
Definition valid_inputs pc pad s := well_formed s /\
 forall n,(n<32)%nat -> SA.placement pc (Z.of_nat (length Ed25519Simd.StageRound.ObjectBytes.symbol_bytes)) (entry_for pad s n).
Definition staged pc pad s n := let e:=entry_for pad s n in
 buffer_words (mem (snd (S.run pc e))) (regs e 7%nat).
Definition slice (w:nat->Z) row (i:nat) := w (8*row+i)%nat.
Lemma stage_digit pad s n r j p : (r=1%nat \/ r=8%nat) ->
 SA.digit (entry_for pad s n) r j (Z.of_nat p)=digits s r j (2*n+p).
Proof. intros [->| ->];unfold SA.digit,SA.digit_addr,digits;
 change (regs (entry_for pad s n) 9%nat) with (Z.of_nat n);
 rewrite Nat2Z.inj_add,Nat2Z.inj_mul;reflexivity || (unfold entry_for,LinkedCalls.set,set_regs;cbn [regs mem Instructions.put Nat.eqb];f_equal;f_equal;ring).
Qed.
Lemma selected_entry pad s n k j :
 SA.selected (entry_for pad s n) k j=table_address s j (affine k) (weight s j n k).
Proof.
 destruct k;unfold SA.selected,weight,affine,table_address,SA.parity;
 change 1 with (Z.of_nat 1);change 0 with (Z.of_nat 0);
 rewrite !stage_digit by auto;rewrite ?Nat.add_0_r,?Nat.add_1_r;
 unfold SA.key_table;change (regs (entry_for pad s n) 2%nat) with (regs s 2%nat);
 change (regs (entry_for pad s n) 6%nat) with (regs s 6%nat);
 change (mem (entry_for pad s n)) with (mem s);ring.
Qed.
Lemma entry_wf pad s n pc : well_formed s ->
 SA.placement pc (Z.of_nat(length Ed25519Simd.StageRound.ObjectBytes.symbol_bytes)) (entry_for pad s n) ->
 well_formed(entry_for pad s n).
Proof.
 intros W P;pose proof(SA.output_range _ _ _ P) as D;pose proof(SA.return_range _ _ _ P) as [R _];
 pose proof(SA.pair_range _ _ _ P) as N.
 change (MemoryGeometry.fits64 (regs s 4%nat+staging pad) 3520) in D;
 change (MemoryGeometry.fits64 (regs s 4%nat+staging pad-8) 8) in R;change (0<=Z.of_nat n<32) in N.
 unfold entry_for;repeat apply set_wf;try exact W;unfold WordBounds.word64,MemoryGeometry.fits64 in *;lia.
Qed.
Lemma source_limb pc pad s n k i j : valid_inputs pc pad s -> (n<32)%nat ->
 (i<SA.columns k)%nat -> (j<8)%nat ->
 cell (slice (staged pc pad s n) (SA.first_row k)) i j =
 table_row s j (affine k) (weight s j n k) i.
Proof.
 intros [W P] N I J;specialize(P n N).
 pose proof (SA.stage_correct _ SO.assembled_stage_round_correct _ _ P (entry_wf _ _ _ _ W P)) as H.
 cbv zeta in H;destruct (S.run pc (entry_for pad s n)) as [ip t] eqn:Run in H.
 destruct H as [_ [_ [_ [_ [_ [_ [_ [_ H]]]]]]]];specialize(H k i j I J).
 unfold slice,staged,cell,buffer_words,table_row;rewrite Run;cbn [snd].
 change (mem (entry_for pad s n)) with (mem s) in H;rewrite selected_entry in H;rewrite <-H;f_equal;rewrite !Nat2Z.inj_add,!Nat2Z.inj_mul;ring.
Qed.
Lemma valid_weight pc pad s n k j : valid_inputs pc pad s -> (n<32)%nat -> (j<8)%nat ->
 legal_index (affine k) (weight s j n k).
Proof.
 intros [_ P] N J;pose proof (SA.signed_digits _ _ _ (P n N)) as D.
 assert (B:forall r p,(r=1%nat \/ r=8%nat) -> (p<=1)%nat ->
 -8<=digits s r j (2*n+p)<8).
 { intros r p R H;rewrite <-(stage_digit pad s n r j p R);apply D;auto;lia. }
 destruct k;unfold affine,weight,legal_index;
 pose proof(B 1%nat 0%nat ltac:(auto) ltac:(lia));
 pose proof(B 1%nat 1%nat ltac:(auto) ltac:(lia));
 pose proof(B 8%nat 0%nat ltac:(auto) ltac:(lia));
 pose proof(B 8%nat 1%nat ltac:(auto) ltac:(lia));
 rewrite ?Nat.add_0_r,?Nat.add_1_r in *;lia.
Qed.
Lemma from_selected_words s B A n k a : valid_tables s B A ->
 (forall j,(j<8)%nat -> legal_index (affine k) (weight s j n k)) ->
 (forall i j,(i<SA.columns k)%nat -> (j<8)%nat -> cell a i j=table_row s j (affine k) (weight s j n k) i) ->
 cache_bounds (affine k) a /\ forall j,(j<8)%nat ->
 represents_cache (cache_values (affine k) a j) (operand_point s B A j n k).
Proof.
 intros T Index Word;split.
 - intros i j I J;rewrite Word by (destruct k;assumption);apply (proj1(T j _ _ J (Index j J))),I.
 - intros j J;unfold operand_point.
   replace (cache_values (affine k) a j) with (scalar_cache (affine k) (table_row s j (affine k) (weight s j n k))) by
    (unfold scalar_cache,cache_values,cache_from_fields,word_coordinate,field_at;
     destruct k;cbn [affine];f_equal;try match goal with |-Some _=Some _=>f_equal end;
     apply Radix51.limbs_ext;intros i I;symmetry;apply Word;cbn;auto;lia).
   exact (proj2(T j _ _ J (Index j J))).
Qed.
Lemma operand_correct pc pad s B A n k :
 valid_inputs pc pad s -> valid_tables s B A -> (n<32)%nat ->
 let a:=slice (staged pc pad s n) (SA.first_row k) in
 cache_bounds (affine k) a /\ forall j,(j<8)%nat ->
 represents_cache (cache_values (affine k) a j) (operand_point s B A j n k).
Proof.
 intros V T N w;apply from_selected_words;[exact T|intros;apply (valid_weight pc pad);assumption|].
 intros;apply source_limb;assumption.
Qed.
