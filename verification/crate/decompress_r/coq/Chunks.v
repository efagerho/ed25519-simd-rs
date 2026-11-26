From Coq Require Import List ZArith Lia Bool.
From Machine Require Import memory.ByteMemory execution.CircuitFacts execution.MaskTrace.
From Curve25519 Require Import Radix51 Field.
From Curve25519.group Require Import PrimeField Affine Decompression.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Pow2 Require Pow2Caller Linked Pow2Spec.
From Ed25519Simd.Decode Require Import Kernels Power.
From Curve25519 Require Import Radix51Digits.
From Ed25519Simd.Decode Require Import Unpack Decode Glue Caller.
Local Open Scope Z_scope.
Local Opaque Pow2Caller.execute8 Linked.chain.

Definition count (pair:bool) := if pair then 16%nat else 8%nat.
Definition base ptr (second:bool) := if second then ptr+256 else ptr.
Definition power_input k flat ptr second n :=
 slots(prepared k (unpack flat (base ptr second) (n mod 8)%nat) (sign flat (base ptr second) (n mod 8)%nat)) 3%nat (n/8)%nat.
Definition pair_powers k flat ptr :=
 Pow2Caller.execute8 Linked.square_code Linked.multiply_code Linked.chain
 (power_input k flat ptr false) (power_input k flat ptr true) (fun _ _ _=>0).
Definition lane_output k flat ptr pair j :=
 let second:=Nat.leb 8 j in let lane:=(j mod 8)%nat in
 let y:=unpack flat (base ptr second) lane in
 let t:=if pair:bool then fun i=>cell (pair_powers k flat ptr) ((if second then 5 else 0)+i)%nat lane
        else single k (slots(prepared k y (sign flat (base ptr second) lane)) 3%nat) in
 scheduled k y (sign flat (base ptr second) lane) t.
Definition returned k flat ptr pair :=
 mask_word (count pair) (fun j=>if valid(lane_output k flat ptr pair j) then 1 else 0).

Lemma power_input_cell k flat ptr second i j : verified k Multiply=true -> byte_memory flat -> (j<8)%nat ->
 cell (power_input k flat ptr second) i j=uv k (unpack flat (base ptr second) j) i.
Proof.
 intros M B J;unfold cell,power_input. replace ((i*8+j)/8)%nat with i by (apply Nat.div_unique with (r:=j);lia).
 replace ((i*8+j) mod 8)%nat with j by (apply Nat.mod_unique with (q:=i);lia). rewrite prepared_product;auto. exact (proj1(unpack_correct _ _ j B J)).
Qed.

Local Lemma paired_correct k flat ptr : verified k Multiply=true -> byte_memory flat ->
 forall second j, (j<8)%nat ->
 let y:=unpack flat (base ptr second) j in
 let t i:=cell (pair_powers k flat ptr) ((if second then 5 else 0)+i)%nat j in
 squared t /\ value t=power (value(uv k y)) exponent.
Proof.
 intros M Bytes second j J y t.
 assert (B:forall side i lane,(i<5)%nat -> (lane<8)%nat ->
    0<=cell (power_input k flat ptr side) i lane<split).
 { intros side i lane I L. rewrite power_input_cell by auto.
   destruct(unpack_correct flat (base ptr side) lane Bytes L) as [Y _].
   destruct(setup_ok _ _ M Y) as [_ [_ [_ [U _]]]]. specialize (U i I). lia. }
 destruct (Linked.linked_pow2_correct _ _ (fun _ _ _=>0)
   (fun i lane I L=>conj (B false i lane I L) (B true i lane I L)) second j J) as [Bounds Value].
 split.
 - intros i I. specialize(Bounds i I). change (0<=t i<=Pow2Spec.public_bound i) in Bounds.
   clear -Bounds I. destruct i as [|[|[|[|[|i]]]]];try lia;cbn in Bounds |- *;lia.
 - change (pack t mod prime = (field_at (if second then power_input k flat ptr true else power_input k flat ptr false) 0 j ^ Pow2Spec.exponent) mod prime) in Value.
   assert (F:field_at (if second then power_input k flat ptr true else power_input k flat ptr false) 0 j=pack (uv k y)).
   { destruct second;unfold field_at,pack,limbs,y;cbn [Nat.add]; now rewrite !power_input_cell by assumption. }
   rewrite F in Value. unfold value. rewrite <-pow_value by (vm_compute;discriminate).
   apply residue_eq;exact Value.
Qed.

Definition lane_claim k flat ptr pair j :=
 let o:=lane_output k flat ptr pair j in let z:=read_le 32 flat (ptr+32*Z.of_nat j) in
 let x:=value(ox o) in let y:=residue(z mod 2^255) in
 (* Strict consumers distinguish the 19 noncanonical encodings using Y. *)
 (field_bound (fun _=>radix-1) (oy o) /\ pack (oy o)=z mod 2^255) /\
 split_field(ox o) /\ split_field(oy o) /\ split_field(oz o) /\ split_field(ot o) /\
 value(oy o)=y /\ value(oz o)=1%fp /\ value(ot o)=(x*y)%fp /\
 if Z.testbit (returned k flat ptr pair) (Z.of_nat j)
 then on_curve x y /\ has_sign (Z.testbit z 255) x /\
      (forall a,on_curve a y -> has_sign (Z.testbit z 255) a -> a=x)
 else forall a, ~on_curve a y.

Theorem decode_chunks k : verified k Multiply=true -> verified k ChainMultiply=true -> verified k Square=true ->
 forall flat ptr pair, byte_memory flat ->
 0<=returned k flat ptr pair<2^Z.of_nat(count pair) /\
 forall j,(j<count pair)%nat -> lane_claim k flat ptr pair j.
Proof.
 intros M C S flat ptr pair B.
 destruct (mask_word_bits (count pair) (fun j=>if valid(lane_output k flat ptr pair j) then 1 else 0)
  ltac:(intros i I;cbv beta;destruct(valid(lane_output k flat ptr pair i));auto)) as [Range Bits].
 split;[exact Range|]. intros j J. set (second:=Nat.leb 8 j). set (lane:=(j mod 8)%nat).
 assert (L:(lane<8)%nat) by (unfold lane;apply Nat.mod_upper_bound;lia).
 set (ptr':=base ptr second). set (y:=unpack flat ptr' lane).
 destruct(unpack_correct flat ptr' lane B L) as [Y [Val Sign]]. fold y in Y,Val.
 assert (Addr: ptr'+32*Z.of_nat lane=ptr+32*Z.of_nat j).
 { unfold ptr',base,second,lane,count in *. destruct pair;cbn in J;destruct (Nat.leb_spec 8 j); assert (D:=Nat.div_mod j 8 ltac:(lia));assert (R:=Nat.mod_upper_bound j 8 ltac:(lia));lia. }
 unfold encoded in Val,Sign. rewrite Addr in Val,Sign.
 assert (F:output_spec y (sign flat ptr' lane) (lane_output k flat ptr pair j)).
 { unfold lane_output; fold second lane ptr' y. rewrite prepared_product by assumption.
   assert (TP:squared (if pair then fun i=>cell (pair_powers k flat ptr) ((if second then 5 else 0)+i)%nat lane else single k (uv k y))).
   { destruct pair;[exact (proj1(paired_correct _ _ _ M B second lane L))|].
     destruct(setup_ok _ _ M Y) as [_ [_ [_ [UV _]]]];exact(proj1(single_power _ _ C S UV)). }
   rewrite scheduled_finish by assumption. apply finish_correct; auto.
   all: destruct pair.
   - exact (proj2(paired_correct _ _ _ M B second lane L)).
   - destruct (setup_ok _ _ M Y) as [_ [_ [_ [UV _]]]]. destruct(single_power _ _ C S UV) as [_ E].
     apply congruent_value in E. unfold value. rewrite <-pow_value by (vm_compute;discriminate). exact E. }
 unfold output_spec in F. change (residue (pack y)) with (value y) in F.
 assert (Vy:value y=residue (read_le 32 flat (ptr+32*Z.of_nat j) mod 2^255)) by (unfold value;now rewrite Val).
 rewrite Vy,Sign in F. unfold lane_claim. fold (returned k flat ptr pair) in Bits.
 specialize (Bits j J). cbv beta in Bits.
 assert (Eq:Z.testbit (returned k flat ptr pair) (Z.of_nat j)=valid(lane_output k flat ptr pair j)).
 { destruct (valid(lane_output k flat ptr pair j)),
   (Z.testbit (returned k flat ptr pair) (Z.of_nat j)); try reflexivity; exfalso; first [pose proof (proj1 Bits eq_refl);discriminate | pose proof (proj2 Bits eq_refl);discriminate]. }
 rewrite Eq.
 assert (Raw: field_bound (fun _=>radix-1) y /\ pack y = read_le 32 flat (ptr+32*Z.of_nat j) mod 2^255).
 { split;[apply unpack_strict|exact Val]. }
 split;[exact Raw|]. destruct F as [X [Yb [Zb [Tb [Ey [Ez [Et Meaning]]]]]]].
 split;[exact X|]. split;[exact Yb|]. split;[exact Zb|]. split;[exact Tb|].
 split;[exact Ey|]. split;[exact Ez|]. split;[exact Et|].
 destruct (valid(lane_output k flat ptr pair j));[|exact Meaning].
 destruct Meaning as [Curve Sig]. split;[exact Curve|]. split;[exact Sig|].
 intros a A AS; eapply unique_signed_root;eassumption.
Qed.

Definition chunk_mask k flat ptr pair offset :=
 mask_word 8 (fun j=>if valid(lane_output k flat ptr pair ((if Z.eqb offset 0 then 0 else 8)+j)%nat) then 1 else 0).
Lemma combine_masks hi lo : 0<=lo<256 -> Z.lor (Z.shiftl hi 8) lo=256*hi+lo.
Proof.
 intro L. assert (No:Z.land (Z.shiftl hi 8) lo=0).
 { apply Z.bits_inj;intro i; destruct(Z_lt_ge_dec i 0);[rewrite !Z.testbit_neg_r by lia;reflexivity|]. rewrite Z.land_spec,Z.bits_0,Z.shiftl_spec by lia.
   destruct (Z_lt_ge_dec i 8).
   - rewrite Z.testbit_neg_r by lia;reflexivity.
   - replace lo with (lo mod 2^8) by (apply Z.mod_small;exact L).
     rewrite Z.mod_pow2_bits_high,Bool.andb_false_r by lia;reflexivity. }
 pose proof(Z.add_lor_land (Z.shiftl hi 8) lo) as E. rewrite No,Z.add_0_r in E.
 rewrite E,Z.shiftl_mul_pow2 by lia;ring.
Qed.
Local Lemma mask_halves (f:nat->Z) :
 256*mask_word 8 (fun i=>f (8+i)%nat)+mask_word 8 f=mask_word 16 f.
Proof. cbn [mask_word Nat.add Z.of_nat];ring. Qed.
Local Lemma packed_halves (f:nat->bool) :
 let bits j:=if f j then 1 else 0 in
 Z.lor (Z.shiftl (mask_word 8 (fun i=>bits (8+i)%nat)) 8) (mask_word 8 bits)=mask_word 16 bits.
Proof.
 intro bits;rewrite combine_masks;[apply mask_halves|].
 destruct(mask_word_bits 8 bits ltac:(intros i I;unfold bits;destruct(f i);auto)) as [R _];exact R.
Qed.
Local Opaque lane_output.
Lemma returned_by_caller h p k flat ptr pair pad : Caller.caller_result h p pair pad ->
 Caller.return_value h p pair pad (chunk_mask k flat ptr pair)=returned k flat ptr pair.
Proof.
 intro C;rewrite Caller.return_value_ok by exact C. destruct pair;[|reflexivity].
 exact (packed_halves (fun j=>valid(lane_output k flat ptr true j))).
Qed.
