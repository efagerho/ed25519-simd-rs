From Coq Require Import List Bool ZArith Lia.
From Machine Require Import execution.MaskTrace memory.ByteMemory.
From Curve25519 Require Import Radix51 Edwards.
From Curve25519.group Require Import Affine Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Decode Chunks.
From Ed25519Simd.Decode Require Audit Object DecoderBytes HelperBytes.
From Ed25519Simd.Dalek Require Import Batch.
From Ed25519Simd.Dalek Require Audit Object ObjectBytes Schedule Masks.
From Ed25519Simd.SmallOrder Require EntryBytes.
From Ed25519Simd.Torsion Require Audit Object Program ObjectBytes.
From Ed25519Simd.Zip215 Require Import Equation.
Local Open Scope Z_scope.

Definition octet (w:Z) i := Z.shiftr w (8*Z.of_nat i) mod 256.
Lemma octet_bit w i j : (j<8)%nat ->
 Z.testbit(octet w i)(Z.of_nat j)=Z.testbit w (8*Z.of_nat i+Z.of_nat j).
Proof. intro J;unfold octet;change 256 with (2^8).
 rewrite Z.mod_pow2_bits_low,Z.shiftr_spec by lia;f_equal;lia. Qed.

Definition component (o:output) c := match c with
 | O=>ox o | S O=>oy o | S(S O)=>oz o | _=>ot o end.
Definition words (os:nat->output) (w:nat) :=
 let row:=(w/8)%nat in component (os (w mod 8)%nat) (row/5)%nat (row mod 5)%nat.
Lemma word_cell os i j : (j<8)%nat -> cell(words os)i j=
 component (os j) (i/5)%nat (i mod 5)%nat.
Proof.
 intro J;unfold cell,words. replace ((i*8+j)/8)%nat with i by
 (apply Nat.div_unique with (r:=j);lia).
 now replace ((i*8+j) mod 8)%nat with j by (apply Nat.mod_unique with (q:=i);lia).
Qed.
Lemma word_coords os j : (j<8)%nat -> point_values (words os) j=coordinates_of(os j).
Proof.
 intro J. unfold point_values,point_from_fields,word_coordinate,field_at,coordinates_of,Limbs.pack,limbs.
 now rewrite !word_cell by exact J.
Qed.
Definition torsion_run pad q r init := result (program_tree 1500 1032 20 Ed25519Simd.Torsion.Program.code pad)
 (Torsion.Audit.inputs q r) init.
Definition candidate_chunk q Q := strict q /\ forall j,(j<8)%nat ->
 represents_point true (point_values q j) (Q j).

(* AL is ANDed into the low byte of R13D. For a pair the shifted second
   torsion byte and the literal 255 leave that already-checked low byte intact. *)
Definition low_and decode torsion :=
 Z.lor (Z.land decode (Z.lnot 255)) (Z.land (decode mod 256) torsion).
Definition check_bits (paired:bool) decode lo hi :=
 let first:=low_and decode lo in if paired then
 Z.land first (Z.lor (Z.shiftl (hi mod 256) 8) 255) else first.
Lemma check_bits_lane paired decode lo hi high j :
 (j<8)%nat -> (high=true -> paired=true) ->
 let p:=if high then (8+j)%nat else j in
 Z.testbit(check_bits paired decode lo hi)(Z.of_nat p)=
 (Z.testbit decode (Z.of_nat p) && Z.testbit (if high then hi else lo) (Z.of_nat j))%bool.
Proof.
 intros J H. unfold check_bits,low_and;change 255 with (Z.ones 8);change 256 with (2^8).
 destruct high,paired;try (specialize(H eq_refl);discriminate);
 cbn zeta;repeat rewrite ?Z.land_spec,?Z.lor_spec,?Z.lnot_spec,?Z.shiftl_spec by lia;
 repeat first [rewrite Z.ones_spec_low by lia | rewrite Z.ones_spec_high by lia |
  rewrite Z.mod_pow2_bits_low by lia | rewrite Z.mod_pow2_bits_high by lia |
  rewrite Z.testbit_neg_r by lia].
 all: replace (Z.of_nat(8+j)-8) with (Z.of_nat j) by lia;
 rewrite ?Z.mod_pow2_bits_low by lia;repeat match goal with |- context [Z.testbit ?w ?p] => destruct (Z.testbit w p) end;reflexivity.
Qed.

Definition outputs k flat ptr paired high j := Chunks.lane_output k flat ptr paired
 (if high:bool then (8+j)%nat else j).
Definition checked_mask k flat pts enc start (paired:bool) pad init :=
 let ptr:=Batch.ptr enc start in
 let check (high:bool):=let i:=if high then S start else start in
 torsion_run pad (point_words flat pts i) (words(outputs k flat ptr paired high)) (init i) in
 match check false, (if paired then check true else Some 0) with
 | Some lo, Some hi=>Some(check_bits paired (Chunks.returned k flat ptr paired) lo hi)
 | _,_=>None end.
Definition strong_mask flat enc Q (n start:nat) (paired:bool) m :=
 forall high j,(j<8)%nat -> (high=true -> paired=true) ->
 let i:=if high then S start else start in
 (i<n)%nat /\ (Z.testbit m (Z.of_nat(if high then (8+j)%nat else j))=true <->
 accepts (Unpack.encoded flat (Batch.ptr enc i) j) (Q i j)).

Lemma slow_masks : exists k, (forall flat pts enc Q n start (paired:bool) pad init,
 byte_memory flat -> (pad<4)%nat -> (start+(if paired then 2 else 1)<=n)%nat ->
 (forall i,(i<n)%nat -> candidate_chunk(point_words flat pts i)(Q i)) ->
 exists m, checked_mask k flat pts enc start paired pad init=Some m /\
 strong_mask flat enc Q n start paired m) /\
 Ed25519Simd.Decode.Image.kernel_image k DecoderBytes.address DecoderBytes.symbol_bytes
 HelperBytes.address HelperBytes.symbol_bytes.
Proof.
 destruct (Decode.Audit.decoder_projection _ _ _ _ _ _ Decode.Object.assembled_decode_correct)
   as [k [Image [_ [_ [_ Decoder]]]]]. exists k. split;[|exact Image].
 intros flat pts enc Q n start paired pad init B Pad N Points.
 set (ptr:=Batch.ptr enc start).
 destruct (Decoder flat ptr paired pad B Pad) as [_ [_ [_ Lanes]]].
 assert (Call:forall high:bool, (high=true -> paired=true) ->
   let i:=if high then S start else start in let os:=outputs k flat ptr paired high in
   exists m, torsion_run pad (point_words flat pts i)(words os)(init i)=Some m /\
   forall j,(j<8)%nat ->
   (Z.testbit (Chunks.returned k flat ptr paired) (Z.of_nat(if high then (8+j)%nat else j)) &&
    Z.testbit m (Z.of_nat j))%bool=true <-> accepts (Unpack.encoded flat (Batch.ptr enc i) j)(Q i j)).
 { intros high H i os. assert (I:(i<n)%nat) by (unfold i;destruct high,paired;intuition lia).
   assert (J':forall j,(j<8)%nat -> ((if high then 8+j else j)<count paired)%nat).
   { unfold count;destruct high,paired;intuition lia. }
   destruct (Points i I) as [Bound Rep].
   assert (Bounds:Torsion.Audit.input_bounds (point_words flat pts i)(words os)).
   { intros row j R J;split;[apply strict_split;assumption|]. intros _;rewrite word_cell by exact J.
     specialize(Lanes _ (J' j J)). unfold lane_claim in Lanes.
     destruct Lanes as [X [Y [Zr [T _]]]].
     assert (D:(row/5<4)%nat) by (apply Nat.div_lt_upper_bound;lia).
     assert (M:(row mod 5<5)%nat) by (apply Nat.mod_upper_bound;lia).
     unfold os,outputs. destruct (row/5)%nat as [|[|[|[|c]]]];cbn [component];try lia;
     first [specialize(X _ M)|idtac]; specialize(Y _ M);specialize(Zr _ M);specialize(T _ M);unfold Radix51.split in *;lia. }
   destruct(Torsion.Audit.run_correct _ Torsion.Object.assembled_torsion_correct _ _ _ (init i) Pad Bounds)
    as [m [Run [_ Bits]]]. exists m;split;[exact Run|].
   intros j J;apply decoded_accepts with (q:=point_values (point_words flat pts i) j).
   - apply Lanes,J';assumption.
   - unfold Unpack.encoded,ptr,Batch.ptr,i. f_equal. destruct high;lia.
   - apply Rep;exact J.
   - specialize(Bits j J);rewrite word_coords in Bits by assumption;exact Bits. }
 destruct(Call false ltac:(discriminate)) as [lo [Lo LoBits]].
 unfold checked_mask;fold ptr.
 destruct paired.
 - destruct(Call true ltac:(auto)) as [hi [Hi HiBits]].
   rewrite Lo,Hi. eexists;split;[reflexivity|].
   intros high j J H. split;[destruct high;lia|]. rewrite check_bits_lane by auto.
   destruct high;[apply HiBits|apply LoBits];exact J.
 - rewrite Lo. eexists;split;[reflexivity|]. intros high j J H.
   destruct high;[discriminate (H eq_refl)|]. split;[lia|].
   rewrite check_bits_lane with (high:=false) by (auto||discriminate). apply LoBits;auto.
Qed.

Definition exact_run k flat pts enc pad init n :=
 Dalek.Schedule.execute k flat pts enc
 (Dalek.Audit.small_call EntryBytes.address HelperBytes.address flat pts pad init) n.
Lemma fast_masks : exists k, Dalek.Audit.shared_image k DecoderBytes.address DecoderBytes.symbol_bytes
 HelperBytes.address HelperBytes.symbol_bytes /\ forall flat pts enc Q n pad init,
 (n<=8)%nat -> Dalek.Audit.input_layout n pts enc -> byte_memory flat -> (pad<4)%nat ->
 (forall i,(i<n)%nat -> candidate_chunk(point_words flat pts i)(Q i)) ->
 exists m, exact_run k flat pts enc pad init n=Some m /\
 forall i j,(i<n)%nat -> (j<8)%nat -> Z.testbit(octet m i)(Z.of_nat j)=true ->
 accepts (Unpack.encoded flat (Batch.ptr enc i) j)(Q i j).
Proof.
 destruct (Dalek.Audit.recompress_result _ _ _ _ _ _ _ _ Dalek.Object.assembled_dalek_recompress_correct)
 as [k [Img [_ [_ Fast]]]]. exists k;split;[exact Img|]. intros flat pts enc Q n pad init N L B P C.
 assert (Chunks:forall i,(i<n)%nat -> valid_chunk(point_words flat pts i)(Q i)).
 { intros i I;destruct(C i I) as [Bound Rep];split.
   - intros r j R J;apply strict_split;auto;lia.
   - intros j J;exact(proj1(Rep j J)). }
 destruct (Fast n flat pts enc Q pad init N L B P Chunks) as [m [Run [_ Bits]]].
 exists m;split;[exact Run|]. intros i j I J H. rewrite octet_bit in H by exact J.
 apply Bits in H as [E _];auto. apply exact_accepts;assumption.
Qed.
