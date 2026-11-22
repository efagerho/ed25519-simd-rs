From Coq Require Import List ZArith Bool Lia Field.
From Coqprime.elliptic Require GZnZ.
From Machine Require Import execution.MaskTrace memory.ByteMemory.
From Curve25519 Require Import Edwards Field Radix51.
From Curve25519.group Require Import PrimeField Affine Cofactor Decompression Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Kernels Decode Limbs Unpack Chunks.
From Ed25519Simd.Decode Require Audit Object DecoderBytes HelperBytes Program.
From Ed25519Simd.SmallOrder Require Audit EntryBytes Object.
From Ed25519Simd.Dalek Require Import FieldOps Encoding Batch Masks.
From Ed25519Simd.PostHash Require Import Lanes.
From Ed25519Simd.DalekPostHash Require Import Caller.
From Ed25519Simd.Zip215 Require Schedule.
Import ListNotations. Local Open Scope Z_scope.
Local Notation val := (GZnZ.val prime).

Definition strict_R w Q := w=compress Q /\ multiple 8 Q<>identity.
Definition match_coord k a z c := high_test (subtract_product k a z c) 0.
Lemma match_ok k a z c : checked k=true -> split_field a -> split_field z -> split_field c ->
 (match_coord k a z c=true <-> (value a*value z)%fp=value c).
Proof.
 intros K A Zr C. destruct (fused_ok _ _ _ _ K A Zr C) as [B [L V]].
 set (h:=subtract_product k a z c) in *.
 assert (Pos:1<pack h).
 { unfold pack,limbs;pose proof(B 1%nat ltac:(lia));pose proof(B 2%nat ltac:(lia));
   pose proof(B 3%nat ltac:(lia));pose proof(B 4%nat ltac:(lia));unfold radix in *;lia. }
 unfold match_coord;fold h;rewrite high_test_correct,congruent_value by (auto || lia).
 change (value h=0%fp <-> (value a*value z)%fp=value c);rewrite V. split;[intro E|intro E;rewrite E;ring].
 replace (value a*value z)%fp with ((value a*value z-value c)+value c)%fp by ring;rewrite E;ring.
Qed.

(* Rust supplies the second eight-point chunk of a paired key/R decode. *)
Definition outputs dk flat ptr j := lane_output dk flat ptr true (8+j)%nat.
Definition valid_mask dk flat ptr := octet (Chunks.returned dk flat ptr true) 1.
Definition order_run os pad init := MaskTrace.result
 (SmallOrder.Audit.run_at EntryBytes.address Ed25519Simd.SmallOrder.HelperBytes.address pad)
 (SmallOrder.Audit.inputs (words os)) init.
Definition mask_and m n := Z.land m n.
Definition mask_clear m n := Z.land m (Z.lnot n).
Definition if_live block live m (rest:Z->option Z) :=
 match next Decoded block (m=?0) false with
 | Some(Local Reject)=>Some 0 | Some(Local l)=>if label_beq l live then rest m else None
 | _=>None end.
Definition coordinate_match k a o q j :=
 let affine:=match a with AxisX=>ox o | AxisY=>oy o end in
 match_coord k affine (coord q 10 j) (coord q (coord_row a) j).
Definition direct k os valid eligible q pad init :=
 if_live Eligible Canonical (mask_and valid (byte eligible)) (fun m=>
 if_live Canonical Weak (mask_clear m (byte(fun j=>noncanonical(oy(os j))))) (fun m=>
 match order_run os pad init with None=>None | Some weak=>
 if_live Weak MatchY (mask_clear m weak) (fun m=>
 if_live MatchY MatchX (mask_and m (byte(fun j=>coordinate_match k AxisY (os j) q j))) (fun m=>
 Some(mask_and m (byte(fun j=>coordinate_match k AxisX (os j) q j))))) end)).
Local Opaque outputs Chunks.returned MaskTrace.result SmallOrder.Audit.run_at.
Lemma mask_result k os valid eligible q pad init weak :
 order_run os pad init=Some weak ->
 let c:=byte(fun j=>noncanonical(oy(os j))) in
 let y:=byte(fun j=>coordinate_match k AxisY (os j) q j) in
 let x:=byte(fun j=>coordinate_match k AxisX (os j) q j) in
 direct k os valid eligible q pad init=
 Some(mask_and(mask_and(mask_clear(mask_clear(mask_and valid (byte eligible)) c)weak)y)x).
Proof.
 intros W c y x;unfold direct;fold c y x;rewrite W.
 assert (Gate:forall m f, let g:=if m=?0 then Some 0 else f m in
   if_live Eligible Canonical m f=g /\ if_live Canonical Weak m f=g /\
   if_live Weak MatchY m f=g /\ if_live MatchY MatchX m f=g).
 { intros m f;unfold if_live;destruct(m=?0);repeat split;reflexivity. }
 repeat first [rewrite (proj1 (Gate _ _))|rewrite (proj1(proj2(Gate _ _)))|
   rewrite (proj1(proj2(proj2(Gate _ _))))|rewrite (proj2(proj2(proj2(Gate _ _))))].
 repeat match goal with |-context[if ?m =? 0 then _ else _] =>
 let E:=fresh in destruct (m=?0) eqn:E;[apply Z.eqb_eq in E;rewrite E;unfold mask_clear,mask_and;cbn [label_beq];now rewrite !Z.land_0_l|] end.
 reflexivity.
Qed.

Lemma lane_exact k dk flat ptr q Q weak j :
 let n:=(8+j)%nat in let o:=outputs dk flat ptr j in
 let ok:=Z.testbit (valid_mask dk flat ptr)(Z.of_nat j) in
 byte_memory flat -> (j<8)%nat -> checked k=true ->
 lane_claim dk flat ptr true n -> valid_chunk q Q ->
 SmallOrder.Audit.lane_result weak j (coordinates_of o) ->
 (ok && negb(noncanonical(oy o)) && negb(Z.testbit weak (Z.of_nat j)) &&
   match_coord k (oy o)(coord q 10 j)(coord q 5 j) &&
   match_coord k (ox o)(coord q 10 j)(coord q 0 j)=true <->
 strict_R (encoded flat (ptr+256) j) (Q j)).
Proof.
 intros n o ok B J K L [Bounds Qs] [_ Weak]. specialize(Qs j J).
 set (w:=encoded flat (ptr+256) j).
 assert (Addr:ptr+32*Z.of_nat n=ptr+256+32*Z.of_nat j) by (unfold n;lia).
 assert (Bit:Z.testbit (Chunks.returned dk flat ptr true) (Z.of_nat n)=ok).
 { unfold ok,valid_mask;rewrite octet_bit by exact J;f_equal;unfold n;lia. }
 unfold lane_claim in L;fold n in L;change (lane_output dk flat ptr true n) with o in L.
 rewrite Addr,Bit in L;change (read_le 32 flat (ptr+256+32*Z.of_nat j)) with w in L.
 destruct L as [[Tight Raw] [X [Y [Zr [T [Ey [Ez [Et Dec]]]]]]]].
 set (fy:=residue(w mod 2^255)) in *. set (fx:=value(ox o)) in *.
 set (z:=value(coord q 10 j)) in *.
 change (z<>0%fp /\ value(coord q 0 j)=(x(Q j)*z)%fp /\
  value(coord q 5 j)=(y(Q j)*z)%fp) in Qs. destruct Qs as [NZ [QX QY]].
 assert (Bound:forall c,(c<=10)%nat -> split_field(coord q c j)).
 { intros c C i I;unfold coord;pose proof(Bounds (c+i)%nat j ltac:(lia) J);lia. }
 rewrite !andb_true_iff,!negb_true_iff,digits_canonical by exact Tight.
 rewrite !match_ok by (assumption || apply Bound;lia). fold fx z. rewrite Raw,Ey,QX,QY.
 assert (Cancel:forall a b:fp,(a*z=b*z)%fp <-> a=b).
 { intros a b;split;[intro E|intros ->;reflexivity].
   replace a with ((a*z)/z)%fp by (field;exact NZ);rewrite E;field;exact NZ. }
 rewrite !Cancel. unfold strict_R;pose proof (encoding_equal flat (ptr+256) j (Q j) B) as Enc;fold w in Enc;rewrite Enc.
 assert (YR:0<=w mod 2^255<2^255) by (apply Z.mod_pos_bound;lia).
 assert (Canon: w mod 2^255<prime -> val fy=w mod 2^255).
 { intro H;change ((w mod 2^255) mod prime=w mod 2^255);apply Z.mod_small;lia. }
 assert (VR:0<=val (y(Q j))<prime) by (rewrite (GZnZ.inZnZ prime (y(Q j)));apply Z.mod_pos_bound;unfold prime;lia).
 assert (FromBytes:w mod 2^255=val (y(Q j)) -> fy=y(Q j)).
 { intro H;unfold fy;rewrite H;destruct (y(Q j)) as [v E];apply GZnZ.zirr;symmetry;exact E. }
 destruct ok.
 - destruct Dec as [Curve [Sign Unique]]. set (R:=Point fx fy Curve).
   assert (Rep:represents_xyz (coordinates_of o) R).
   { change (value(oz o)<>0%fp /\ fx=(fx*value(oz o))%fp /\ value(oy o)=(fy*value(oz o))%fp).
     rewrite Ez,Ey;split;[discriminate|split;ring]. }
   specialize(Weak R Rep).
   split.
   + intros [[[[ _ Can] Strong] yEq] xEq].
     assert (RP:R=Q j) by (apply point_ext;exact(conj xEq yEq)).
     assert (NN:multiple 8 R<>identity) by (intro E;apply Weak in E;congruence).
     split;[split;[rewrite <-yEq;now rewrite Canon|]|congruence].
     unfold has_sign in Sign. destruct Sign as [Zero|Parity];[|congruence].
     exfalso;apply NN,eight_identity_iff. change (fx*fy*(fx*fx+fy*fy)=0)%fp;rewrite Zero;ring.
   + intros [[Bytes SignQ] Strong];assert (yEq:=FromBytes Bytes).
     assert (xEq:x(Q j)=fx).
     { apply Unique;[rewrite yEq;apply on_edwards|right;congruence]. }
     assert (RP:R=Q j) by (apply point_ext;split;[symmetry|];assumption).
     assert (Off:Z.testbit weak (Z.of_nat j)=false) by (destruct (Z.testbit weak (Z.of_nat j)) eqn:H;
       [exfalso;apply Strong;rewrite <-RP;apply Weak;reflexivity|reflexivity]).
     intuition congruence.
 - split;[intuition discriminate|]. intros [[Bytes _] _];exfalso.
   apply (Dec (x(Q j)));rewrite (FromBytes Bytes);apply on_edwards.
Qed.

Definition decoder_runs dk := forall flat ptr,byte_memory flat ->
 forall j,(j<8)%nat -> lane_claim dk flat ptr true (8+j)%nat.

Lemma decoder_certificate : exists dk,
 Decode.Image.kernel_image dk Decode.DecoderBytes.address Decode.DecoderBytes.symbol_bytes
 Decode.HelperBytes.address Decode.HelperBytes.symbol_bytes /\ decoder_runs dk.
Proof.
 destruct (Decode.Audit.decoder_projection _ _ _ _ _ _ Decode.Object.assembled_decode_correct)
 as [dk [Image [_ [_ [_ Run]]]]]. exists dk;split;[exact Image|].
 intros flat ptr Bytes j J;destruct(Run flat ptr true 0%nat Bytes ltac:(lia)) as [_ [_ [_ L]]].
 apply L;change (8+j<16)%nat;lia.
Qed.

Lemma direct_correct dk k flat ptr q Q eligible pad init :
 decoder_runs dk -> checked k=true -> byte_memory flat -> (pad<4)%nat -> valid_chunk q Q ->
 let os:=outputs dk flat ptr in let valid:=valid_mask dk flat ptr in
 exists m,direct k os valid eligible q pad init=Some m /\
 forall j,(j<8)%nat -> (Z.testbit m (Z.of_nat j)=true <->
 eligible j=true /\ strict_R (encoded flat (ptr+256) j) (Q j)).
Proof.
 intros D K B P Qs os valid.
 assert (L:forall j,(j<8)%nat -> lane_claim dk flat ptr true (8+j)%nat) by auto.
 assert (Bounds:SmallOrder.Audit.bounded(words os)).
 { intros row j R J;specialize(L j J);unfold lane_claim in L;change (lane_output dk flat ptr true (8+j)%nat) with (os j) in L.
   destruct L as [_ [X [Y _]]]. rewrite word_cell by exact J.
   assert (I:(row mod 5<5)%nat) by (apply Nat.mod_upper_bound;lia).
   assert (H:(row/5<2)%nat) by (apply Nat.div_lt_upper_bound;lia).
   destruct (row/5)%nat as [|[|n]];cbn [component];try lia;
     first [specialize(X _ I);unfold split in X;lia|specialize(Y _ I);unfold split in Y;lia]. }
 destruct(SmallOrder.Audit.run_correct _ _ _ _ SmallOrder.Object.assembled_small_order_correct
  pad (words os) init P Bounds) as [weak [Run [_ Bits]]].
 change (order_run os pad init=Some weak) in Run.
 rewrite (mask_result _ _ _ _ _ _ _ _ Run);eexists;split;[reflexivity|].
 intros j J;specialize(Bits j J);rewrite word_coords in Bits by exact J.
 pose proof(lane_exact k dk flat ptr q Q weak j B J K (L j J) Qs Bits) as E.
 fold os valid in E. cbn [coordinate_match coord_row]. unfold mask_and,mask_clear;rewrite !Z.land_spec,!Z.lnot_spec by lia;
 rewrite !byte_bit by exact J. rewrite !andb_true_iff in *;tauto.
Qed.
