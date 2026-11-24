From Coq Require Import List ZArith Bool Lia Field.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.MemoryGeometry memory.FlatMemory memory.ByteMemory.
From ProofArithmetic Require Import Radix.
From Curve25519 Require Import Scalar Radix51 Edwards.
From Curve25519.group Require Import PrimeField Affine Decompression Representation SignedMultiple.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.Decode Require Import Kernels Limbs Decode Chunks Program.
From Ed25519Simd.SignatureScalar Require Audit Object.
From Ed25519Simd.KeyTable Require Import Rows Execution Correct.
From Ed25519Simd.KeyTable Require Audit.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.DalekPostHash Require Keys.
From Ed25519Simd.PostHash Require Import Lanes.
From Ed25519Simd.PrepareChunk Require Import Caller Staging Dispatch.
Import ListNotations. Local Open Scope Z_scope.

Definition encoding p sig j := read_le 32 (original p) (lane_ptr p sig j).
Definition signature_scalar p j := read_le 32 (original p) (s_ptr p j).
Definition decodes z P := y P=residue(z mod 2^255) /\ has_sign (Z.testbit z 255) (x P).
Definition accepts mode p j :=
 signature_scalar p j<L /\ (exists R, decodes (encoding p true j) R) /\
 exists A, decodes (encoding p false j) A /\ (mode=true -> multiple 8 A<>identity).

Definition scalar_result p out :=
 0<=regs out 0%nat<256 /\ forall j,(j<8)%nat ->
 let s:=signature_scalar p j in let ds:=SignatureScalar.Audit.digits out (scratch p+digits_offset) j in
 (bit (regs out 0%nat) j=true <-> s<L) /\
 if s<?L then Forall (fun d=> -8<=d<8) ds /\ number 16 ds=s else ds=repeat 0 64.
Lemma scalar_call common_pc p prior incoming slide : scalar_inputs common_pc p prior slide ->
 scalar_result p (scalar_run common_pc p prior incoming slide).
Proof.
 intros H;pose proof H as Args;destruct H as [Place [W [M Rest]]].
 pose proof(SignatureScalar.Audit.returns_correct _ _ _ _
   SignatureScalar.Object.assembled_signature_scalar_correct slide (scalar_entry common_pc p prior slide) incoming Place W M) as [_ C].
 unfold scalar_run;destruct (SignatureScalar.Program.run _ _ _ _ _ _) as [ip out];cbn [snd].
 destruct C as [_ [_ [_ [_ [_ [Range C]]]]]];split;[exact Range|].
 intros j J;specialize(C j J);unfold signature_scalar;rewrite <-(scalar_source common_pc p prior slide j);[exact C|exact Args|exact J].
Qed.

Definition index (sig:bool) j := if sig then (8+j)%nat else j.
Definition outputs p := lane_output Ed25519Simd.Decode.Program.code (staged p) (scratch p) true.
Definition decoded p := Chunks.returned Ed25519Simd.Decode.Program.code (staged p) (scratch p) true.
Definition returned_bit p (sig:bool) j := bit (octet (decoded p) (if sig then 1 else 0)%nat) j.
Definition lane_result p sig j :=
 let o:=outputs p (index sig j) in let z:=encoding p sig j in
 (returned_bit p sig j=true <-> exists P,decodes z P) /\
 (forall P, decodes z P -> represents_point true (coordinates_of o) P) /\
 pack(oy o)=z mod 2^255 /\ value(oz o)=1%fp /\
 forall c,(c<4)%nat -> split_field(component o c).

Local Lemma checked_decode : forall op,verified Ed25519Simd.Decode.Program.code op=true.
Proof. destruct op;vm_compute;reflexivity. Qed.
Local Opaque lane_output Chunks.returned staged copy_trace Ed25519Simd.Decode.Program.code.
Lemma decode_lane p sig j : byte_memory(original p) -> (j<8)%nat -> lane_result p sig j.
Proof.
 intros B J;pose proof(proj2(decode_chunks _ (checked_decode _) (checked_decode _) (checked_decode _)
   _ (scratch p) true (staged_wf _ B)) (index sig j)
   ltac:(unfold count,index;destruct sig;lia)) as H.
 assert (Addr:scratch p+32*Z.of_nat(index sig j)=encoded_ptr p sig j)
   by (unfold encoded_ptr,index,r_bytes,encoding_size;destruct sig;lia).
 assert (Mask:returned_bit p sig j=bit (decoded p) (index sig j)).
 { unfold returned_bit,bit,index;rewrite octet_bit by exact J;f_equal;destruct sig;lia. }
 unfold lane_claim in H;fold (outputs p) (decoded p) in H.
 rewrite Addr,(staged_encoding p sig j J) in H.
 unfold lane_result;set (o:=outputs p (index sig j)) in *;fold (encoding p sig j) in H.
 destruct H as [[_ Raw] [X [Y [Zb [T [Vy [Vz [Vt Meaning]]]]]]]].
 set (z:=encoding p sig j) in *;set (fy:=residue(z mod 2^255)) in *.
 fold (bit (decoded p) (index sig j)) in Meaning;rewrite <-Mask in Meaning.
 assert (Out:forall P,decodes z P -> value(ox o)=x P).
 { intros P [Py Sign];fold fy in Py;pose proof(on_edwards P) as Curve;rewrite Py in Curve.
   destruct(returned_bit p sig j);[symmetry;apply (proj2(proj2 Meaning));assumption|exfalso;exact (Meaning _ Curve)]. }
 split.
 - destruct(returned_bit p sig j);[split;[intros _;exists(Point _ _ (proj1 Meaning));split;[reflexivity|exact(proj1(proj2 Meaning))]|auto]|].
   split;[discriminate|intros [P [Py _]];exfalso;apply (Meaning (x P));fold fy in Py;rewrite <-Py;apply on_edwards].
 - split.
   + intros P D;pose proof(Out _ D) as Vx;destruct D as [Py _];fold fy in Py.
     unfold represents_point,represents_xyz,coordinates_of;cbn [cx cy cz ct].
     fold (value (oz o)) (value (ox o)) (value (oy o)) (value (ot o)).
     rewrite Vt,Vz,Vx,Vy,Py.
     split;[split;[discriminate|split;ring]|intros _;ring].
   + split;[exact Raw|];split;[exact Vz|].
     intros [|[|[|c]]] C;assumption.
Qed.

Definition key_words p := words (outputs p).
Definition base p := scratch p+tables_offset.
Definition writes := match returning 8 with Some ws=>ws | None=>[] end.
Definition table_memory p incoming := KeyTable.Audit.table_view incoming Ed25519Simd.Decode.Program.code
 (key_words p) writes (base p) (original p).
(* Keys and the ladder share a selected-table reader. Register 6 in that
   reader denotes the pointer row passed in RDI at the filter call. *)
Definition filter_entry p incoming prior := with_words prior (Instructions.put (regs prior) 6 (selected p))
 (write_bytes (table_memory p incoming) (selected p) 64 (vector_byte(selected_ptr p (decoded p)))).
Definition layout p := fits64 (scratch p) 25344 /\ word64(identity_ptr p) /\
 disjoint (selected p) 80 (scratch p) 25344.
Definition selected_row p incoming prior j d := table_row (filter_entry p incoming prior) j false d.
Definition tables_result p incoming prior := forall j d,(j<8)%nat -> -8<=d<=8 ->
 forall P,decodes (encoding p false j) P ->
 let row:=selected_row p incoming prior j d in
 (forall i,(i<20)%nat -> 0<=row i<2^52) /\ represents_cache (scalar_cache false row) (scale d P).

Lemma pointer_value p incoming prior j : layout p -> (j<8)%nat ->
 read_word (mem (filter_entry p incoming prior)) (selected p+8*Z.of_nat j)=selected_ptr p (decoded p) j.
Proof.
 intros [Fit [Id D]] J;apply write_read_vector;[exact J|].
 unfold selected_ptr;destruct(bit _ _);[unfold table_offset,tables_offset,table_stride,word64,fits64 in *;lia|exact Id].
Qed.

Definition initialized_tables p incoming := KeyTable.Audit.signed_table_result incoming
 Ed25519Simd.Decode.Program.code 8 (key_words p) (base p).
Lemma initializes_tables p incoming : byte_memory(original p) ->
 (forall t,data_words(incoming t)) -> initialized_tables p incoming.
Proof.
 intros B W.
 assert (Bounds:cache_bounds false (key_words p)).
 { intros i j I J;unfold key_words;rewrite word_cell by exact J.
   destruct(decode_lane p false j B J) as [_ [_ [_ [_ H]]]].
   specialize(H (i/5)%nat ltac:(apply Nat.div_lt_upper_bound;lia) (i mod 5)%nat ltac:(apply Nat.mod_upper_bound;lia)).
   cbn [index] in H;unfold split in H;lia. }
 assert (K:kernels_ok Ed25519Simd.Decode.Program.code) by (split;[apply checked_decode|destruct op;vm_compute;reflexivity]).
 exact (result_correct incoming _ 8 _ (base p) W K Bounds (or_intror eq_refl)).
Qed.

Lemma built_tables p incoming prior : layout p -> byte_memory(original p) ->
 initialized_tables p incoming -> tables_result p incoming prior.
Proof.
 intros Layout B Init;destruct Init
   as [ws [Return [_ [_ Rows]]]].
 assert (Which:writes=ws) by (unfold writes;now rewrite Return).
 intros j d J D P Dec;specialize(Rows j d J D);destruct Rows as [_ Rows];specialize(Rows (original p)).
 destruct (decode_lane p false j B J) as [Ok [Rep [_ [Z1 _]]]].
 assert (A:bit(key_mask(decoded p)) j=true) by (apply Ok;now exists P).
 assert (Coord:value (Rows.coord (key_words p) j 2)=value(oz (outputs p j))).
 { unfold Rows.coord,key_words,value,pack,limbs;now rewrite !word_cell by exact J. }
 destruct Rows as [Bound Represents].
 specialize(Represents P ltac:(unfold key_words;rewrite word_coords by exact J;apply Rep,Dec)
   ltac:(rewrite Coord;exact Z1)).
 set (row:=fun i=>read_word (table_memory p incoming) (KeyTable.Audit.slot (base p) j d i)).
 assert (Equal:forall i,(i<20)%nat -> selected_row p incoming prior j d i=row i).
 { intros i I;unfold selected_row,table_row,table_address.
   change (regs(filter_entry p incoming prior) 6%nat) with (selected p).
   rewrite pointer_value by assumption;unfold selected_ptr;rewrite A.
   unfold row,KeyTable.Audit.slot,base,table_offset,tables_offset,table_stride.
   apply read_block;intros k Range;cbn [mem filter_entry with_words].
   replace (scratch p+(3584+2720*Z.of_nat j)+160*(8+d)+8*Z.of_nat i+k)
    with (scratch p+3584+2720*Z.of_nat j+160*(8+d)+8*Z.of_nat i+k) by ring.
   apply write_outside;destruct Layout as [_ [_ Sep]];unfold disjoint in Sep;lia. }
 rewrite <-Which in Bound,Represents.
 change (forall i,(i<20)%nat -> 0<=row i<2^52) in Bound.
 change (represents_cache (scalar_cache false row) (scale d P)) in Represents.
 split;[intros i I;rewrite Equal by assumption;apply Bound,I|].
 replace (scalar_cache false (selected_row p incoming prior j d)) with (scalar_cache false row);[exact Represents|].
 unfold scalar_cache,cache_from_fields;f_equal;try match goal with |- Some _=Some _=>f_equal end;
 apply limbs_ext;intros;symmetry;apply Equal;lia.
Qed.

Lemma valid_lane mode p out incoming prior j : scalar_result p out ->
 lane_result p false j -> lane_result p true j -> tables_result p incoming prior -> (j<8)%nat ->
 (final_flag mode (filter_entry p incoming prior) (regs out 0%nat) (decoded p) j=true <->
  accepts mode p j).
Proof.
 intros [_ S] [Dec _] [Rdec _] Tables J;destruct(S j J) as [Scalar _].
 set (f:=flags(eligible_mask (regs out 0%nat) (decoded p))).
 assert (Common:f j=true <-> signature_scalar p j<L /\
   (exists R, decodes (encoding p true j) R) /\ exists P,decodes(encoding p false j) P).
 { unfold f;rewrite (proj2(flag_exact _ _)),eligible_bit,!andb_true_iff,Scalar.
   change (bit (key_mask (decoded p)) j=true <-> exists P,decodes (encoding p false j) P) in Dec.
   change (bit (octet (decoded p) 1) j=true <-> exists R,decodes (encoding p true j) R) in Rdec.
   tauto. }
 unfold final_flag;fold f;unfold accepts.
 destruct mode.
 - destruct (f j) eqn:F.
   + destruct (proj1 Common eq_refl) as [Canon [Rdecodes [P DP]]].
     assert (Filter:forall Q,decodes(encoding p false j) Q ->
        (Keys.filter_keys (filter_entry p incoming prior) f j=true <-> multiple 8 Q<>identity)).
     { intros Q D;destruct(Tables j 8 J ltac:(lia) Q D) as [Bound Rep].
       rewrite (Keys.filter_lane_correct _ Q _ j Bound Rep J),F;tauto. }
     split;[intro H;split;[exact Canon|split;[exact Rdecodes|];exists P;split;[exact DP|intros _;now apply (Filter P DP)]]|].
     intros [_ [_ [Q [D Strong]]]];apply (Filter Q D);auto.
   + rewrite filter_clears by exact F;split;[discriminate|].
     intros [Canon [Rdecodes [P [D Strong]]]];apply (proj2 Common);repeat split;auto;now exists P.
 - rewrite Common;split;intros [C [Rdecodes [P D]]];repeat split;auto;exists P;intuition discriminate.
Qed.
