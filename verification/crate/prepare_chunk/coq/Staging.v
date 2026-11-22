From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls memory.MemoryGeometry memory.FlatMemory memory.ByteMemory.
From Ed25519Simd.SignatureScalar Require Audit ObjectBytes OrderBytes Program.
From Ed25519Simd.PrepareChunk Require Import Caller.
Import ListNotations. Local Open Scope Z_scope.

Record inputs := Inputs { original : bytes; pointers : Z; scratch : Z; selected : Z;
                          identity_ptr : Z; stack : Z }.
Definition source p (signature:bool) off := read_word (original p)
 (pointers p+(if signature then signature_row else 0)+off).
Definition lane_ptr p sig j := source p sig (8*Z.of_nat j).
Definition s_ptr p j := lane_ptr p true j+scalar_offset.
Definition workspace p := stack p-frame.
Definition scalar_memory p := write_bytes (original p) (workspace p) allocation (vector_byte (s_ptr p)).
(* Only the registers and memory observed by the scalar contract matter.
   The return slot and the order literal must be mapped at this call boundary. *)
Definition scalar_entry p (prior:cpu) := with_words prior
 (fun r=>match r with 4%nat=>workspace p-8 | 6%nat=>workspace p
 | 7%nat=>scratch p+digits_offset | _=>regs prior r end) (scalar_memory p).
Definition scalar_run p prior incoming slide := snd (Program.run ObjectBytes.address
 (Z.of_nat(length ObjectBytes.symbol_bytes)) OrderBytes.address slide (scalar_entry p prior) incoming).
Definition scalar_inputs p prior slide := let e:=scalar_entry p prior in
 Audit.placement e (slide+ObjectBytes.address) (Z.of_nat(length ObjectBytes.symbol_bytes))
                  (slide+OrderBytes.address) /\
 well_formed e /\ Audit.mapped e (slide+OrderBytes.address) OrderBytes.symbol_bytes /\
 forall j,(j<8)%nat -> fits64 (lane_ptr p true j) 64 /\
 disjoint (workspace p) allocation (s_ptr p j) 32.

Lemma read_block n (a b:bytes) x y :
 (forall k,0<=k<Z.of_nat n -> a(x+k)=b(y+k)) -> read_le n a x=read_le n b y.
Proof.
 revert x y;induction n as [|n IH];intros x y H;[reflexivity|].
 cbn [read_le];rewrite (IH (x+1) (y+1)).
 - specialize(H 0 ltac:(lia));rewrite !Z.add_0_r in H;now rewrite H.
 - intros k K;replace (x+1+k) with (x+(1+k)) by ring;
   replace (y+1+k) with (y+(1+k)) by ring;apply H;lia.
Qed.

Lemma scalar_source p prior slide j : scalar_inputs p prior slide -> (j<8)%nat ->
 Audit.scalar (scalar_entry p prior) j=read_le 32 (original p) (s_ptr p j).
Proof.
 intros [_ [_ [_ Layout]]] J;destruct (Layout j J) as [Fit D].
 assert (Ptr:Audit.ptr (scalar_entry p prior) j=s_ptr p j).
 { unfold Audit.ptr;change (read_word (scalar_memory p) (workspace p+8*Z.of_nat j)=s_ptr p j).
   apply write_read_vector;[exact J|unfold s_ptr,scalar_offset,WordBounds.word64,fits64 in *;lia]. }
 unfold Audit.scalar;rewrite Ptr;apply read_block;intros k K.
 change (scalar_memory p (s_ptr p j+k)=original p (s_ptr p j+k));apply write_outside.
 unfold disjoint in D;cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in K;lia.
Qed.

(* Follow the actual copying loop. Each entry names the destination byte
   offset, source pointer-row byte offset and choice of signature or key. *)
Fixpoint copies fuel ptr_off dst_off : list (Z*(bool*Z)) := match fuel with
 | O=>[] | S n=>(dst_off,(false,ptr_off))::(r_bytes+dst_off,(true,ptr_off))::
   (if reaches common CopyLane (dst_off+encoding_size=?r_bytes) CopyLane
    then copies n (ptr_off+8) (dst_off+encoding_size) else []) end.
Definition copy_trace := copies 9 0 0.
Fixpoint copied off (xs:list (Z*(bool*Z))) := match xs with
 | []=>None | (dst,src)::rest=>if (dst<=?off)&&(off<?dst+encoding_size)
   then Some(src,off-dst) else copied off rest end.
Definition staged p x := match copied (x-scratch p) copy_trace with
 | Some ((sig,ptr_off),b)=>original p (source p sig ptr_off+b)
 | None=>original p x end.
Definition encoded_ptr p (sig:bool) j := scratch p+(if sig then r_bytes else 0)+encoding_size*Z.of_nat j.
Lemma copy_layout :
 length copy_trace=16%nat /\ forallb (fun n=>let off:=Z.of_nat n in
 match copied off copy_trace with Some ((sig,ptr_off),b)=>
 Bool.eqb sig (256<=?off) && (ptr_off=?8*((off/32) mod 8)) && (b=?off mod 32)
 | None=>false end) (seq 0 512)=true.
Proof. vm_compute;split;reflexivity. Qed.
Lemma staged_bytes p (sig:bool) j k : (j<8)%nat -> 0<=k<32 ->
 staged p (encoded_ptr p sig j+k)=original p (lane_ptr p sig j+k).
Proof.
 intros J K;set (d:=(if sig then 256 else 0)+32*Z.of_nat j+k).
 assert (Range:0<=d<512) by (unfold d;destruct sig;lia).
 pose proof (proj2 copy_layout) as C.
 apply forallb_forall with (x:=Z.to_nat d) in C;[|apply in_seq;lia].
 cbv beta zeta in C;rewrite Z2Nat.id in C by lia.
 unfold staged;replace (encoded_ptr p sig j+k-scratch p) with d by
 (unfold encoded_ptr,r_bytes,encoding_size,d;ring).
 destruct (copied d copy_trace) as [[[side off] b]|];[|discriminate].
 apply andb_true_iff in C as [C B];apply andb_true_iff in C as [Side Off].
 apply Bool.eqb_prop in Side;apply Z.eqb_eq in Off,B.
 assert (D:d= k+((if sig then 8 else 0)+Z.of_nat j)*32) by (unfold d;destruct sig;ring).
 rewrite D,Z.div_add,Z.div_small,Z.add_0_l in Off by lia.
 rewrite D,Z.mod_add,Z.mod_small in B by lia.
 assert (E:(256<=?d)=sig) by (unfold d;destruct sig;[apply Z.leb_le|apply Z.leb_gt];lia).
 rewrite E in Side;subst side b;unfold lane_ptr;rewrite Off.
 f_equal;f_equal;f_equal;destruct sig;[replace (8+Z.of_nat j) with (Z.of_nat j+1*8) by ring;
 rewrite Z.mod_add by lia|];rewrite Z.mod_small by lia;reflexivity.
Qed.
Lemma staged_encoding p sig j : (j<8)%nat ->
 read_le 32 (staged p) (encoded_ptr p sig j)=read_le 32 (original p) (lane_ptr p sig j).
Proof. intros J;apply read_block;intros;apply staged_bytes;assumption. Qed.
Lemma staged_wf p : byte_memory (original p) -> byte_memory (staged p).
Proof. intros B x;unfold staged;destruct(copied _ _) as [[[? ?] ?]|];apply B. Qed.
