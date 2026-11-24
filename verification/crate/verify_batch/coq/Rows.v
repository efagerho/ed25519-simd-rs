From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.FlatMemory memory.ByteMemory memory.MemoryGeometry.
From Ed25519Simd.Sha512Challenge Require Frame.
From Ed25519Simd.PrepareChunk Require Staging Caller Composition.
From Ed25519Simd.VerifyBatch Require Import Policy Routing Digest.
Local Open Scope Z_scope.

Definition frame e := regs e 4%nat - 1000. (* five pushes followed by sub rsp,960 *)
Definition row_no first active j := (first+source_lane active j)%nat.
Definition field_word e first active f j :=
 let '(r,col):=routed f j in descriptor (mem e) (regs e 7%nat) (row_no first active r) (8*Z.of_nat col).
Definition staged_rows e first active :=
 Frame.matrix (mem e) (frame e+512) 4 (field_word e first active).
Definition preparation e first active (mode:bool) :=
 Staging.Inputs (staged_rows e first active) (frame e+512) (regs e 1%nat) (frame e+768)
   (regs e 8%nat) (frame e-8-(if mode then 16 else 0)).
Definition original_row e first active j := read_input (mem e) (regs e 7%nat) (row_no first active j).
Definition source e first active j f := descriptor (mem e) (regs e 7%nat) (row_no first active j) f.
Definition index_of e first active j := output_index (mem e) (regs e 7%nat) (row_no first active j).

Lemma row_word e first active f j : byte_memory(mem e) -> (f<4)%nat -> (j<8)%nat ->
 read_word (staged_rows e first active) (frame e+512+64*Z.of_nat f+8*Z.of_nat j)=
 source e first active j (8*Z.of_nat f).
Proof.
 intros B F J. unfold staged_rows. fold (Frame.cell (frame e+512) f j). rewrite Frame.matrix_word by
 (try assumption;try lia;unfold field_word;destruct(routed _ _);apply read_word_bound,B).
 unfold field_word;now rewrite transpose_fields by assumption.
Qed.

Lemma prepared_ptr e first active mode sig j : byte_memory(mem e) -> (j<8)%nat ->
 Staging.lane_ptr (preparation e first active mode) sig j =
 source e first active j (if sig then 8 else 0).
Proof.
 intros B J. unfold Staging.lane_ptr,Staging.source,preparation;cbn [Staging.original Staging.pointers].
 destruct sig;[apply (row_word _ _ _ 1 j B ltac:(lia) J)|apply (row_word _ _ _ 0 j B ltac:(lia) J)].
Qed.

(* A descriptor can borrow another descriptor's message or encoding. The
   caller frame must be private with respect to each read-only slice. *)
Definition rows_apart e first active := forall j,(j<8)%nat ->
 let a:=source e first active j in
 disjoint (frame e+512) 256 (a 0) 32 /\ disjoint (frame e+512) 256 (a 8) 64.

Lemma prepared_bytes e first active mode j : byte_memory(mem e) -> rows_apart e first active -> (j<8)%nat ->
 let p:=preparation e first active mode in let i:=original_row e first active j in
 Composition.encoding p false j=little_endian (key_bytes i) /\
 Composition.encoding p true j=little_endian (r_bytes i) /\
 Composition.signature_scalar p j=little_endian (s_bytes i).
Proof.
 intros B Sep J p i. unfold Composition.encoding, Composition.signature_scalar,Staging.s_ptr.
 unfold i,original_row,read_input;cbn [key_bytes r_bytes s_bytes];rewrite !read_octets by exact B.
 unfold p;rewrite !prepared_ptr by auto.
 destruct(Sep j J) as [K S]. unfold disjoint in *.
 unfold source in *; unfold Staging.original,preparation,staged_rows,Frame.matrix,Caller.scalar_offset.
 repeat split;apply Staging.read_block;intros k K';apply write_outside;cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in K';lia.
Qed.
