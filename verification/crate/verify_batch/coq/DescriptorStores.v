From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds execution.WordSemantics
 execution.ScalarBytes execution.MappedFetch execution.FrameInstructions
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry memory.WriteTrace.
From Machine Require isa.VectorMoves execution.IndexedLoads.
From Ed25519Simd.VerifyBatch Require Import Routing.
Import ListNotations. Local Open Scope Z_scope.

Definition input i : line := (length (IndexedLoad.encode i),VectorMove (VectorMoves.Input i)).
Definition output (f:nat) : line := let d:=512+64*Z.of_nat f in
 (length (Move.encode_store f 4 d),VectorMove (VectorMoves.Output f 4 d)).
Definition inputs := map input transpose.
Definition publish := map output (seq 0 4).

Definition load_vectors ops s := fold_left (fun s i=>IndexedLoads.execute [i] s) ops s.
Lemma read_block origin text ops : forall off s carry, 0<=off -> decoded text off (map input ops) ->
 run (length (map input ops)) (ScalarBytes.fetch origin text) (State (Running off) s carry)=
 Some(State (Running (off+FrameInstructions.width (map input ops))) (load_vectors ops s) carry,[]).
Proof.
 induction ops as [|i ops IH];intros off s c O D.
 - cbn [map load_vectors fold_left FrameInstructions.width fold_right];now rewrite Z.add_0_r.
 - destruct D as [D R]. cbn [map length run];unfold ScalarBytes.fetch at 1;cbn [loc cpu_state cf].
   rewrite (proj2 (Z.ltb_ge _ _) O),D. cbn [ScalarBytes.step].
   rewrite (IH (off+Z.of_nat(length(IndexedLoad.encode i))) _ c ltac:(lia) R).
   cbn [option_map app FrameInstructions.width map fold_right fst input load_vectors fold_left];now rewrite Z.add_assoc.
Qed.

Definition value s j f := read_word (mem s) (word(regs s 3%nat+40*Z.of_nat j)+8*Z.of_nat f).
Lemma lane_loaded s j f : (j<8)%nat -> (f<4)%nat ->
 vectors (load_vectors transpose s) j f=value s j f.
Proof.
 intros J F. do 4 (destruct f as [|f];[
   do 8 (destruct j as [|j];[reflexivity|]);lia|]);lia.
Qed.

Definition bank frame f := frame+512+64*Z.of_nat f.
Definition store_vector frame f s := with_words s (regs s)
 (write_bytes (mem s) (bank frame f) 64 (vector_byte (fun j=>vectors s j f))).
Definition stored frame fs s := fold_left (fun t f=>store_vector frame f t) fs s.

Lemma store_block origin text frame fs : fits64 frame 960 -> Forall (fun f=>(f<4)%nat) fs ->
 forall off s c, 0<=off -> decoded text off (map output fs) -> regs s 4%nat=frame ->
 exists ws,run (length (map output fs)) (ScalarBytes.fetch origin text) (State (Running off) s c)=
 Some(State (Running (off+FrameInstructions.width (map output fs))) (stored frame fs s) c,ws).
Proof.
 intros Fit Fs;induction Fs as [|f fs F Fs IH];intros off s c O D SP.
 - exists [];cbn [map stored fold_left FrameInstructions.width fold_right];now rewrite Z.add_0_r.
 - destruct D as [D R].
   destruct (IH (off+Z.of_nat(fst(output f))) (store_vector frame f s) c ltac:(lia) R SP) as [ws Run].
   set (w:=vector (word(origin+off)) (bank frame f) (fun j=>vectors s j f)).
   exists (w::ws);cbn [length map run];unfold ScalarBytes.fetch at 1;cbn [loc cpu_state cf].
   rewrite (proj2 (Z.ltb_ge _ _) O),D. cbn [ScalarBytes.step].
   assert (Addr:word(regs s 4%nat+(512+64*Z.of_nat f))=bank frame f).
   { rewrite SP;unfold bank;rewrite <-Z.add_assoc;apply word_fits;destruct Fit;unfold word64;lia. }
   rewrite Addr;fold w. lazymatch goal with |- _ = ?rhs => change (option_map (fun '(st,tail)=>(st,w::tail))
      (run (length (map output fs)) (ScalarBytes.fetch origin text)
       (State (Running (off+Z.of_nat(fst(output f)))) (store_vector frame f s) c)) = rhs) end.
   rewrite Run. cbn [option_map app FrameInstructions.width fold_right fst map output stored fold_left];now rewrite Z.add_assoc.
Qed.

Lemma store_payload frame s j f k : (j<8)%nat -> (f<4)%nat -> 0<=k<8 ->
 mem (stored frame (seq 0 4) s) (bank frame f+8*Z.of_nat j+k)=word_byte (vectors s j f) k.
Proof.
 intros J F K.
 destruct f as [|[|[|[|f]]]];try lia.
 all: cbn [stored seq fold_left store_vector with_words mem vectors];unfold bank;
   cbn [Z.of_nat Pos.of_succ_nat Pos.succ];repeat rewrite write_outside by lia;
   match goal with |- write_bytes _ ?a _ _ ?x = _ => replace x with (a+(8*Z.of_nat j+k)) by ring end;
   rewrite write_at by lia;rewrite vector_byte_lane by exact K;reflexivity.
Qed.
