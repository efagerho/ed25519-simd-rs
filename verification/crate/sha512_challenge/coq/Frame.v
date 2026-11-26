From Coq Require Import List ZArith NArith Strings.Byte Bool Lia.
From Machine Require Import execution.LinkedCalls execution.WordSemantics execution.WordBounds
  memory.FlatMemory memory.ByteMemory memory.MemoryGeometry.
From SHA512 Require Import LengthTrailer Spec.
From Ed25519Simd.Sha512Challenge Require Import Output Block Loader Lanes.
Import ListNotations.
Local Open Scope Z_scope.

Definition sp s := regs s 4%nat.
Definition dst s := regs s 7%nat.
Definition frame s := (sp s-8) - (sp s-8) mod 64 - 704.
Definition writable s x := frame s-8 <= x < sp s \/ dst s <= x < dst s+512.
Definition source s addr n := fits64 addr n /\
 (n=0 \/ (disjoint (dst s) 512 addr n /\ disjoint (frame s-8) (sp s-frame s+8) addr n)).
Record placement s pc size ro : Prop := {
 stack_fits : 0 <= frame s-8 /\ sp s+8 < 2^64;
 out_fits : fits64 (dst s) 512 /\ disjoint (dst s) 512 (frame s-8) (sp s-frame s+16);
 image_fits : source s pc size /\ source s ro 832 /\ ro mod 64=0;
 tables_fit : source s (regs s 6%nat) 256 /\ source s (regs s 2%nat) 256 /\
              source s (regs s 1%nat) 64 /\ source s (regs s 8%nat) 64;
 slices_fit : forall j,(j<8)%nat ->
   0 <= message_length s j < 2^63 /\
   source s (read_word (mem s) (regs s 1%nat + 8*Z.of_nat j)) (message_length s j)
}.
Definition mapped s addr raw := forall i,(i<length raw)%nat ->
  mem s (addr+Z.of_nat i)=nth i raw 0.

(* Row-major vector writes, with eight little-endian qwords per ZMM. *)
Definition matrix (before:bytes) base rows (v:nat->nat->Z) :=
  write_bytes before base (64*rows) (fun d =>
    word_byte (v (Z.to_nat (d/64)) (Z.to_nat (d mod 64/8))) (d mod 8)).
Definition cell base row lane := base + 64*Z.of_nat row + 8*Z.of_nat lane.
Lemma indices r j k : (j<8)%nat -> 0<=k<8 ->
  let d:=64*Z.of_nat r+8*Z.of_nat j+k in
  (d/64=Z.of_nat r /\ d mod 64/8=Z.of_nat j /\ d mod 8=k).
Proof.
  intros J K. cbv zeta. set (b:=8*Z.of_nat j+k).
  assert (B:0<=b<64) by (unfold b;lia).
  replace (64*Z.of_nat r+8*Z.of_nat j+k) with (b+Z.of_nat r*64) by (unfold b;ring).
  rewrite Z.div_add, Z.mod_add, (Z.div_small b 64) by lia.
  replace (b+Z.of_nat r*64) with (k+(Z.of_nat j+8*Z.of_nat r)*8) by (unfold b;ring).
  unfold b. replace (8*Z.of_nat j+k) with (k+Z.of_nat j*8) by ring.
  rewrite (Z.mod_small (k+Z.of_nat j*8) 64) by lia.
  now rewrite Z.div_add, Z.mod_add, Z.div_small, Z.mod_small by lia.
Qed.
Lemma matrix_word before base n v r j : (j<8)%nat -> 0<=Z.of_nat r<n ->
  word64 (v r j) -> read_word (matrix before base n v) (cell base r j) = v r j.
Proof.
  intros J R W. apply read_word_exact; [exact W|].
  intros k K. unfold matrix, cell.
  replace (base+64*Z.of_nat r+8*Z.of_nat j+k) with (base+(64*Z.of_nat r+8*Z.of_nat j+k)) by ring.
  rewrite write_at by lia. destruct (indices r j k J K) as [A [B C]].
  now rewrite A,B,C,!Nat2Z.id.
Qed.

Definition length_value s row j :=
  let m:=message_length s j in let n:=WordSemantics.word (m+64) in
  match row with O => Z.shiftr n 61 | S O => WordSemantics.word (Z.shiftl n 3)
   | _ => Z.shiftr (WordSemantics.word (m+80)) 7 end.
Definition init_frame s :=
  matrix (store_word (mem s) (sp s-8) (regs s 5%nat)) (frame s+512) 3 (length_value s).
Definition spill_frame m s hs := matrix m (frame s) 8
  (fun row lane => Z.of_N (nth row (spill (hs lane)) 0%N)).
Definition length_slot s m row j := read_word m (cell (frame s+512) row j).
Definition bounded_lengths s := forall j, (j<8)%nat -> 0<=message_length s j<2^63.
Lemma length_words s j : bounded_lengths s -> (j<8)%nat ->
 (forall r,word64 (length_value s r j)) /\
 length_value s 2%nat j = Z.of_nat (last_block (challenge_input s j)) /\
 big_endian 8 (Z.to_N (length_value s 0%nat j)) ++
 big_endian 8 (Z.to_N (length_value s 1%nat j)) = trailer (challenge_input s j).
Proof.
  intros Sizes J. specialize (Sizes j J). unfold length_value.
  set (m:=message_length s j) in *. rewrite !(word_fits (m+_)) by (unfold word64;lia).
  rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  split.
  - intros [|[|r]]; unfold WordSemantics.word, word64;
      first [apply Z.mod_pos_bound; lia | split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia].
  - split.
    + unfold last_block. rewrite challenge_size, Nat2Z.inj_div, Nat2Z.inj_add, Nat2Z.inj_sub,
        Nat2Z.inj_add, Z2Nat.id by (fold m; lia). fold m. f_equal; lia.
    + unfold trailer. rewrite challenge_size, Nat2N.inj_add, Z_nat_N.
      rewrite N.shiftr_div_pow2, N.shiftl_mul_pow2.
      unfold Spec.word, WordSemantics.word. rewrite !Z2N.inj_div, Z2N.inj_mod, Z2N.inj_mul,
        !Z2N.inj_add by lia. fold m. now rewrite N.add_comm.
Qed.

(* R8 increases twice per block. The largest temporary used by LEA in the
   row helper also fits a qword, including the last iteration of the longest
   Rust slice. Remainders on lanes which borrow are never used as addresses. *)
Lemma cursor_fits s t : bounded_lengths s -> (t<=Lanes.maximum (challenge_input s))%nat ->
  word64 (128*Z.of_nat t+128).
Proof.
 intros L T.
 assert (Lane:forall j,(j<8)%nat -> 128*Z.of_nat (last_block (challenge_input s j))+128<2^64).
 { intros j J. unfold last_block. rewrite challenge_size.
   set (n:=Z.to_nat (message_length s j)). replace (64+n-64+80)%nat with (n+80)%nat by lia.
   pose proof (Nat.div_mod (n+80) 128 ltac:(lia)).
   pose proof (L _ J). unfold n in *. lia. }
 assert (H : forall js:list nat,(forall j,In j js -> (j<8)%nat) ->
   128*Z.of_nat (fold_right Nat.max 0%nat (map (fun j=>last_block (challenge_input s j)) js))+128<2^64).
 { induction js as [|j js IH];intro B;[vm_compute;reflexivity|].
   cbn [fold_right map]. rewrite Nat2Z.inj_max. specialize (IH ltac:(intros;apply B;now right)).
   specialize (Lane j ltac:(apply B;now left)). lia. }
 specialize (H (seq 0 8) ltac:(intros j I;apply in_seq in I;lia)).
 unfold Lanes.maximum in T. unfold word64;lia.
Qed.
