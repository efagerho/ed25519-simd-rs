From Coq Require Import ZArith Bool List Lia.
From Machine Require Import execution.LinkedCalls memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.Dalek Require Import Masks.
From Ed25519Simd.DalekPostHash Require Import Keys.
From Ed25519Simd.PostHash Require Import Lanes.
From Ed25519Simd.PrepareChunk Require Import Caller Staging.
Import ListNotations. Local Open Scope Z_scope.

Definition bit m j := Z.testbit m (Z.of_nat j).
Definition key_mask decoded := octet decoded 0.
Definition eligible_mask scalars decoded := Z.land scalars (key_mask decoded).
Definition selected_ptr p decoded j := if bit (key_mask decoded) j
 then scratch p+table_offset j else identity_ptr p.
Definition flag_byte m j := Z.abs (if bit m j then -1 else 0).
Definition flags m j := negb (flag_byte m j=?0).
Lemma flag_exact m j : flag_byte m j=Z.b2z(bit m j) /\ flags m j=bit m j.
Proof. unfold flags,flag_byte;destruct(bit m j);split;reflexivity. Qed.
Lemma eligible_bit s d j : (j<8)%nat ->
 bit (eligible_mask s d) j=(bit s j && bit d j)%bool.
Proof. intros J;unfold bit,eligible_mask,key_mask;rewrite Z.land_spec,octet_bit by assumption;reflexivity. Qed.
Lemma selected_bit d j : (j<8)%nat -> bit (key_mask d) j=bit d j.
Proof. intro J;apply octet_bit,J. Qed.

(* A zero qword iff every stored 0/1 byte is zero. *)
Definition flag_word f := read_word (fun a=>Z.b2z(f (Z.to_nat a))) 0.
Lemma flag_word_zero f : flag_word f=0 <-> forall j,(j<8)%nat -> f j=false.
Proof.
 split.
 - intros H j J;pose proof(read_le_byte 8 (fun a=>Z.b2z(f (Z.to_nat a))) 0 j
     ltac:(intro x;destruct(f (Z.to_nat x));cbn;lia) J) as B.
   change (word_byte (flag_word f) (Z.of_nat j)=Z.b2z(f (Z.to_nat (0+Z.of_nat j)))) in B.
   rewrite H,Z.add_0_l,Nat2Z.id in B.
   unfold word_byte in B;rewrite Z.div_0_l,Z.mod_0_l in B by (try lia;apply Z.pow_nonzero;lia).
   destruct(f j);[discriminate|reflexivity].
 - intros F;unfold flag_word,read_word;cbn [read_le Z.add Z.to_nat Pos.to_nat];rewrite !F by lia;reflexivity.
Qed.

Definition final_flag strict_mode cpu s d j :=
 let f:=flags(eligible_mask s d) in if strict_mode:bool then filter_keys cpu f j else f j.
Inductive path := NoScalars | NoKeys | Built | Filtered.
Definition dispatch strict_mode cpu s d :=
 if reaches common Scalars (s=?0) Finish then (NoScalars,false)
 else if reaches common Decode (eligible_mask s d=?0) Reject then (NoKeys,false)
 else if strict_mode:bool then
   if reaches strict Prepare false Screen then
     (Filtered,negb(flag_word (final_flag true cpu s d)=?0)) else (Built,false)
 else (Built,true).

Lemma filter_clears cpu f j : f j=false -> filter_keys cpu f j=false.
Proof. intro H;unfold filter_keys;destruct(DalekPostHash.Caller.reaches _ _ _ _ _);rewrite H;reflexivity. Qed.
Lemma flag_nonzero m : 0<=m<256 -> (m<>0 <-> exists j,(j<8)%nat /\ bit m j=true).
Proof.
 intro M;split.
 - intro N;destruct (existsb (bit m) (seq 0 8)) eqn:E.
   + apply existsb_exists in E as [j [J B]];exists j;apply in_seq in J;auto with zarith.
   + exfalso;apply N,Z.bits_inj;intro i;rewrite Z.bits_0.
     destruct (Z_lt_ge_dec i 0);[apply Z.testbit_neg_r;lia|].
     destruct (Z_lt_ge_dec i 8);[|apply (above 8);lia].
     replace i with (Z.of_nat(Z.to_nat i)) by (rewrite Z2Nat.id;lia).
     change (bit m (Z.to_nat i)=false);destruct(bit m (Z.to_nat i)) eqn:B;auto.
     assert (existsb (bit m) (seq 0 8)=true) by
       (apply existsb_exists;exists(Z.to_nat i);split;[apply in_seq;lia|exact B]);congruence.
 - intros [j [_ B]] ->;unfold bit in B;rewrite Z.bits_0 in B;discriminate.
Qed.
Lemma ready_correct mode cpu s d : 0<=s<256 ->
 (snd (dispatch mode cpu s d)=true <-> exists j,(j<8)%nat /\ final_flag mode cpu s d j=true).
Proof.
 intros S;unfold dispatch.
 assert (ScalarBranch:forall z,reaches common Scalars z Finish=z) by (destruct z;reflexivity).
 assert (KeyBranch:forall z,reaches common Decode z Reject=z) by (destruct z;reflexivity).
 rewrite ScalarBranch,KeyBranch.
 assert (B:0<=eligible_mask s d<256).
 { unfold eligible_mask,key_mask,octet;change 256 with (2^8).
   rewrite <-Z.land_ones,Z.land_assoc,Z.land_ones by lia;apply Z.mod_pos_bound;lia. }
 assert (Zero:eligible_mask s d=0 -> forall j, final_flag mode cpu s d j=false).
 { intros E j;unfold final_flag;rewrite E.
   assert (Zr:flags 0 j=false) by (rewrite (proj2(flag_exact _ _));apply Z.bits_0).
   destruct mode;[apply filter_clears|];exact Zr. }
 destruct (Z.eqb_spec s 0) as [V|N].
 { assert (E:eligible_mask s d=0) by (unfold eligible_mask;rewrite V;apply Z.land_0_l).
   split;[discriminate|intros [j [_ F]];rewrite (Zero E) in F;discriminate]. }
 destruct (Z.eqb_spec (eligible_mask s d) 0) as [E|E].
 { split;[discriminate|intros [j [_ F]];rewrite (Zero E) in F;discriminate]. }
 destruct mode.
 - cbn [snd];change (reaches strict Prepare false Screen) with true;cbn [snd].
   rewrite negb_true_iff,Z.eqb_neq.
   destruct(existsb (final_flag true cpu s d) (seq 0 8)) eqn:X.
   + apply existsb_exists in X as [j [J F]];apply in_seq in J;split;[intros;exists j;tauto|].
     intros _ Zr;apply flag_word_zero with (j:=j) in Zr;tauto || congruence || lia.
   + assert (Zr:flag_word(final_flag true cpu s d)=0).
     { apply flag_word_zero;intros j J;destruct(final_flag true cpu s d j) eqn:F;auto.
       assert (existsb (final_flag true cpu s d) (seq 0 8)=true) by
       (apply existsb_exists;exists j;split;[apply in_seq;lia|exact F]);congruence. }
     split;[contradiction|intros [j [J F]];apply flag_word_zero with (j:=j) in Zr;congruence || lia].
 - split;[intros _|reflexivity];apply (flag_nonzero _ B) in E as [j [J F]].
   exists j;split;[exact J|unfold final_flag;now rewrite (proj2(flag_exact _ _))].
Qed.
