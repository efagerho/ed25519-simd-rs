From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.ByteMemory
 memory.FlatMemory memory.MemoryGeometry.
From Curve25519 Require Import Scalar.
From Ed25519Simd.SignatureScalar Require Import Audit ObjectBytes OrderBytes.
Import ListNotations. Local Open Scope Z_scope.

(* Every 256-bit S can reach the contract. All eight pointer slots alias
   one unaligned scalar, and the writable output is also unaligned. *)
Local Definition ro := 2^32.
Local Definition slide := ro-OrderBytes.address.
Local Definition key := 0x0101010101010101.
Local Definition entry x := CPU
 (fun r=>match r with 4%nat=>0x10008 | 7%nat=>0x20001 | 6%nat=>0x30000 | _=>0 end)
 (fun _ _=>0) None
 (fun a=>if (ro<=?a)&&(a<?ro+32) then word_byte L (a-ro)
         else if (key<=?a)&&(a<?key+32) then word_byte x (a-key) else 1).
Local Lemma repeated_pointer x j : (j<8)%nat -> ptr (entry x) j=key.
Proof. intro J;do 8 (destruct j as [|j];[reflexivity|]);lia. Qed.

Example admitted_entries x : 0<=x<2^256 ->
 let s:=entry x in well_formed s /\ mapped s (slide+OrderBytes.address) OrderBytes.symbol_bytes /\
 placement s (slide+ObjectBytes.address) (Z.of_nat(length ObjectBytes.symbol_bytes)) (slide+OrderBytes.address) /\
 forall j,(j<8)%nat -> scalar s j=x.
Proof.
 intros X s;split.
 - split;[intros r;do 8 (destruct r as [|r];[vm_compute;intuition discriminate|]);vm_compute;intuition discriminate|].
   split;[intros;vm_compute;intuition discriminate|].
   intro a;unfold s,entry;cbn [mem];destruct (_ && _)%bool;[apply word_byte_bound|].
   destruct (_ && _)%bool;[apply word_byte_bound|lia].
 - split.
   + intros i I;change (i<32)%nat in I;
       do 32 (destruct i as [|i];[reflexivity|]);lia.
   + split.
     * constructor;[ | | | | intros j J;unfold s;rewrite repeated_pointer by assumption | | ];
       vm_compute;intuition discriminate.
     * intros j J;unfold s,scalar;rewrite repeated_pointer by assumption.
       rewrite (read_le_encoded 32 x).
       -- apply Z.mod_small,X.
       -- intros k K;change (0<=k<32) in K;unfold entry;cbn [mem].
          destruct (_ && _)%bool eqn:R.
          ++ apply Bool.andb_true_iff in R as [_ H];apply Z.ltb_lt in H;unfold key,ro in H;lia.
          ++ rewrite (proj2 (Bool.andb_true_iff _ _)) by
               (split;[apply Z.leb_le|apply Z.ltb_lt];lia).
             f_equal;ring.
Qed.
