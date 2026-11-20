From Coq Require Import ZArith List Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory WordBounds ByteMemory.
From Ed25519Simd.Pow2 Require Import Pow2ABI Pow2Memory Pow2Bytes.
From Curve25519 Require Field Radix51.
From Ed25519Simd Require Wide51.
From Ed25519Simd.Pow2 Require Audit Program Pow2Spec.
Import ListNotations.
Open Scope Z_scope.

(* Concrete witnesses keep the public precondition from becoming vacuous.
   The input bases are unaligned; offsets 0 and 64 exercise exact and partial
   aliasing. Output and stack stay disjoint from both views. *)
Definition test_placement delta := Placement
 (fun r => match r with
  | 1%nat => 0x2001 | 2%nat => 0x2001+delta
  | 3%nat => 0x3003 | 4%nat => 0x10000 | _ => 0 end) 0x1000 0x800.
Definition test_regs loc r := match r with
 | 2%nat => origin loc input_b | 4%nat => entry_rsp loc
 | 6%nat => origin loc input_a | 7%nat => origin loc output | _ => 2^64-1 end.
Definition test_bytes loc := write_bytes (fun _ => 0xa5) (entry_rsp loc) 8 (word_byte (caller_pc loc)).

Example overlapping_entries_exist delta : In delta [0;64] ->
 concrete_entry (test_placement delta) 4096 (test_regs (test_placement delta))
                (fun _ _ => 2^64-1) (test_bytes (test_placement delta)).
Proof.
 intros [<-|[<-|N]]; try contradiction; constructor;
 try (unfold valid_placement,fits64,disjoint,entry_rsp,test_placement; cbn; intuition lia);
 try (intro r; destruct r as [|[|[|[|[|[|[|[|r]]]]]]]]; unfold word64; cbn; lia);
 try (intros; unfold word64; lia); try reflexivity.
 all: first [apply write_bytes_well_formed; [intro x; lia|intros; apply word_byte_bound]
            |apply write_read_word; unfold word64; cbn; lia].
Qed.

Example overlapping_views_use_the_same_bytes flat vectors :
 memory (snd (entry_from_bytes (test_placement 64) (test_regs (test_placement 64)) vectors None flat))
   (input_a,64) 0%nat =
 memory (snd (entry_from_bytes (test_placement 64) (test_regs (test_placement 64)) vectors None flat))
   (input_b,0) 0%nat.
Proof. reflexivity. Qed.

Example wrong_caller_return_is_rejected :
 ~ concrete_entry (test_placement 0) 4096 (test_regs (test_placement 0))
     (fun _ _ => 0) (fun _ => 0).
Proof. intro E; pose proof (entry_return_word _ _ _ _ _ E) as H; discriminate. Qed.

(* The public initialization guarantee must remain available even when the
   arithmetic specification's 52-bit input precondition is false. *)
Definition maximal_word_entry : state :=
 (initial_control (Control Caller (fun _ => Int 0) None (fun _ => None)),
  Data (fun _ _ => 2^64-1) (fun _ _ => 2^64-1)).

Example maximal_words_are_outside_the_field_input_bound :
 ~ (0 <= 2^64-1 < Radix51.split).
Proof. unfold Radix51.split; vm_compute; intuition discriminate. Qed.

Example public_initialization_without_field_input_bound symbol_bytes :
 Audit.pow2_contract symbol_bytes ->
 exists final, returns Program.pow2_program abi_layout maximal_word_entry final /\
   output_initialized Program.pow2_program maximal_word_entry final.
Proof.
 intros [_ [_ [_ [_ [Run _]]]]].
 assert (Entry : valid_pow2_entry maximal_word_entry (fun _ => 2^64-1) (fun _ => 2^64-1)).
 { split; [eexists; reflexivity|]. split; intros; reflexivity. }
 destruct (Run _ _ _ Entry) as [final [R [_ [_ [_ [Init _]]]]]].
 exists final; auto.
Qed.

(* Permitting output stores is insufficient: omitting the tenth store leaves
   the final byte unwritten, even though the first nine stores are present. *)
Definition short_output_trace :=
 map (fun i => DataOp (Write i (limb_address output 0 i))) (seq 0 9).

Example missing_last_vector_leaves_output_uninitialized :
 ~ (forall loc k, 0 <= k < 640 -> writes_at loc short_output_trace (origin loc output+k)).
Proof.
 intro H. destruct (H (test_placement 0) 639 ltac:(lia)) as [e [s [Member [Dest Byte]]]].
 apply in_map_iff in Member as [i [<- I]]. apply in_seq in I.
 cbn [destination] in Dest. injection Dest as <-.
 unfold inside,cell_address,address_of,limb_address in Byte; cbn [fst snd width] in Byte. lia.
Qed.
