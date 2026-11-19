From Coq Require Import ZArith List Lia.
From Machine Require Import Blocks FlatMemory WordBounds ByteMemory.
Require Import Pow2ABI Pow2Memory Pow2Bytes.
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
