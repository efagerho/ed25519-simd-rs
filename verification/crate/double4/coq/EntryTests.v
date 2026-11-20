From Coq Require Import ZArith List Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory WordBounds ByteMemory.
From Ed25519Simd.Double4 Require Import Double4ABI Double4Memory Double4Bytes Double4Spec.
From Ed25519Simd.Double4 Require Audit Program.
Import ListNotations. Open Scope Z_scope.

(* Witness every supported stack alignment with actual bytes and maximal
   saved register values. This checks satisfiability of the public ABI. *)
Definition test_placement := Placement
 (fun r => if Nat.eqb r scratch then 0x10000 else 0x4000) 0x1000 0x800.
Definition test_regs pad r := match r with
 | 4%nat => entry_rsp test_placement pad
 | 7%nat => origin test_placement point
 | _ => 2^64-1 end.
Definition test_bytes pad := write_bytes (fun _ => 0xa5)
 (entry_rsp test_placement pad) 8 (word_byte (caller_pc test_placement)).

Example concrete_entries_exist size pad : 0 <= size <= 8192 -> permitted_padding pad ->
 concrete_entry test_placement size pad (test_regs pad)
                (fun _ _ => 2^64-1) (test_bytes pad).
Proof.
 intros Size Pad; pose proof (FrameProof.padding_range _ Pad) as Range; constructor.
 - unfold valid_placement; split; [exact Pad|].
   unfold fits64,disjoint.
   cbv beta iota zeta delta [origin code_base caller_pc test_placement scratch point Nat.eqb].
   intuition lia.
 - apply write_bytes_well_formed; [intro x; lia|intros; apply word_byte_bound].
 - intro r; destruct r as [|[|[|[|[|[|[|[|r]]]]]]]];
   unfold word64; cbn [test_regs];
   cbv beta iota zeta delta [entry_rsp origin test_placement scratch point Nat.eqb]; lia.
 - intros; unfold word64; lia.
 - reflexivity.
 - reflexivity.
 - apply write_read_word; unfold word64; cbn; lia.
Qed.

Example wrong_caller_return_is_rejected :
 ~ concrete_entry test_placement 8192 0 (test_regs 0) (fun _ _ => 0) (fun _ => 0).
Proof. intro E; pose proof (entry_return_word _ _ _ _ _ _ E) as H; discriminate. Qed.

Definition maximal_word_entry : state :=
 (initial_control (Control Caller (fun _ => Int 0) None (fun _ => None)) 48 (2^64-1),
  Data (fun _ _ => 2^64-1) (fun _ _ => 2^64-1)).

(* Initialization and return must not depend on arithmetic input bounds. *)
Example public_initialization_without_field_input_bound symbol_bytes :
 Audit.double4_contract symbol_bytes ->
 exists final, returns Program.double4_program abi_layout maximal_word_entry final /\
   output_initialized Program.double4_program maximal_word_entry final.
Proof.
 intros [_ [_ [_ [_ [Run _]]]]].
 assert (Entry : valid_double4_entry maximal_word_entry 48).
 { split; [unfold permitted_padding; cbn; auto|]. split.
   - eexists; exists (2^64-1); split; [unfold word64; lia|reflexivity].
   - split; intros; change (0 <= 2^64-1 < 2^64); lia. }
 destruct (Run _ _ Entry) as [final [R [_ [_ [_ [Init _]]]]]].
 exists final; auto.
Qed.
