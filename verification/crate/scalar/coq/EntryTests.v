From Coq Require Import ZArith List Lia.
From Machine Require Import execution.Blocks memory.MemoryTrace memory.FlatMemory execution.WordBounds memory.ByteMemory.
From Ed25519Simd.Scalar Require Import ScalarABI ScalarMemory ScalarBytes ScalarSpec FrameProof.
From Ed25519Simd.Scalar Require Audit Program.
Import ListNotations. Open Scope Z_scope.
Definition test_placement shift := Placement
 (fun r=>if Nat.eqb r stack then 0x10008 else if Nat.eqb r output then 0x4000+shift else 0x8000+shift)0x1000 (2^64-1).
Definition test_regs shift r := match r with
 | 4%nat=>origin(test_placement shift)stack | 6%nat=>origin(test_placement shift)input
 | 7%nat=>origin(test_placement shift)output | _=>2^64-1 end.
Definition test_bytes : Z->Z := fun _=>255.
(* Unaligned buffers are valid, including every byte offset within a cache line. *)
Example concrete_entries_exist size shift : 0<=size<=8192 ->0<=shift<64 ->
 concrete_entry(test_placement shift)size(test_regs shift)(fun _ _=>2^64-1)test_bytes.
Proof.
 intros Size Shift;constructor.
 - unfold valid_placement,fits64,disjoint.
   cbv beta iota zeta delta[origin code_base caller_pc test_placement stack output input Nat.eqb];intuition lia.
 - intro;unfold test_bytes;lia.
 - intro r;do 8(destruct r as[|r];[unfold word64;cbn [test_regs];
   cbv beta iota zeta delta[origin test_placement stack output input Nat.eqb];lia|]);unfold word64;cbn [test_regs];lia.
 - intros;unfold word64;lia.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
Example wrong_return_rejected :
 ~concrete_entry(test_placement 0)8192(test_regs 0)(fun _ _=>0)(fun _=>1).
Proof. intro E;pose proof(entry_return_word _ _ _ _ _ E)as H;discriminate. Qed.
(* All eight qwords of every input lane decode to the maximal unsigned word. *)
Example maximal_input_is_covered symbol_bytes : Audit.scalar_contract symbol_bytes ->
  0 <= Z.of_nat (length symbol_bytes) <= 8192 ->
  exists after, forall j, (j < 8)%nat ->
    lane_output (buffer_words after (origin (test_placement 0) output)) j = (2^512-1) mod L.
Proof.
 intros Cert Size.
 pose proof (concrete_entries_exist _ 0 Size ltac:(lia)) as Entry.
 destruct (Audit.run_concrete Cert _ _ _ None _ Entry) as [final [after Result]].
 exists after; intros j J. rewrite (proj1 (SysV.computed_output Result j J)).
 unfold lane_input, buffer_words, ByteMemory.buffer_words, read_word, test_bytes.
 reflexivity.
Qed.
