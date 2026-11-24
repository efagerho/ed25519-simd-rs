From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.ByteMemory abi.SysV.
From Ed25519Simd.Sha512Challenge Require Import Output Frame Image Execution Rows Writes.
Local Open Scope Z_scope.

Record sha512_contract pc code ro literal : Prop := {
  linked_text : image pc ro = code;
  linked_literals : literals = literal;
  relative_operands_fit : displacements pc ro 0 listing = true;
  message_reads : forall s m off j k, (j<8)%nat -> (k<64)%nat ->
    (reads_message s m off j k=true <-> (off+k<length_at s m j)%nat);
  message_offsets_fit : forall s t, bounded_lengths s -> (t<=Lanes.maximum (challenge_input s))%nat ->
    word64 (128*Z.of_nat t+128);
  write_footprint : writes_correct pc code ro;
  returns_correct : forall slide entry,
    placement entry (slide+pc) (Z.of_nat (length code)) (slide+ro) ->
    well_formed entry -> mapped entry (slide+ro) literal ->
    exists result, run pc code slide ro entry = Some result /\
      return_ip result = read_word (mem entry) (sp entry) /\
      return_sp result = sp entry+8 /\
      (forall r, In r sysv_saved -> saved_register result r = Some (regs entry r)) /\
      byte_memory (after result) /\
      preserved (fun x=>~writable entry x) (mem entry) (after result) /\
      challenge_digests entry (after result)
}.
