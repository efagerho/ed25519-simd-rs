From Coq Require Import ZArith List Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory WordBounds ByteMemory.
Require Import ScalarABI ScalarMemory ScalarBytes ScalarSpec FrameProof.
Require Audit Program.
Import ListNotations. Open Scope Z_scope.
Definition test_placement shift := Placement
 (fun r=>if Nat.eqb r stack then 0x10008 else if Nat.eqb r output then 0x4000+shift else 0x8000+shift)0x1000 0.
Definition test_regs shift r := match r with
 | 4%nat=>origin(test_placement shift)stack | 6%nat=>origin(test_placement shift)input
 | 7%nat=>origin(test_placement shift)output | _=>2^64-1 end.
Definition test_bytes : Z->Z := fun _=>0.
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
Definition maximal_entry : state :=
 (initial_control(Control Caller(fun _=>Int(2^64-1))None(fun _=>None)),
 Data(fun _ _=>2^64-1)(fun _ _=>2^64-1)).
Example maximal_input_is_covered symbol_bytes : Audit.scalar_contract symbol_bytes ->exists final,
 returns Program.scalar_program abi_layout maximal_entry final /\
 scalar_spec(words_at(memory(snd maximal_entry))input)(words_at(memory(snd final))output).
Proof.
 intros[_[_[_[Run _]]]].
 assert(Entry:valid_scalar_entry maximal_entry).
 { split;[eexists;reflexivity|split;intros;change(0<=2^64-1<2^64);lia]. }
 destruct(Run _ Entry)as[final[R[_[_[_[_ Spec]]]]]];exists final;auto.
Qed.
