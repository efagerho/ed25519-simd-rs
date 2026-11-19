From Coq Require Import ZArith List Lia.
From Machine Require Import Blocks MemoryTrace FlatMemory WordBounds ByteMemory.
Require Import CachedAddABI CachedAddMemory CachedAddBytes CachedAddSpec FrameProof FieldSpec.
Require Audit Program.
Import ListNotations. Open Scope Z_scope.
Definition test_placement := Placement
 (fun r=>if Nat.eqb r scratch then 0x10000 else if Nat.eqb r point then 0x4000 else 0x8000) 0x1000 0.
Definition test_regs pad full affine r := match r with
 | 1%nat=>flag_word affine | 2%nat=>flag_word full
 | 4%nat=>entry_rsp test_placement pad | 6%nat=>origin test_placement cached
 | 7%nat=>origin test_placement point | _=>2^64-1 end.
Definition test_bytes : Z->Z := fun _=>0.
(* All 16 public flag/alignment combinations have concrete byte-level entries.
   Their arithmetic precondition is also true: every input limb is zero. *)
Example concrete_entries_exist full affine size pad : 0<=size<=8192 ->permitted_padding pad ->
 concrete_entry full affine test_placement size pad(test_regs pad full affine)
 (fun _ _=>2^64-1)test_bytes.
Proof.
 intros Size Pad;pose proof(padding_range _ Pad)as Range;constructor.
 - unfold valid_placement;split;[exact Pad|];unfold fits64,disjoint.
   destruct affine;cbv beta iota zeta delta[cache_length origin code_base caller_pc test_placement scratch point cached Nat.eqb];intuition lia.
 - intro;unfold test_bytes;lia.
 - intro r;do 8(destruct r as[|r];[unfold word64;cbn [test_regs];
    cbv beta iota zeta delta[entry_rsp origin test_placement scratch point cached Nat.eqb];
    destruct full,affine;cbn [flag_word];lia|]);unfold word64;cbn [test_regs];lia.
 - intros;unfold word64;lia.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.
Example concrete_arithmetic_inputs affine : input_bounds affine
 (buffer_words test_bytes(origin test_placement point))(buffer_words test_bytes(origin test_placement cached)).
Proof. split;intros;change(0<=0<split);unfold split;lia. Qed.
Example wrong_return_rejected full affine :
 ~concrete_entry full affine test_placement 8192 0(test_regs 0 full affine)(fun _ _=>0)(fun _=>1).
Proof. intro E;pose proof(entry_return_word _ _ _ _ _ _ _ _ E)as H;discriminate. Qed.
Definition maximal_entry full affine : state :=
 (initial_control(Control Caller(fun _=>Int 0)None(fun _=>None))48(2^64-1)full affine,
 Data(fun _ _=>2^64-1)(fun _ _=>2^64-1)).
Example initialization_without_field_bounds symbol_bytes full affine : Audit.cached_add_contract symbol_bytes ->
 exists final,returns Program.add_cached_program(abi_layout affine)(maximal_entry full affine)final /\
 output_initialized affine Program.add_cached_program(maximal_entry full affine)final.
Proof.
 intros[_[_[_[Run _]]]].
 assert(Entry:valid_cached_add_entry(maximal_entry full affine)48 full affine).
 { split;[unfold permitted_padding;cbn;auto|];split.
   - eexists;exists(2^64-1);split;[unfold word64;lia|reflexivity].
   - split;intros;change(0<=2^64-1<2^64);lia. }
 destruct(Run full affine _ _ Entry)as[final[R[_[_[_[Init _]]]]]];exists final;auto.
Qed.
