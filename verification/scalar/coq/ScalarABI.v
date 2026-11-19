From Coq Require Import List ZArith Bool.
From Machine Require Import Blocks WordBounds.
Import ListNotations. Open Scope Z_scope.
Definition stack := 0%nat.
Definition output := 1%nat.
Definition input := 2%nat.
Definition abi_layout : layout := fun r cell =>
 if Nat.eqb r stack && (cell=?0)then ReturnWords 1
 else if Nat.eqb r output && (0<=?cell)&&(cell<?5)then WriteVector
 else if Nat.eqb r input && (0<=?cell)&&(cell<?8)then ReadVector else Unmapped.
Definition initial_control incoming := Control(At 0)
 (fun r=>match r with 4%nat=>Ptr(stack,0) | 6%nat=>Ptr(input,0) | 7%nat=>Ptr(output,0) | _=>gpr incoming r end)
 (zf incoming)(fun a=>if ptr_eq a(stack,0)then Some Caller else return_memory incoming a).
Definition words_at(m:pointer->vector)region k := m(region,64*Z.of_nat(k/8))(k mod 8)%nat.
Definition valid_scalar_entry(initial:state) :=
 (exists incoming,fst initial=initial_control incoming) /\data_words(snd initial).
Definition saved_registers := [3;5;12;13;14;15]%nat.
Definition registers_preserved(initial final:state) :=
 forall r,In r saved_registers ->gpr(fst final)r=gpr(fst initial)r.
Definition stack_restored(initial final:state) :=
 Some(gpr(fst final)4%nat)=option_map Ptr(pointer_at(fst initial)4 8).
