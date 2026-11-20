From Coq Require Import List ZArith Bool.
From Machine Require Import abi.SysV execution.Blocks execution.WordBounds.
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
Definition saved_registers := SysV.sysv_saved.
Definition registers_preserved := SysV.preserves_sysv.
Definition stack_restored := SysV.restores_rsp.
