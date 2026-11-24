From Coq Require Import List ZArith.
From Machine Require Import isa.X86 execution.LinkedCalls execution.WordSemantics memory.FlatMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* MOV r/m8,r8 with a REX prefix and [base + index] SIB. *)
Record indexed_byte := IndexedByte { source : nat; base : nat; index : nat }.
Definition byte_encoding i : option (list Z) :=
 let r:=Z.of_nat (source i) in let b:=Z.of_nat (base i) in let x:=Z.of_nat (index i) in
 if ((r <? 16) && (b <? 16) && (x <? 16) && negb (b mod 8 =? 5) && negb (x =? 4))%bool
 then Some [0x40+4*(r/8)+2*(x/8)+b/8; 0x88; X86.modrm 0 r 4; 8*(x mod 8)+b mod 8]
 else None.
Definition byte_store ip i s :=
 Store ip (word (regs s (base i)+regs s (index i))) 1
   (fun _ => regs s (source i) mod 256).
Definition byte_step ip i s :=
 let w:=byte_store ip i s in
 (with_words s (regs s) (commit (mem s) w), [w]).

(* The words used by caller_step for both implicit pushes. *)
Definition caller_stores slide ip op s : list store :=
 let slot:=word (regs s 4%nat-8) in
 match op with
 | Save r => [qword (word (slide+ip)) slot (regs s r)]
 | Invoke _ => [qword (word (slide+ip)) slot (slide+next_pc ip op)]
 | _ => [] end.

Theorem caller_store_memory slide ip op s :
 mem (snd (caller_step slide ip op s)) = replay (mem s) (caller_stores slide ip op s).
Proof. destruct op;reflexivity. Qed.
