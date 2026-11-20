From Coq Require Import List ZArith Bool.
From Machine Require Import isa.Instructions.
Open Scope Z_scope.

(* Addresses are byte offsets in disjoint, relocatable memory regions. Each
   64-byte cell holds one vector or up to eight return-address words. Alignment
   is relative to the region origin, which need not be physically aligned. *)
Definition pointer := (nat * Z)%type.
Definition offset (a : pointer) d : pointer := (fst a, snd a+d).
Definition ptr_eq (a b : pointer) := Nat.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
Inductive permission := Unmapped | ReadVector | WriteVector | ReturnWords (qword_mask:Z).
Definition layout := nat -> Z -> permission.
Definition access (l : layout) (a : pointer) := l (fst a) (snd a / 64).
Definition vector_ok l a writing := (snd a mod 64 =? 0) &&
 match access l a with WriteVector => true | ReadVector => negb writing | _ => false end.
Definition return_ok l a := (snd a mod 8 =? 0) &&
 match access l a with
 | ReturnWords mask => Z.testbit mask ((snd a / 8) mod 8)
 | _ => false end.

Inductive scalar := Int (bits : Z) | Ptr (address : pointer) | Unknown.
(* SavedWord is a tagged stack qword, never an executable PC. PUSH/POP RBP
   share the same memory as CALL/RET, so the byte proof also covers the save. *)
Definition stack_word n := n mod 2^64.
Inductive pc := At (address : Z) | Caller | SavedWord (bits : Z).
Record control := Control {
 rip : pc; gpr : nat -> scalar; zf : option bool;
 return_memory : pointer -> option pc
}.
Definition pointer_at c base disp := match gpr c base with
 | Ptr a => Some (offset a disp) | _ => None end.
Definition set_gpr c r v := Control (rip c) (put (gpr c) r v) (zf c) (return_memory c).

Definition vector := nat -> Z.
Record data := Data { zmm : nat -> nat -> Z; memory : pointer -> vector }.
(* zmm lane register; memory maps a vector's start address to its eight lanes. *)
Definition register_write s r v := Data (fun j => put (zmm s j) r (v j)) (memory s).
Definition effective_load (s:data) (bases:list (nat*pointer)) j b d :=
 match find (fun entry => Nat.eqb (fst entry) b) bases with
 | Some (_,a) => memory s (offset a d) j | None => 0 end.

Definition state := (control * data)%type.
