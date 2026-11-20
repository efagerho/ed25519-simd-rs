From Coq Require Import List ZArith Bool.
From Machine Require Import isa.X86 isa.ProgramLayout isa.Arithmetic isa.Shift isa.Logic isa.Move
 execution.LinkedCalls memory.ByteMemory.
Import ListNotations. Local Open Scope Z_scope.

(* Unmasked EVEX.512 integer operations on one RDI-relative row buffer.
   Expressions delay arithmetic while register moves and byte routing execute.
   Each memory operand denotes an entire, possibly unaligned, 64-byte row. *)
Inductive expr :=
| Lit (v:Z) | Acc | Initial (r lane:nat) | Load (row lane:nat)
| Add (a b:expr) | LeftQ (a:expr) (n:nat) | RightQ (a:expr) (n:nat)
| Octet (a:expr) (k:nat) | AndB (a b:expr) | SubB (a b:expr).
Scheme Equality for expr.

Fixpoint value (s:cpu) e := match e with
| Lit v => v | Acc => regs s 0%nat | Initial r j => vectors s j r
| Load row j => buffer_words (mem s) (regs s 7%nat) (8*row+j)%nat
| Add a b => vpaddq (value s a) (value s b)
| LeftQ a n => vpsllq (value s a) n | RightQ a n => vpsrlq (value s a) n
| Octet a k => FlatMemory.word_byte (value s a) (Z.of_nat k)
| AndB a b => Z.land (value s a) (value s b)
| SubB a b => (value s a-value s b) mod 256 end.

Inductive vec := Words (f:nat->expr) | Bytes (f:nat->expr).
Definition byte v (i:nat) := match v with
| Bytes f => f i | Words f => Octet (f (i/8)%nat) (i mod 8)%nat end.
Fixpoint join (f:nat->expr) (i n:nat) := match n with
| O => Lit 0 | S k => Add (f i) (LeftQ (join f (S i) k) 8) end.
Definition qword v j := match v with Words f => f j | Bytes f => join f (8*j)%nat 8 end.

Inductive op :=
| Imm (wide:bool) (n:Z) | Broadcast (octets:bool) (d:nat)
| AddRow (d a row:nat) | AddQ (d a b:nat) | ShiftQ (left:bool) (d a n:nat)
| And (d a b:nat) | Sub (d a b:nat) | Unpack (high:bool) (d a b:nat)
| Shuffle (d a b imm:nat) | Store (row a:nat) | Upper.
(* Byte operations use EVEX.W=0; the shared qword encoders use W=1. *)
Definition rr_w0 map pp opcode d a b :=
 match rr map pp opcode d a b with x::y::w::rest => x::y::(w-128)::rest | _=>[] end.
Definition encode op := match op with
| Imm wide n => op_bytes (Program [] []) (if wide then MovAbsRax n else Mov32 0 n)
| Broadcast octets d => if octets then rr_w0 2 1 0x7a d 0 0 else op_bytes (Program [] []) (BroadcastRax d)
| AddRow d a row => rm_memory 1 1 0xd4 d a 7 (64*Z.of_nat row)
| AddQ d a b => encode_vpaddq d a b
| ShiftQ to_left d a n => if to_left then encode_vpsllq d a n else encode_vpsrlq d a n
| And d a b => encode_vpandq d a b | Sub d a b => rr_w0 1 1 0xf8 d a b
| Unpack high d a b => rr_w0 1 1 (if high then 0x68 else 0x60) d a b
| Shuffle d a b imm => rr 3 1 0x43 d a b ++ [Z.of_nat imm]
| Store row a => encode_store a 7 (64*Z.of_nat row)
| Upper => op_bytes (Program [] []) ZeroUpper end.

Definition valid rows op := match op with
| Imm wide n => unsigned (if wide then 64 else 32) n
| Broadcast _ d => (d <? 32)%nat
| AddRow d a row => (d <? 32)%nat && (a <? 32)%nat && (row <? rows)%nat && signed 32 (64*Z.of_nat row)
| Store row a => (a <? 32)%nat && (row <? rows)%nat && signed 32 (64*Z.of_nat row)
| ShiftQ _ d a n => (d <? 32)%nat && (a <? 32)%nat && (n <? 256)%nat
| Shuffle d a b i => forallb (fun r=>(r <?32)%nat) [d;a;b] && (i <? 256)%nat
| And d a b | Sub d a b | Unpack _ d a b | AddQ d a b =>
    forallb (fun r=>(r <?32)%nat) [d;a;b]
| Upper => true end.

Record symbolic := State { acc:expr; zmm:nat->vec; stores:nat->option vec }.
Definition initial := State Acc (fun r=>Words (Initial r)) (fun _=>None).
Definition update {A} (f:nat->A) i a j := if Nat.eqb j i then a else f j.
Definition putv s d v := State (acc s) (update (zmm s) d v) (stores s).
Definition step s op :=
 let q r := qword (zmm s r) in let b r := byte (zmm s r) in
 match op with
 | Imm _ n => State (Lit n) (zmm s) (stores s)
 | Broadcast octets d => putv s d (if octets then Bytes(fun _=>Octet (acc s) 0)
                                   else Words(fun _=>acc s))
 | AddRow d a row => let src := match stores s row with Some v=>qword v | None=>Load row end in
                     putv s d (Words(fun j=>Add (q a j) (src j)))
 | AddQ d a src => putv s d (Words(fun j=>Add (q a j) (q src j)))
 | ShiftQ to_left d a n => putv s d (Words(fun j=>if to_left then LeftQ (q a j) n else RightQ (q a j) n))
 | And d a c => putv s d (Bytes(fun i=>AndB (b a i) (b c i)))
 | Sub d a c => putv s d (Bytes(fun i=>SubB (b a i) (b c i)))
 | Unpack high d a c => putv s d (Bytes(fun i=>
     let src := (16*(i/16) + (if high then 8 else 0) + i mod 16 / 2)%nat in
     if Nat.even i then b a src else b c src))
 | Shuffle d a c imm => putv s d (Bytes(fun i=>
     let block := (i/16)%nat in
     let src := (16*(imm / 4^block mod 4) + i mod 16)%nat in
     if (block <? 2)%nat then b a src else b c src))
 | Store row a => State (acc s) (zmm s) (update (stores s) row (Some (zmm s a)))
 | Upper => State (acc s) (fun r=>if (r <? 16)%nat then
     Words(fun j=>if (j <? 2)%nat then q r j else Lit 0) else zmm s r) (stores s)
 end.

(* Last store wins, including for reads following a store. Materialize the
   overlay in the same flat byte memory used by the SysV call model. *)
Definition finish rows state s :=
 let base:=regs s 7%nat in
 CPU (update (regs s) 0 (value s (acc state)))
     (fun j r=>value s (qword (zmm state r) j)) (flag s)
     (fun x=>let off:=x-base in
       if (0<=?off) && (off<?64*Z.of_nat rows) then
         match stores state (Z.to_nat (off/64)) with
         | Some v=>value s (byte v (Z.to_nat (off mod 64))) | None=>mem s x end
       else mem s x).
Definition execute rows code s := finish rows (fold_left step code initial) s.
