From Coq Require Import List ZArith Bool.
From Machine Require Import execution.LinkedCalls execution.IndexedLoads execution.WordSemantics
 memory.PackedWrites memory.WriteTrace memory.ByteMemory memory.FlatMemory memory.MemoryGeometry abi.SysV.
From Curve25519 Require Import Scalar SignedRadix16.
From ProofArithmetic Require Import Radix.
From Ed25519Simd.SignatureScalar Require Import Program.
Import ListNotations. Local Open Scope Z_scope.

Definition ptr s j := read_word (mem s) (regs s 6%nat + 8*Z.of_nat j).
Definition scalar s j := read_le 32 (mem s) (ptr s j).
Definition output s x := regs s 7%nat <= x < regs s 7%nat+512.
Definition digits s dst j := map (fun k=>signed_byte (mem s (dst+64*Z.of_nat j+Z.of_nat k))) (seq 0 64).
Definition source s a n := fits64 a n /\ disjoint (regs s 7%nat) 512 a n.
Record placement s pc size ro : Prop := {
 out_fits : fits64 (regs s 7%nat) 512;
 code_fits : source s pc size;
 literals_fit : source s ro 32;
 table_fits : source s (regs s 6%nat) 64;
 scalar_fits : forall j,(j<8)%nat -> source s (ptr s j) 32;
 ret_fits : source s (regs s 4%nat) 8;
 next_sp_fits : regs s 4%nat+8 < 2^64
}.
Definition mapped s a bs := forall i,(i<length bs)%nat -> mem s (a+Z.of_nat i)=nth i bs 0.
Definition reads_inputs s := forall a n, In (a,n) (loads (summary inputs)) ->
 exists j,(j<8)%nat /\ ((n=8%nat /\ eval s a=regs s 6%nat+8*Z.of_nat j) \/
                          (n=32%nat /\ eval s a=ptr s j)).
(* Account for data reads outside the pointer-loading block. A constant load
   must fit wholly in the linked 32-byte object. The packing code only stores. *)
Definition literal_access ro i := match i with
 | MaskedWords.Compare _ _ _ _ (MaskedWords.Rip a) => (ro <=? a) && (a+8 <=? ro+32)
 | _=>true end.
Definition no_row_load op := match op with Packed.AddRow _ _ _=>false | _=>true end.

(* The digit stores are the only memory writes in the entry. Their PCs
   start immediately after the input loads and register comparison. *)
Definition digit_start pc size slide :=
 let suffix := flat_map Packed.encode Radix16Output.write_digits ++
   MaskTrace.encoding (MaskTrace.KmovEax result_mask) ++ Packed.encode Packed.Upper ++
   LinkedCalls.encoding 0 LinkedCalls.Return in
 slide+pc+size-Z.of_nat(length suffix).
Definition digit_writes pc size ro slide entry incoming :=
 PackedWrites.trace (digit_start pc size slide)
   (prepared ro slide entry incoming) Packed.initial Radix16Output.write_digits.

Record signature_scalar_contract pc code ro literal : Prop := {
 linked_code : image pc ro = Some code /\ forallb IndexedLoad.valid inputs=true /\
               forallb (Packed.valid 8) Radix16Output.write_digits=true;
 read_footprint : forallb (literal_access ro) (compare_order ro++bias_words)=true /\
                  forallb no_row_load Radix16Output.write_digits=true;
 linked_order : length literal=32%nat /\
     read_le 32 (fun a=>nth (Z.to_nat a) literal 0) 0=L;
 initializes_output : forall j,(j<8)%nat -> exists row,
     Packed.stores Radix16Output.output_state j=Some row;
 write_footprint : forall slide entry incoming,
   let n:=Z.of_nat(length code) in let ws:=digit_writes pc n ro slide entry incoming in
   confined (output entry) ws /\ forall x,
   mem (snd (run pc n ro slide entry incoming)) x=WriteTrace.replay (mem entry) ws x;
 returns_correct : forall slide entry incoming,
   placement entry (slide+pc) (Z.of_nat(length code)) (slide+ro) ->
   well_formed entry -> mapped entry (slide+ro) literal ->
   reads_inputs entry /\
   let '(ip,out):=run pc (Z.of_nat(length code)) ro slide entry incoming in
   ip=read_word (mem entry) (regs entry 4%nat) /\
   regs out 4%nat=regs entry 4%nat+8 /\
   (forall r,In r sysv_saved -> regs out r=regs entry r) /\
   preserved (fun x=>~output entry x) (mem entry) (mem out) /\
   byte_memory (mem out) /\ 0<=regs out 0%nat<256 /\
   (forall j,(j<8)%nat ->
     let x:=scalar entry j in let ds:=digits out (regs entry 7%nat) j in
     (Z.testbit (regs out 0%nat) (Z.of_nat j)=true <-> x<L) /\
     (if x <? L then Forall (fun d=> -8<=d<8) ds /\ number 16 ds=x
      else ds=repeat 0 64))
}.
