From Coq Require Import List ZArith.
From Machine Require Import abi.SysV execution.LinkedCalls execution.Packed memory.ByteMemory
  memory.FlatMemory memory.MemoryGeometry.
From Curve25519 Require Import SignedRadix16.
From Ed25519Simd.StageRound Require Import Program.
Local Open Scope Z_scope.

(* The output holds the two projective key operands around the affine base operand. *)
Definition first_row k : nat := match k with Odd => 0 | Base => 20 | Even => 35 end.
Definition columns k : nat := match k with Base => 15 | _ => 20 end.
Definition destination s x := regs s 7%nat <= x < regs s 7%nat + 3520.
Definition key_table s lane := read_word (mem s) (regs s 6%nat + 8 * Z.of_nat lane).
Definition digit_addr s r lane parity :=
  regs s r + 64 * Z.of_nat lane + 2 * regs s 9%nat + parity.
Definition digit s r lane parity := signed_byte (mem s (digit_addr s r lane parity)).
Definition parity k : Z := match k with Odd => 1 | _ => 0 end.

(* Address of the first word of this lane’s signed table entry. *)
Definition selected s k lane :=
  match k with
  | Base => regs s 2%nat + 120 * (136 + digit s 1%nat lane 0 + 16 * digit s 1%nat lane 1)
  | _ => key_table s lane + 160 * (8 - digit s 8%nat lane (parity k))
  end.

Definition source s a n := fits64 a n /\ disjoint (regs s 7%nat) 3520 a n.
Record placement pc n s : Prop := {
  output_range : fits64 (regs s 7%nat) 3520;
  output_aligned : regs s 7%nat mod 64 = 0;
  code_range : source s pc n;
  return_range : source s (regs s 4%nat) 8;
  return_rsp : regs s 4%nat + 8 < 2^64;
  pointers_range : source s (regs s 6%nat) 64;
  key_range : forall lane, (lane < 8)%nat -> source s (key_table s lane) (17*160);
  affine_range : source s (regs s 2%nat) (273*120);
  digits_range : forall r, r = 1%nat \/ r = 8%nat -> source s (regs s r) 512;
  pair_range : 0 <= regs s 9%nat < 32;
  signed_digits : forall r lane p, (r = 1%nat \/ r = 8%nat) -> (lane < 8)%nat ->
    0 <= p <= 1 -> -8 <= digit s r lane p < 8
}.

Definition within a n b m := b <= a /\ a+n <= b+m.
Definition input_access s k a width := exists lane, (lane < 8)%nat /\
  match width with
  | 1%nat => k <> Base /\ a = digit_addr s 8%nat lane (parity k)
  | 2%nat => k = Base /\ a = digit_addr s 1%nat lane 0
  | 8%nat => k <> Base /\ a = regs s 6%nat + 8 * Z.of_nat lane
  | 32%nat | 64%nat =>
      within a (Z.of_nat width) (selected s k lane) (8 * Z.of_nat (columns k))
  | _ => False
  end.
Definition reads_safe s k st := forall a n,
  In (a,n) (IndexedLoads.loads (IndexedLoads.summary (load_block k))) ->
  input_access s k (IndexedLoads.eval st a) n.

(* The access log covers all data reads: the prefix is register-only, and
   the packed suffix can only permute registers and store aligned rows. *)
Definition routing_op op := match op with
  | UnpackQ _ _ _ _ | Shuffle _ _ _ _ | StoreAligned _ _ => true
  | _ => false end.

Record stage_contract bs : Prop := {
  linked_code : image = bs /\ valid_code = true;
  access_coverage : IndexedLoads.loads (IndexedLoads.summary prefix) = nil /\
    forall k, forallb routing_op (route k) = true;
  initializes_output : forall k col, (col < columns k)%nat ->
    exists v, stores (fold_left Packed.step (route k) Packed.initial) (first_row k+col)%nat=Some v;
  stage_correct : forall pc s, placement pc (Z.of_nat (length bs)) s ->
    well_formed s ->
    let entry := IndexedLoads.execute prefix s in
    reads_safe s Odd entry /\ reads_safe s Base (phase entry Odd) /\
    reads_safe s Even (phase (phase entry Odd) Base) /\
    let '(ip,out) := run pc s in
    ip = read_word (mem s) (regs s 4%nat) /\
    regs out 4%nat = regs s 4%nat + 8 /\
    (forall r, In r sysv_saved -> regs out r = regs s r) /\
    preserved (fun x => ~destination s x) (mem s) (mem out) /\
    byte_memory (mem out) /\
    (forall k col lane, (col < columns k)%nat -> (lane < 8)%nat ->
      read_word (mem out) (regs s 7%nat + 64 * Z.of_nat (first_row k+col) + 8 * Z.of_nat lane) =
      read_word (mem s) (selected s k lane + 8 * Z.of_nat col))
}.
