From Coq Require Import List PeanoNat ZArith Lia.
From Machine Require Import execution.Packed isa.X86.
Import ListNotations.
Local Open Scope nat_scope.

Inductive instruction :=
| Unpack (high:bool) (d a b:nat) | Join (d a b imm:nat)
| Mask | ShuffleBytes (d a b:nat).
Definition unpack a b lo hi := [Unpack false lo a b; Unpack true hi a b].
Definition join a b lo hi := [Join lo a b 0x88; Join hi a b 0xdd].
Definition transpose first :=
  unpack 8 9 24 25 ++ unpack 10 11 26 27 ++ unpack 12 13 28 29 ++ unpack 14 15 30 31 ++
  join 24 26 8 10 ++ join 28 30 9 11 ++ join 25 27 12 14 ++ join 29 31 13 15 ++
  join 8 9 24 28 ++ join 10 11 26 30 ++ join 12 13 25 29 ++ join 14 15 27 31 ++
  [Mask] ++ map (fun i=>ShuffleBytes (first+i) (24+i) 8) (rev (seq 0 8)).

Definition encode (disp:Z) ins := match ins with
| Unpack h d a b => Packed.encode (Packed.UnpackQ h d a b)
| Join d a b imm => Packed.encode (Packed.Shuffle d a b imm)
| Mask => prefix 1 1 8 0 5 ++ [0x6f;0x05]%Z ++ le32 disp
| ShuffleBytes d a b => rr_w0 2 1 0 d a b end.

(* Each byte carries either its input coordinate or a constant. An unknown
   shuffle control cannot be used as a known permutation. *)
Inductive origin := Input (r i:nat) | Literal (n:nat) | Unknown.
Scheme Equality for origin.
Definition swap i := (i/8 mod 2)*8 + (7-i mod 8).
Definition permute (src : nat -> nat * nat) i :=
  let '(r,j) := src (i/8) in (r,8*j+i mod 8).
Definition read_perm (regs:nat->nat->origin) src i :=
  let '(r,k) := permute src i in regs r k.
Definition step (regs:nat->nat->origin) ins := match ins with
| Unpack h d a b => update regs d (read_perm regs (unpack_source h a b))
| Join d a b imm => update regs d (read_perm regs (shuffle_source a b imm))
| Mask => update regs 8 (fun i => Literal (swap i))
| ShuffleBytes d a b => update regs d (fun i => match regs b i with
  | Literal m => if m <? 128 then regs a (16*(i/16)+m mod 16) else Literal 0
  | _ => Unknown end) end.
Definition route first := fold_left step (transpose first) Input.
Lemma transpose_bytes first w lane b :
  (first = 0 \/ first = 8) -> w<8 -> lane<8 -> b<8 ->
  route first (first+w) (8*lane+b) = Input (8+lane) (8*w+7-b).
Proof.
  assert (C : forallb (fun f => forallb (fun w => forallb (fun l => forallb (fun b =>
    origin_beq (route f (f+w) (8*l+b)) (Input (8+l) (8*w+7-b))) (seq 0 8))
    (seq 0 8)) (seq 0 8)) [0;8] = true) by (vm_compute; reflexivity).
  intros F W L B. apply internal_origin_dec_bl. rewrite forallb_forall in C.
  specialize (C first ltac:(destruct F as [->| ->]; simpl; auto)).
  rewrite forallb_forall in C. specialize (C w ltac:(apply in_seq; lia)).
  rewrite forallb_forall in C. specialize (C lane ltac:(apply in_seq; lia)).
  rewrite forallb_forall in C. apply C. apply in_seq; lia.
Qed.
