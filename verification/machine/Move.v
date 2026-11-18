From Coq Require Import ZArith List Bool.
From Machine Require Import X86.
Import ListNotations.
Open Scope Z_scope.

(* VMOVDQA64 register copy. Intel's register intrinsic with k = 0xff
   copies all eight lanes, as does the unmasked encoding used here.
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_mask_mov_epi64
   VMOVDQU64 load uses the same lane copy with a memory source.
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_loadu_epi64 *)
Definition copy (source : Z) := source.

Definition encode_vmovdqa64 dst src := rr 1 1 0x6f dst 0 src.

(* Base plus signed byte displacement. EVEX disp8 uses a 64-byte tuple.
   RSP/R12 need a SIB; RBP/R13 need an explicit displacement even at zero. *)
Definition memory (op : Z) (r : nat) (base disp : Z) :=
  let reg := Z.of_nat r in
  let rm := base mod 8 in
  let scaled := disp / 64 in
  let '(mode, displacement) :=
    if (disp =? 0) && negb (rm =? 5) then (0, [])
    else if (disp mod 64 =? 0) && (-128 <=? scaled) && (scaled <? 128)
         then (1, [scaled mod 256])
         else (2, le32 disp) in
  prefix 1 2 reg 0 base ++ [op; modrm mode reg rm]
  ++ (if rm =? 4 then [0x24] else []) ++ displacement.

(* VMOVDQU64 unaligned load, memory to ZMM.
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_loadu_epi64 *)
Definition encode_load dst base disp := memory 0x6f dst base disp.

(* VMOVDQU64 unaligned store, ZMM to memory.
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_storeu_epi64 *)
Definition encode_store src base disp := memory 0x7f src base disp.
