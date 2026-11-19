From Coq Require Import List ZArith Bool.
From Machine Require Import Instructions X86.
From Machine Require Move.
Import ListNotations.
Open Scope Z_scope.

(* Symbol-relative instruction addresses. A vector fragment is a shared list
   of straight-line instructions, expanded in place by both the encoder and
   the interpreter. These are the scalar operand forms supported so far. *)
Inductive operation :=
| Mov32 (dst : nat) (imm : Z) | MovAbsRax (imm : Z)
| BroadcastRax (dst : nat) | AdjustRsp (subtract : bool) (imm : Z)
| LeaR8Rsp (disp : Z) | DecEcx
| LoadZmm (dst base : nat) (disp : Z) | StoreZmm (src base : nat) (disp : Z)
| VectorCode (fragment : nat) | ZeroUpper
| MovReg (dst src : nat) | AlignRsp64 | LeaR8Rsi (disp : Z).
Inductive exit := Next | CallRel32 (disp : Z) | JneRel8 (disp : Z) | Ret | PushRbp | PopRbp.
Record block := Block { start : Z; body : list operation; terminator : exit }.
Inductive section := Code (b : block) | Padding (bytes : list Z).
Record program := Program { fragments : list (list instruction); sections : list section }.

Definition fragment_code p id := nth id (fragments p) [].
(* Scalar encodings: Intel SDM vol. 2, MOV, LEA, ADD/SUB, DEC.
   https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html
   The vector moves use the encoders in Machine.Move. VPBROADCASTQ and VZEROUPPER:
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm512_set1_epi64
   https://www.intel.com/content/www/us/en/docs/intrinsics-guide/index.html#text=_mm256_zeroupper *)
Definition op_bytes p op := match op with
 | Mov32 d n => [0xb8 + Z.of_nat d] ++ le32 n
 | MovAbsRax n => [0x48;0xb8] ++ le32 n ++ le32 (n / 2^32)
 | BroadcastRax d => rr 2 1 0x7c d 0 0
 | AdjustRsp sub n => [0x48;0x81;if sub then 0xec else 0xc4] ++ le32 n
 | LeaR8Rsp d => if d =? 0 then [0x4c;0x8d;4;0x24]
                  else [0x4c;0x8d;0x84;0x24] ++ le32 d
 | DecEcx => [0xff;0xc9]
 | LoadZmm d b n => Move.encode_load d (Z.of_nat b) n
 | StoreZmm s b n => Move.encode_store s (Z.of_nat b) n
 | VectorCode id => flat_map encode (fragment_code p id)
 | ZeroUpper => [0xc5;0xf8;0x77]
 | MovReg d s => [0x48 + 4*Z.of_nat (s/8) + Z.of_nat (d/8); 0x89;
                   0xc0 + 8*Z.of_nat (s mod 8) + Z.of_nat (d mod 8)]
 | AlignRsp64 => [0x48;0x83;0xe4;0xc0]
 | LeaR8Rsi d => [0x4c;0x8d;0x86] ++ le32 d
 end.
Definition exit_bytes e := match e with
 | Next => [] | CallRel32 d => 0xe8 :: le32 d
 | JneRel8 d => [0x75;d mod 256] | Ret => [0xc3]
 | PushRbp => [0x55] | PopRbp => [0x5d] end.
Definition block_bytes p b := flat_map (op_bytes p) (body b) ++ exit_bytes (terminator b).
Definition image p := flat_map (fun s => match s with
 | Code b => block_bytes p b | Padding bytes => bytes end) (sections p).
Definition after p b := start b + Z.of_nat (length (block_bytes p b)).
Fixpoint lookup ss pc := match ss with
 | [] => None
 | Code b :: rest => if start b =? pc then Some b else lookup rest pc
 | Padding _ :: rest => lookup rest pc end.
Definition unsigned bits n := (0 <=? n) && (n <? 2^bits).
Definition signed bits n := (-2^(bits-1) <=? n) && (n <? 2^(bits-1)).
Definition valid_op p op := match op with
 | Mov32 d n => Nat.ltb d 8 && unsigned 32 n
 | MovAbsRax n => unsigned 64 n | BroadcastRax d => Nat.ltb d 32
 | AdjustRsp _ n | LeaR8Rsp n => signed 32 n
 | DecEcx | ZeroUpper | AlignRsp64 => true
 | MovReg d s => Nat.ltb d 16 && Nat.ltb s 16
 | LeaR8Rsi n => signed 32 n
 | LoadZmm d b n | StoreZmm d b n => encodable (d, Load b n)
 | VectorCode id => Nat.ltb id (length (fragments p)) && forallb encodable (fragment_code p id)
 end.
Definition starts_block p pc := match lookup (sections p) pc with Some _ => true | None => false end.
Definition valid_exit p b := let n := after p b in match terminator b with
 | Next | PushRbp | PopRbp => starts_block p n | Ret => true
 | CallRel32 d => signed 32 d && starts_block p (n+d) && starts_block p n
 | JneRel8 d => signed 8 d && starts_block p (n+d) && starts_block p n end.
Fixpoint layout_ok p pc ss := match ss with
 | [] => true
 | Padding bytes :: rest => forallb (unsigned 8) bytes && layout_ok p (pc+Z.of_nat (length bytes)) rest
 | Code b :: rest => (start b =? pc) && (pc <? after p b) &&
     forallb (valid_op p) (body b) && valid_exit p b && layout_ok p (after p b) rest end.
Definition valid_program p := starts_block p 0 && layout_ok p 0 (sections p).
