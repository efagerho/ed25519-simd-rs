From Coq Require Import ZArith List Bool.
From Machine Require Import isa.X86 execution.LinkedCalls.
From Ed25519Simd.Decode Require Import Glue.
From Ed25519Simd.Zip215 Require Caller.
Import ListNotations. Local Open Scope Z_scope.

(* Byte offsets from the four Rust ABI arguments. *)
Definition signature_row := 64.
Definition scalar_offset := 32.
Definition encoding_size := 32.
Definition r_bytes := 256.
Definition digits_offset := 512.
Definition points_offset := 1024.
Definition tables_offset := 3584.
Definition table_stride := 2720.
Definition flags_offset := 64.
Definition r_mask_offset := 72.
Definition table_offset j := tables_offset+table_stride*Z.of_nat j.
Definition saves := [3;12;13;14;15]%nat.
Definition allocation := 64.
Definition frame := 8*Z.of_nat(length saves)+allocation.
Definition disp32 op n := fixed (op++le32 n).
Definition imm8 op n := fixed (op++[n]).
Definition word16 n := [n mod 256;(n/256) mod 256].

Inductive symbol := Common | Strict | Scalar | DecodePair | Tables | Filter.
Inductive block := Scalars | CopyInit | CopyLane | Decode | Build | Reject | Finish | Offsets
                 | Prepare | Screen | ReturnStrict.
Scheme Equality for block.
Definition common := [Scalars;CopyInit;CopyLane;Decode;Build;Reject;Finish;Offsets].
Definition strict := [Prepare;Screen;ReturnStrict].
Definition body (pc:symbol->Z) offsets b : fragment := match b with
 | Scalars=>group [
   fixed(flat_map (reg_byte 0x50) saves);imm8 [0x48;0x83;0xec] allocation;
   fixed [0x48;0x89;0xfb; 0x49;0x89;0xd4; 0x49;0x89;0xcd; 0x49;0x89;0xf7];
   disp32 [0xb8] scalar_offset; fixed [0x62;0xf2;0xfd;0x48;0x7c;0xc0];
   imm8 [0x62;0xf1;0xfd;0x48;0xd4;0x46] (signature_row/64);
   fixed [0x62;0xf1;0xfe;0x48;0x7f;0x04;0x24];
   disp32 [0x48;0x8d;0xbb] digits_offset;fixed [0x48;0x89;0xe6];
   invoke(pc Scalar);fixed [0x85;0xc0]]
 | CopyInit=>fixed [0x41;0x89;0xc6; 0x31;0xc9]
 | CopyLane=>group [fixed [0x49;0x8b;0x3f];imm8 [0x49;0x8b;0x77] signature_row;
   fixed [0xc5;0xfe;0x6f;0x07; 0xc5;0xfe;0x6f;0x0e; 0xc5;0xfd;0x7f;0x04;0x0b];
   disp32 [0xc5;0xfd;0x7f;0x8c;0x0b] r_bytes;imm8 [0x49;0x83;0xc7] 8;
   imm8 [0x83;0xc1] encoding_size;disp32 [0x81;0xf9] r_bytes]
 | Decode=>group [disp32 [0x48;0x8d;0xbb] points_offset;fixed [0x48;0x8d;0x33];
   disp32 [0xba] 2;invoke(pc DecodePair);fixed [0x44;0x0f;0xb6;0xf8; 0xc1;0xe8;0x08];
   imm8 [0x41;0x88;0x45] r_mask_offset;fixed [0x45;0x21;0xfe]]
 | Build=>group [disp32 [0x48;0x8d;0xbb] points_offset;disp32 [0x48;0x8d;0xb3] tables_offset;
   disp32 [0xba] 8;invoke(pc Tables);fixed [0x62;0xf2;0xfd;0x48;0x7c;0xc3];
   rip (fun d=>[0x62;0xf2;0x7d;0x48;0x34;0x0d]++le32 d) offsets;
   fixed [0x62;0xd2;0xfd;0x48;0x7c;0xd4; 0xc4;0xc1;0x78;0x92;0xcf;
          0x62;0xf1;0xfd;0x49;0xd4;0xd1; 0x62;0xd1;0xfe;0x48;0x7f;0x55;0x00;
          0xc4;0xc1;0x78;0x92;0xce; 0x62;0xf2;0x7e;0x48;0x28;0xc1;
          0x62;0xf2;0x7d;0x48;0x1c;0xc0];
   imm8 [0xc4;0xc1;0x79;0xd6;0x45] flags_offset;
   fixed [0xc5;0xf8;0x77];disp32 [0xb8] 1]
 | Reject=>fixed [0x31;0xc0]
 | Finish=>group [imm8 [0x48;0x83;0xc4] allocation;fixed(flat_map (reg_byte 0x58) (rev saves));fixed [0xc3]]
 | Offsets=>fixed(flat_map (fun j=>word16(table_offset j)) (seq 0 8))
 | Prepare=>group [fixed [0x53; 0x48;0x89;0xcb];invoke(pc Common);fixed [0x85;0xc0]]
 | Screen=>group [fixed [0x48;0x89;0xdf];imm8 [0x48;0x8d;0x73] flags_offset;invoke(pc Filter);
   fixed [0x31;0xc0];fixed [0x48;0x83;0x7b;flags_offset;0x00; 0x0f;0x95;0xc0]]
 | ReturnStrict=>fixed [0x5b;0xc3] end.

Definition jump b := match b with
 | Scalars=>Some(Caller.Eq,false,Finish) | CopyLane=>Some(Caller.Ne,true,CopyLane)
 | Decode=>Some(Caller.Eq,true,Reject) | Build=>Some(Caller.Always,true,Finish)
 | Prepare=>Some(Caller.Eq,true,ReturnStrict) | _=>None end.
Definition expand pc addr b := group [body pc (addr Offsets) b;
 match jump b with None=>fixed [] | Some(cc,short,dst)=>Caller.tail cc short (addr dst) end].
Fixpoint offset l bs := match bs with []=>0 | b::rest=>if block_beq l b then 0 else
 Z.of_nat(length(expand (fun _=>0) (fun _=>0) b 0))+offset l rest end.
Definition image pc s bs := let addr b:=pc s+offset b bs in
 group(map (expand pc addr) bs) (pc s).
Fixpoint following b bs := match bs with []=>None | h::t=>if block_beq b h then hd_error t else following b t end.
Definition next bs b zero := match jump b with
 | Some(cc,_,dst)=>if match cc with Caller.Eq=>zero | Caller.Ne=>negb zero | _=>true end
                   then Some dst else following b bs
 | None=>match b with Finish | ReturnStrict | Offsets=>None | _=>following b bs end end.
Definition reaches bs b zero dst := match next bs b zero with
 | Some t=>block_beq t dst | None=>false end.

(* Reject a wrapped short displacement even if its low byte matches the ELF. *)
Definition fits_jump pc s bs b := match jump b with
 | Some(_,small,dst)=>
   let addr t:=pc s+offset t bs in
   let delta:=addr dst-addr b-Z.of_nat(length(expand pc addr b (addr b))) in
   let bound:=if small then 128 else 2^31 in (-bound<=?delta)&&(delta<?bound)
 | None=>true end.
