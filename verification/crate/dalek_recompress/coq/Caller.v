From Coq Require Import ZArith List Bool Lia.
From Machine Require Import isa.X86 isa.Instructions execution.MaskTrace execution.LinkedCalls.
From Ed25519Simd.Decode Require Import Kernels Power Image Glue.
From Ed25519Simd.Dalek Require Import FieldOps.
Import ListNotations. Local Open Scope Z_scope.

(* Every label is relative to the recompression entry. Long and short jumps
   use the layout of the same blocks that the symbolic caller traverses. *)
Inductive label := Entry | Init | Forward | MultiplyPrefix | EndPrefix | Advance
 | Gate | Invert | Back | Recover | Score | Parity | Next | Previous | Restore | Empty | Reduce.
Scheme Equality for label.
Definition order := [Entry;Init;Forward;MultiplyPrefix;EndPrefix;Advance;Gate;Invert;Back;
 Recover;Score;Parity;Next;Previous;Restore;Empty;Reduce].
Inductive op := Frame | YCheck | LoadField (base:nat)(disp:Z) | StoreField (base:nat)(disp:Z)
 | Rhs (base:nat)(disp:Z)(lea:bool) | Mul | Bump (sub:bool)(r:nat)(amount:Z)
 | StartInverse | SaveMasks | ScoreMask | Reload | Epilogue | ReduceParity.
Inductive test := NoChunks | First | Last | NoMatch.
Inductive exit := Fall | Branch (t:test)(long:bool)(dst:label) | Jump (dst:label) | ParityBranch (slow:label) | End.
Definition block l : list op * exit := match l with
 | Entry=>([],Branch NoChunks true Empty)
 | Init=>([Frame],Fall)
 | Forward=>([YCheck;LoadField 12 640],Branch First false EndPrefix)
 | MultiplyPrefix=>([Rhs 14 (-320) true;Mul],Fall)
 | EndPrefix=>([],Branch Last false Gate)
 | Advance=>([StoreField 14 0;Bump false 14 320;Bump false 12 1280;
    Bump false 13 256;Bump false 10 2],Jump Forward)
 | Gate=>([],Branch NoMatch true Restore)
 | Invert=>([SaveMasks;StartInverse;StoreField 4 0],Fall)
 | Back=>([Rhs 4 0 false],Branch First true Score)
 | Recover=>([LoadField 14 (-320);Mul;StoreField 4 320;LoadField 12 640;Mul;
    StoreField 4 0;Rhs 4 320 true],Fall)
 | Score=>([LoadField 12 0;Mul],ParityBranch Reduce)
 | Parity=>([ScoreMask],Fall)
 | Next=>([],Branch First false Restore)
 | Previous=>([Bump true 14 320;Bump true 12 1280;Bump true 13 2;Reload],Jump Back)
 | Restore=>([Epilogue],Fall) | Empty=>([],End) | Reduce=>([ReduceParity],Jump Parity) end.

Definition near op dst : fragment := fun pc=>op++le32(dst-pc-Z.of_nat(length op)-4).
Definition rhs_bytes (base:nat) disp (lea:bool) : fragment :=
 let b:=Z.of_nat base in
 if lea then
   let '(mode,displacement):=if (disp=?0) && negb(b mod 8=?5) then (0,[])
     else if (-128<=?disp)&&(disp<?128) then (1,[disp mod 256]) else (2,le32 disp) in
   fixed ([0x4c+b/8;0x8d;modrm mode 8 b]++(if b mod 8=?4 then [0x24] else [])++displacement)
 else fixed [0x49+4*(b/8);0x89;modrm 3 b 8].
Definition chain_op decoder cmd : fragment := match cmd with
 | Save s=>match s with Root=>field_mem true 14 0 | A=>field_mem true 4 0 | B=>field_mem true 4 320 end
 | Product s=>group [match s with Root=>rhs_bytes 14 0 false | A=>rhs_bytes 4 0 true
   | B=>rhs_bytes 4 320 true end;invoke(decoder+0x7b2)]
 | Squares O=>fixed [] | Squares 1=>invoke(decoder+0x59b)
 | Squares n=>group[fixed([0xb9]++le32(Z.of_nat n));invoke(decoder+0x59b);fixed[0xff;0xc9;0x75;0xf7]] end.
Definition fused_load i := let '(dst,bias):=seed_operands i in
 fixed (rm_memory 1 1 0xfb dst bias 12 (320+64*Z.of_nat(dst-10))).
Definition y_check d h := group [
 word_loads 13 (d+0xb00); fixed(rr 2 2 0x39 1 0 6);fixed(MaskTrace.encoding(KmovEax 1));
 fixed[0x41;0x88;0x42;1];y_limbs;ones;
 (fun pc=>mask_bytes 1 (rip_bcst 3 1 0x1e 2 0 (d+0xb88-pc-11))++[5]);
 fixed(field_rows false 5 12 640);group(map fused_load (seq 0 5));invoke(h+0xbae);
 invoke(d+0xa7e);ones;Glue.test 1 (d+0xb88);fixed[0xc5;0xec;0x42;0xc9];
 fixed(MaskTrace.encoding(KmovEax 1));fixed[0x41;0x88;0x02;0x41;0x09;0xc1]].
Definition saved := [3;12;13;14;15]%nat.
Definition frame h := group [fixed[0x55;0x48;0x89;0xe5];
 fixed(flat_map (reg_byte 0x50) saved);fixed([0x48;0x83;0xe4;0xc0;0x48;0x81;0xec]++le32 3264);
 fixed[0x48;0x89;0xfb;0x49;0x89;0xfc;0x49;0x89;0xf5];
 fixed([0x4c;0x8d;0xb4;0x24]++le32 640++[0x45;0x31;0xff]);constants h;
 fixed([0x4c;0x8d;0x94;0x24]++le32 3200++[0x45;0x31;0xc9])].
Definition parity_guard dst := group [fixed(rr 3 1 0x1e 1 4 29++[5]);
 fixed[0xc5;0xf8;0x98;0xc9];near [0x0f;0x85] dst].
Definition exclude_small s := group [fixed[0x49;0x09;0xc7;0x4c;0x89;0xe7];invoke s;
 fixed[0x0f;0xb6;0xc0;0x48;0xf7;0xd0;0x49;0x21;0xc7]].
Definition op_bytes d h s loc cmd : fragment := match cmd with
 | Frame=>frame h | YCheck=>y_check d h
 | LoadField b off=>field_mem false (Z.of_nat b) off | StoreField b off=>field_mem true (Z.of_nat b) off
 | Rhs b off lea=>rhs_bytes b off lea | Mul=>invoke(d+0xa57)
 | Bump sub r amount=>let short:=(-128<=?amount)&&(amount<?128) in fixed([0x48+Z.of_nat r/8;if short then 0x83 else 0x81;
   modrm 3 (if sub then 5 else 0) (Z.of_nat r)]++(if short then [amount mod 256] else le32 amount))
 | SaveMasks=>fixed[0x4d;0x89;0xd5] | StartInverse=>group(map (chain_op d) inverse_chain)
 | ScoreMask=>group [rip(rip_bcst 2 1 0x27 1 0)(d+0xb80);fixed(MaskTrace.encoding(KmovEax 1));
   fixed[0x41;0x32;0x45;1;0xf6;0xd0;0x41;0x22;0x45;0;0x49;0xc1;0xe7;8;0x84;0xc0];
   short 0x74 (loc Next);exclude_small s]
 | Reload=>constants h | Epilogue=>fixed([0x4c;0x89;0xf8;0x48;0x8d;0x65;0xd8]++
   flat_map(reg_byte 0x58)(rev saved)++[0x5d;0xc5;0xf8;0x77])
 | ReduceParity=>group ([alu 20 (Add 0 28)]++flat_map parity_step (seq 1 4)++
   [alu 20 (Shr 20 51);alu 0 (Xor 0 20)]) end.
Definition exit_bytes loc e := match e with
 | ParityBranch dst=>parity_guard(loc dst) | Fall=>fixed [] | End=>fixed[0xc3] | Jump dst=>near [0xe9](loc dst)
 | Branch t long dst=>group [fixed(match t with NoChunks=>[0x31;0xc0;0x48;0x85;0xd2]
   | First=>[0x49;0x39;0xdc] | Last=>[0xff;0xca] | NoMatch=>[0x45;0x85;0xc9] end);
   if long then near [0x0f;0x84](loc dst) else short 0x74(loc dst)] end.
Definition expansion d h s loc l := let '(ops,e):=block l in group
 (map (op_bytes d h s loc) ops ++ [exit_bytes loc e]).
Fixpoint offset l labels := match labels with []=>0 | a::tail=>if label_beq a l then 0 else
 Z.of_nat(length(expansion 0 0 0 (fun _=>0) a 0))+offset l tail end.
Definition loc l := offset l order.
Definition caller_bytes d h s := group(map (expansion d h s loc) order) 0.

(* Check that layout with the actual relocations places every label at its
   computed address and that each rel8 branch reaches its signed target. *)
Fixpoint placement d h s pc labels := match labels with []=>true | l::tail=>
 let stop:=pc+Z.of_nat(length(expansion d h s loc l pc)) in
 let fits delta:=(-128<=?delta)&&(delta<?128) in
 (pc=?loc l) && (match snd(block l) with
   | Branch _ false dst=>fits(loc dst-stop) | _=>true end) &&
 (match l with Parity=>(stop=?loc Next)&&fits(Z.of_nat(length(exclude_small s 0)))
  | _=>true end) && placement d h s stop tail end.
