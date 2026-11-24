From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.StoreInstructions
 execution.WordSemantics memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require isa.QwordRegister isa.VectorMoves execution.IndexedLoads.
Import ListNotations. Local Open Scope Z_scope.

(* Scalar and vector-move forms used by scatter and the batch wrapper.
   The PC is a byte offset in the linked text. RET yields an absolute IP. *)
Inductive addr := Address (base:nat) (index:option (nat*Z)) (disp:Z).
Inductive condition := Equal | Unequal | Below | Above | AtLeast.
Inductive instruction :=
| Load64 (r:nat) (a:addr) | Load8 (r:nat) (a:addr) | Store8 (i:indexed_byte)
| CompareImm (r:nat) (k:Z) | Compare (l r:nat) | Test (r:nat)
| Zero32 (r:nat) | OneEax | And8 (d r:nat) | ShrEax | Inc (r:nat)
| RestoreG (r:nat) | Imm32 (r:nat) (imm:Z) | Test32 (r:nat)
| BroadcastG (dst src:nat) | AddVectorMem (dst src:nat) (a:addr)
| SaveG (r:nat) | CopyG (dst src:nat) | LeaG (dst:nat) (a:addr)
| Sub64 (r:nat) (k:Z) | Add32 (r:nat) (k:Z) | Compare32 (r:nat) (k:Z)
| MoveBelow (dst src:nat) | Store64 (r:nat) (a:addr)
| Copy32 (dst src:nat) | StoreAlignedY (r:nat) (a:addr)
| LoadY (r:nat) (a:addr) | StoreY (r:nat) (a:addr)
| VectorMove (op:VectorMoves.operation) | Add64 (r:nat) (k:Z) | CallRelative (disp:Z)
| StoreImmediate (a:addr) (k:Z) | Jump (disp:Z)
| Branch (c:condition) (disp:Z) | Ret
| QwordOp (i:QwordRegister.op)
| AndImmediate (r:nat) (mask:Z) | BroadcastRip (r:nat) (disp:Z)
| AlignedRow (i:VectorMoves.aligned_row).

Definition little32 bs := read_le 4 (fun i=>nth (Z.to_nat i) bs 0) 0.
(* REX-prefixed opcode 89 /r with a register destination. REX.R extends the source
   and REX.B extends the destination. The W bit selects the operand size. *)
Definition reg_move rex m : option (nat*instruction) :=
 if (0x40<=?rex)&&(rex<?0x50)&&(0xc0<=?m)&&(m<?256) then
 let dst:=Z.to_nat (m mod 8+8*(rex mod 2)) in
 let src:=Z.to_nat ((m/8) mod 8+8*((rex/4) mod 2)) in
 Some(3%nat,if 0x48<=?rex then CopyG dst src else Copy32 dst src)
 else None.
(* The inverted EVEX.R and EVEX.R' bits select the bank of eight ZMM
   destinations. RIP-relative addressing fixes the remaining extension bits. *)
Definition broadcast_reg prefix modrm : option nat :=
 let bank:=match prefix with 0xf2=>Some 0 | 0x72=>Some 8 |
   0xe2=>Some 16 | 0x62=>Some 24 | _=>None end in
 if (0<=?modrm)&&(modrm<?64)&&(modrm mod 8=?5) then
   option_map (fun b=>Z.to_nat (b+modrm/8)) bank else None.
Definition decode (bs:list Z) : option (nat*instruction) := match bs with
 | 0x55::_=>Some(1%nat,SaveG 5)
 | 0x48::0x83::0xe4::k::_=>Some(4%nat,AndImmediate 4 (signed_value 128 k))
 | 0x62::p::0xfd::0x48::0x59::m::a::b::c::d::_=>
   option_map (fun r=>(10%nat,BroadcastRip r (displacement32 [a;b;c;d]))) (broadcast_reg p m)
 | 0x5b::_=>Some (1%nat,RestoreG 3)
 | 0x41::0x5c::_=>Some (2%nat,RestoreG 12)
 | 0x41::0x5d::_=>Some (2%nat,RestoreG 13)
 | 0x41::0x5e::_=>Some (2%nat,RestoreG 14)
 | 0x41::0x5f::_=>Some (2%nat,RestoreG 15)
 | 0x41::0x83::0xfc::d::_=>Some (4%nat,Compare32 12 (signed_value 128 d))
 | 0x48::0x81::0xc6::a::b::c::d::_=>Some (7%nat,Add64 6 (displacement32 [a;b;c;d]))
 | 0x49::0x8b::0x3f::_=>Some (3%nat,Load64 7 (Address 15 None 0))
 | 0x49::0x8b::0x77::d::_=>Some (4%nat,Load64 6 (Address 15 None (signed_value 128 d)))
 | 0xc5::0xfe::0x6f::0x07::_=>Some (4%nat,LoadY 0 (Address 7 None 0))
 | 0xc5::0xfe::0x6f::0x0e::_=>Some (4%nat,LoadY 1 (Address 6 None 0))
 | 0xc5::0xfd::0x7f::0x04::0x0b::_=>Some (5%nat,StoreAlignedY 0 (Address 3 (Some (1%nat,1)) 0))
 | 0xc5::0xfd::0x7f::0x8c::0x0b::a::b::c::d::_=>
   Some (9%nat,StoreAlignedY 1 (Address 3 (Some (1%nat,1)) (displacement32 [a;b;c;d])))
 | 0x49::0x83::0xc7::d::_=>Some (4%nat,Add64 15 (signed_value 128 d))
 | 0x48::0x8d::0x33::_=>Some (3%nat,LeaG 6 (Address 3 None 0))
 | 0xba::a::b::c::d::_=>Some (5%nat,Imm32 2 (little32 [a;b;c;d]))
 | 0x48::0x83::0xec::d::_=>Some (4%nat,Sub64 4 (signed_value 128 d))
 | 0x48::0x83::0xc4::d::_=>Some (4%nat,Add64 4 (signed_value 128 d))
 | 0x48::0x81::0xc4::a::b::c::d::_=>Some (7%nat,Add64 4 (displacement32 [a;b;c;d]))
 | 0x48::0x8d::0x93::a::b::c::d::_=>Some (7%nat,LeaG 2 (Address 3 None (displacement32 [a;b;c;d])))
 | 0x48::0x8d::0xb3::a::b::c::d::_=>Some (7%nat,LeaG 6 (Address 3 None (displacement32 [a;b;c;d])))
 | 0x48::0x8d::0xbb::a::b::c::d::_=>Some (7%nat,LeaG 7 (Address 3 None (displacement32 [a;b;c;d])))
 | 0x48::0x8d::0xbc::0x24::a::b::c::d::_=>Some (8%nat,LeaG 7 (Address 4 None (displacement32 [a;b;c;d])))
 | 0x4d::0x85::0xe4::_=>Some (3%nat,Test 12)
 | 0x0f::0x85::a::b::c::d::_=>Some (6%nat,Branch Unequal (displacement32 [a;b;c;d]))
 | 0x85::0xc0::_=>Some (2%nat,Test32 0)
 | 0xb8::0x20::0::0::0::_=>Some (5%nat,Imm32 0 32)
 | 0x62::0xf2::0xfd::0x48::0x7c::0xc0::_=>Some (6%nat,BroadcastG 0 0)
 | 0x62::0xf1::0xfd::0x48::0xd4::0x46::d::_=>
   Some (7%nat,AddVectorMem 0 0 (Address 6 None (64*signed_value 128 d)))
 | 0x53::_=>Some (1%nat,SaveG 3)
 | 0x41::0x54::_=>Some (2%nat,SaveG 12)
 | 0x41::0x55::_=>Some (2%nat,SaveG 13)
 | 0x41::0x56::_=>Some (2%nat,SaveG 14)
 | 0x41::0x57::_=>Some (2%nat,SaveG 15)
 | 0x48::0x81::0xec::a::b::c::d::_=>Some (7%nat,Sub64 4 (displacement32 [a;b;c;d]))
 | 0x4c::0x89::0x84::0x24::a::b::c::d::_=>Some (8%nat,Store64 8 (Address 4 None (displacement32 [a;b;c;d])))
 | 0x4c::0x89::0x8c::0x24::a::b::c::d::_=>Some (8%nat,Store64 9 (Address 4 None (displacement32 [a;b;c;d])))
 | 0x49::0x83::0xfc::d::_=>Some (4%nat,CompareImm 12 (word (signed_value 128 d)))
 | 0x0f::0x82::a::b::c::d::_=>Some (6%nat,Branch Below (displacement32 [a;b;c;d]))
 | 0x48::0xc7::0x84::0x24::a::b::c::d::u::v::w::x::_=>
   Some (12%nat,StoreImmediate (Address 4 None (displacement32 [a;b;c;d])) (displacement32 [u;v;w;x]))
 | 0x49::0x83::0xec::d::_=>Some (4%nat,Sub64 12 (signed_value 128 d))
 | 0x4c::0x89::0xa4::0x24::a::b::c::d::_=>Some (8%nat,Store64 12 (Address 4 None (displacement32 [a;b;c;d])))
 | 0x4b::0x8d::0x04::0xa4::_=>Some (4%nat,LeaG 0 (Address 12 (Some (12%nat,4)) 0))
 | 0x48::0x8d::0x7c::0xc3::d::_=>Some (5%nat,LeaG 7 (Address 3 (Some (0%nat,8)) (signed_value 128 d)))
 | 0x48::0x8d::0x1c::0x24::_=>Some (4%nat,LeaG 3 (Address 4 None 0))
 | 0x45::0x31::0xe4::_=>Some (3%nat,Zero32 12)
 | 0x31::0xc9::_=>Some (2%nat,Zero32 1)
 | 0xeb::d::_=>Some (2%nat,Jump (signed_value 128 d))
 | 0xe9::a::b::c::d::_=>Some (5%nat,Jump (displacement32 [a;b;c;d]))
 | 0xc5::0xfe::0x6f::0x06::_=>Some (4%nat,LoadY 0 (Address 6 None 0))
 | 0x48::0x8b::0x46::d::_=>Some (4%nat,Load64 0 (Address 6 None (signed_value 128 d)))
 | 0xc5::0xfe::0x7f::0x04::0x0b::_=>Some (5%nat,StoreY 0 (Address 3 (Some (1%nat,1)) 0))
 | 0x48::0x89::0x44::0x0b::d::_=>Some (5%nat,Store64 0 (Address 3 (Some (1%nat,1)) (signed_value 128 d)))
 | 0x48::0x8d::0x46::d::_=>Some (4%nat,LeaG 0 (Address 6 None (signed_value 128 d)))
 | 0x48::0x39::0xfe::_=>Some (3%nat,Compare 6 7)
 | 0x48::0x0f::0x42::0xf0::_=>Some (4%nat,MoveBelow 6 0)
 | 0x83::0xc1::d::_=>Some (3%nat,Add32 1 (signed_value 128 d))
 | 0x81::0xf9::a::b::c::d::_=>Some (6%nat,Compare32 1 (little32 [a;b;c;d]))
 | 0x75::d::_=>Some (2%nat,Branch Unequal (signed_value 128 d))
 | 0x48::0x8b::0x4f::0x48::_ => Some (4%nat,Load64 1 (Address 7 None 72))
 | 0x48::0x83::0xf9::0x08::_ => Some (4%nat,CompareImm 1 8)
 | 0x45::0x31::0xc0::_ => Some (3%nat,Zero32 8)
 | 0x48::0x85::0xc9::_ => Some (3%nat,Test 1)
 | 0x48::0x85::0xf6::_ => Some (3%nat,Test 6)
 | 0x4e::0x8b::0x4c::0xc7::0x08::_ => Some (5%nat,Load64 9 (Address 7 (Some (8%nat,8)) 8))
 | 0x49::0x39::0xd1::_ => Some (3%nat,Compare 9 2)
 | 0x46::0x8a::0x14::0x07::_ => Some (4%nat,Load8 10 (Address 7 (Some (8%nat,1)) 0))
 | 0x41::0x20::0xc2::_ => Some (3%nat,And8 10 0)
 | 0x46::0x88::0x14::0x0e::_ => Some (4%nat,Store8 (IndexedByte 10 6 9))
 | 0xd1::0xe8::_ => Some (2%nat,ShrEax)
 | 0x49::0xff::0xc0::_ => Some (3%nat,Inc 8)
 | 0x49::0x39::0xc8::_ => Some (3%nat,Compare 8 1)
 | 0xb8::0x01::0x00::0x00::0x00::_ => Some (5%nat,OneEax)
 | 0x31::0xc0::_ => Some (2%nat,Zero32 0)
 | 0x77::d::_ => Some (2%nat,Branch Above (signed_value 128 d))
 | 0x74::d::_ => Some (2%nat,Branch Equal (signed_value 128 d))
 | 0x73::d::_ => Some (2%nat,Branch AtLeast (signed_value 128 d))
 | 0x72::d::_ => Some (2%nat,Branch Below (signed_value 128 d))
 | 0x0f::0x84::a::b::c::d::_ => Some (6%nat,Branch Equal (displacement32 [a;b;c;d]))
 | 0x48::0x8b::0x43::d::_=>Some (4%nat,Load64 0 (Address 3 None (signed_value 128 d)))
 | 0x48::0x8b::0x83::a::b::c::d::_=>Some (7%nat,Load64 0 (Address 3 None (displacement32 [a;b;c;d])))
 | 0x48::0x89::0x84::0x24::a::b::c::d::_=>Some (8%nat,Store64 0 (Address 4 None (displacement32 [a;b;c;d])))
 | 0x48::0x81::0xc3::a::b::c::d::_=>Some (7%nat,Add64 3 (displacement32 [a;b;c;d]))
 | 0x48::0x8d::0xb4::0x24::a::b::c::d::_=>Some (8%nat,LeaG 6 (Address 4 None (displacement32 [a;b;c;d])))
 | 0x48::0x8b::0x94::0x24::a::b::c::d::_=>Some (8%nat,Load64 2 (Address 4 None (displacement32 [a;b;c;d])))
 | 0x48::0x8d::0x8c::0x24::a::b::c::d::_=>Some (8%nat,LeaG 1 (Address 4 None (displacement32 [a;b;c;d])))
 | 0x4c::0x8d::0x87::a::b::c::d::_=>Some (7%nat,LeaG 8 (Address 7 None (displacement32 [a;b;c;d])))
 | 0xe8::a::b::c::d::_=>Some (5%nat,CallRelative (displacement32 [a;b;c;d]))
 | 0xc3::_ => Some (1%nat,Ret)
 | rex::0x89::m::_=>reg_move rex m
 | _=>match VectorMoves.decode bs with Some(n,i)=>Some(n,VectorMove i)
      | None=>match QwordRegister.decode bs with Some(n,i)=>Some(n,QwordOp i)
              | None=>option_map (fun '(n,i)=>(n,AlignedRow i)) (VectorMoves.decode_row bs) end end end.

Definition effective s a := match a with Address b ix d=>word (regs s b+
 (match ix with Some (i,k)=>regs s i*k | None=>0 end)+d) end.
Definition low_byte s d v := set s d (regs s d-regs s d mod 256+v mod 256).
Definition with_zf s z := CPU (regs s) (vectors s) (Some z) (mem s).
Inductive location := Running (off:Z) | Returned (ip:Z).
Record state := State { loc:location; cpu_state:cpu; cf:option bool }.
Definition eval_condition cc z c :=
 match cc with Equal=>z | Unequal=>option_map negb z | Below=>c | AtLeast=>option_map negb c
 | Above=>match z,c with Some z,Some c=>Some (negb(z||c)) | _,_=>None end end.
Definition vector_dest s r (v:nat->Z) := CPU (regs s) (fun j=>put (vectors s j) r (v j)) (flag s) (mem s).
Definition vector_load s j b d := read_word (mem s) (word(regs s b+d)+8*Z.of_nat j).
Definition qword_op next s i := match i with
 | QwordRegister.Alu (d,op)=>Some(vector_dest s d (fun j=>bits (vector_load s j) (vectors s j) d op))
 | QwordRegister.Or d a b=>Some(vector_dest s d (fun j=>word(Z.lor (vectors s j a) (vectors s j b))))
 | QwordRegister.Permute2 d idx b=>Some(vector_dest s d (fun j=>
     let k:=vectors s j idx mod 16 in vectors s (Z.to_nat(k mod 8)) (if k<?8 then d else b)))
 | QwordRegister.AlignedRip d disp=>let addr:=word(next+disp) in
   if addr mod 64=?0 then Some(vector_dest s d (fun j=>read_word (mem s) (addr+8*Z.of_nat j))) else None
 | QwordRegister.SubRip d a disp=>let v:=read_word (mem s) (word(next+disp)) in
   Some(vector_dest s d (fun j=>Arithmetic.vpsubq (vectors s j a) v)) end.

Lemma qword_state next s i out : qword_op next s i=Some out ->
 mem out=mem s /\ regs out=regs s /\ flag out=flag s.
Proof.
 destruct i as [[d op]| | | |];cbn [qword_op];try destruct (_=?0);intro R;try discriminate;
 injection R as <-;repeat split;reflexivity.
Qed.

Definition step origin off n op s carry : option (state*list store) :=
 let next:=off+Z.of_nat n in
 let go s c := Some (State (Running next) s c,[]) in
 let cmp a b:=go (with_zf s (a=?b)) (Some (a<?b)) in
 match op with
 | Load64 r a=>go (set s r (read_word (mem s) (effective s a))) carry
 | Load8 r a=>go (low_byte s r (mem s (effective s a))) carry
 | Store8 i=>let '(out,ws):=byte_step (word (origin+off)) i s in
      Some (State (Running next) out carry,ws)
 | CompareImm r k=>cmp (word (regs s r)) k
 | Compare l r=>cmp (word (regs s l)) (word (regs s r))
 | Test r=>go (with_zf s (word(regs s r)=?0)) (Some false)
 | OneEax=>go (set s 0 1) carry
 | Zero32 r=>go (with_zf (set s r 0) true) (Some false)
 | And8 d r=>let v:=Z.land (regs s d mod 256) (regs s r mod 256) in
      go (with_zf (low_byte s d v) (v=?0)) (Some false)
 | ShrEax=>let v:=regs s 0%nat mod 2^32 in let t:=v/2 in
      go (with_zf (set s 0 t) (t=?0)) (Some (Z.odd v))
 | Inc r=>let t:=word(regs s r+1) in go (with_zf (set s r t) (t=?0)) carry
 | RestoreG r=>go (pop s r) carry
 | Imm32 r k=>go (set s r (k mod 2^32)) carry
 | Test32 r=>go (with_zf s (regs s r mod 2^32=?0)) (Some false)
 | BroadcastG d r=>go (CPU (regs s) (fun j=>Instructions.put (vectors s j) d (regs s r))
                            (flag s) (mem s)) carry
 | AddVectorMem d r a=>let base:=effective s a in
   let lane j:=word (vectors s j r+read_word (mem s) (base+8*Z.of_nat j)) in
   go (CPU (regs s) (fun j=>Instructions.put (vectors s j) d (lane j)) (flag s) (mem s)) carry
 | SaveG r=>Some (State (Running next) (snd (caller_step origin off (Save r) s)) carry,
                    caller_stores origin off (Save r) s)
 | Copy32 d r=>go (set s d (regs s r mod 2^32)) carry
 | CopyG d r=>go (set s d (regs s r)) carry
 | LeaG d a=>go (set s d (effective s a)) carry
 | Sub64 r k=>let a:=word (regs s r) in let b:=word k in let v:=word (a-b) in
   go (with_zf (set s r v) (v=?0)) (Some (a<?b))
 | Add32 r k=>let m:=2^32 in let a:=regs s r mod m+k mod m in let v:=a mod m in
   go (with_zf (set s r v) (v=?0)) (Some (m<=?a))
 | Compare32 r k=>cmp (regs s r mod 2^32) (k mod 2^32)
 | MoveBelow d r=>option_map (fun b:bool=>(State (Running next)
         (if b then set s d (regs s r) else s) carry,[])) carry
 | Store64 r a=>let w:=qword (word (origin+off)) (effective s a) (regs s r) in
   Some (State (Running next) (with_words s (regs s) (commit (mem s) w)) carry,[w])
 | LoadY r a=>let base:=effective s a in
   let lanes:=fun j=>if (j<?4)%nat then read_word (mem s) (base+8*Z.of_nat j) else 0 in
   go (CPU (regs s) (fun j=>Instructions.put (vectors s j) r (lanes j)) (flag s) (mem s)) carry
 | StoreAlignedY r a=>
   let dst:=effective s a in
   if dst mod 32=?0 then
     let w:=Store (word (origin+off)) dst 32 (vector_byte (fun j=>vectors s j r)) in
     Some (State (Running next) (with_words s (regs s) (commit (mem s) w)) carry,[w])
   else None
 | StoreY r a=>let w:=Store (word (origin+off)) (effective s a) 32 (vector_byte (fun j=>vectors s j r)) in
   Some (State (Running next) (with_words s (regs s) (commit (mem s) w)) carry,[w])
 | VectorMove (VectorMoves.Input i)=>go (IndexedLoads.execute [i] s) carry
 | VectorMove (VectorMoves.Output src base disp)=>
   let w:=vector (word (origin+off)) (word (regs s base+disp)) (fun j=>vectors s j src) in
   Some (State (Running next) (with_words s (regs s) (commit (mem s) w)) carry,[w])
 | AlignedRow i=>let b:=VectorMoves.gpr i in let d:=VectorMoves.offset i in
   let addr:=word(regs s b+d) in let r:=VectorMoves.zmm i in
   if addr mod 64=?0 then
     if VectorMoves.writing i then
       let w:=vector (word(origin+off)) addr (fun j=>vectors s j r) in
       Some(State (Running next) (with_words s (regs s) (commit (mem s) w)) carry,[w])
     else go (vector_dest s r (fun j=>vector_load s j b d)) carry
   else None
 | Add64 r k=>let sum:=word (regs s r)+word k in let v:=word sum in
   go (with_zf (set s r v) (v=?0)) (Some (2^64<=?sum))
 | CallRelative d=>
   let target:=next+d in
   let child:=push s (origin+next) in
   Some (State (Running (word (origin+target)-origin)) child carry,
         [qword (word (origin+off)) (word (regs s 4%nat-8)) (origin+next)])
 | StoreImmediate a k=>let w:=qword (word (origin+off)) (effective s a) k in
   Some (State (Running next) (with_words s (regs s) (commit (mem s) w)) carry,[w])
 | Jump d=>Some (State (Running (next+d)) s carry,[])
 | Branch cc d=>option_map (fun take:bool=>(State (Running (if take then next+d else next)) s carry,[]))
     (eval_condition cc (flag s) carry)
 | QwordOp i=>option_map (fun v=>(State (Running next) v carry,[])) (qword_op (origin+next) s i)
 | AndImmediate r k=>let v:=word (Z.land (regs s r) k) in go (with_zf (set s r v) (v=?0)) (Some false)
 | BroadcastRip r d=>let v:=read_word (mem s) (word (origin+next+d)) in
   go (CPU (regs s) (fun j=>Instructions.put (vectors s j) r v) (flag s) (mem s)) carry
 | Ret=>let '(ip,out):=caller_step 0 0 Return s in Some (State (Returned ip) out carry,[])
 end.

Definition fetch origin text st := match loc st with Returned _=>None | Running off=>
 if off<?0 then None else
 match decode (skipn (Z.to_nat off) text) with Some (n,op)=>step origin off n op (cpu_state st) (cf st)
 | None=>None end end.
Inductive steps origin text : state -> list store -> state -> Prop :=
| stop s : steps origin text s [] s
| advance s mid last ws tail : fetch origin text s=Some(mid,ws) ->
    steps origin text mid tail last -> steps origin text s (ws++tail) last.

Lemma step_memory o off n op s c t ws : step o off n op s c=Some(t,ws) ->
 mem (cpu_state t)=WriteTrace.replay (mem s) ws.
Proof.
 destruct op;cbn [step];try solve [intro E;injection E as <- <-;reflexivity].
 - destruct c as [[]|];intro E;try discriminate;injection E as <- <-;reflexivity.
 - destruct (_=?0);intro E;try discriminate;injection E as <- <-;reflexivity.
 - destruct op;intro E;injection E as <- <-;reflexivity.
 - destruct (eval_condition _ _ _) as [[]|];intro E;try discriminate;injection E as <- <-;reflexivity.
 - destruct (qword_op _ _ _) as [v|] eqn:V;intro E;try discriminate;injection E as <- <-;exact (proj1(qword_state _ _ _ _ V)).
 - destruct (_=?0), (VectorMoves.writing i);intro E;try discriminate;injection E as <- <-;reflexivity.
Qed.
Theorem steps_memory o text s ws t : steps o text s ws t ->
 mem (cpu_state t)=WriteTrace.replay (mem (cpu_state s)) ws.
Proof.
 induction 1 as [|s mid last ws tail F R IH];[reflexivity|].
 unfold fetch in F;destruct (loc s);try discriminate. destruct (_<?_);try discriminate.
 destruct (decode _) as [[n op]|];try discriminate. rewrite replay_app,<-(step_memory _ _ _ _ _ _ _ _ F);exact IH.
Qed.

Fixpoint observe fuel origin text st : state * list store := match fuel with
| O=>(st,[]) | S n=>match fetch origin text st with
 | Some (mid,ws)=>let '(t,tail):=observe n origin text mid in (t,ws++tail)
 | None=>(st,[]) end end.
Lemma observe_steps fuel origin text : forall st,
 let '(t,ws):=observe fuel origin text st in steps origin text st ws t.
Proof.
 induction fuel as [|n IH];intros st;cbn [observe];[constructor|].
 destruct (fetch _ _ _) as [[mid ws]|] eqn:F;[|constructor].
 specialize (IH mid);destruct (observe _ _ _ _) as [t tail];eapply advance;eauto.
Qed.

(* Any prefix starting at the same state is an initial segment of a known
   terminating execution. This also supplies progress at every live prefix. *)
Lemma prefix_of_return o text s full last : steps o text s full last ->
 forall ip, loc last=Returned ip ->
 forall pre mid, steps o text s pre mid ->
 exists tail, full=pre++tail /\ steps o text mid tail last.
Proof.
 induction 1 as [s|s next last ws rest F R IH];intros ip End pre mid P.
 - inversion P as [|a b f w t Step Run];subst.
   + exists [];split;[reflexivity|constructor].
   + unfold fetch in Step;rewrite End in Step;discriminate.
 - inversion P as [|a b f w t Step Run];subst.
   + exists (ws++rest);split;[reflexivity|eapply advance;eauto].
   + rewrite F in Step;injection Step as <- <-.
     destruct (IH ip End _ _ Run) as [tail [-> T]]. exists tail;split;[apply app_assoc|exact T].
Qed.
