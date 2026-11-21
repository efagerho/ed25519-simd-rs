From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls.
From Ed25519Simd.Decode Require Import Glue.
Import ListNotations. Local Open Scope Z_scope.

Inductive callee := Reduce | MultiplyPoint | MakeCandidate.
Inductive op := PushReg (r:nat) | PopReg (r:nat) | Mov (dst src:nat)
 | LoadInput (d:nat)(disp:Z) | SetReg (r:nat)(imm:Z)
 | Reserve | Release | LoadCount | StoreCount | ClearCount | IncCount | CompareFull
 | EncodingOffset | LaneOffset | PointOffset | AddQueue
 | ReadEncoding (i:nat) | WriteEncoding (i:nat) | ReadLanes | ReadLaneCount
 | WriteLanes | WriteLaneCount | Call (c:callee).
Definition candidate_ops := [PushReg 3;PushReg 12;Reserve;Mov 3 7;Mov 12 6;
 Mov 7 4;LoadInput 6 80;Call Reduce;Mov 7 3;Mov 6 12;LoadInput 2 64;
 LoadInput 1 72;Mov 8 4;SetReg 9 1;Call MultiplyPoint;Release;PopReg 12;PopReg 3].
Definition push_ops := [PushReg 3;PushReg 12;PushReg 13;Mov 3 7;Mov 12 8;Mov 13 9;
 LoadCount;Mov 8 0;EncodingOffset] ++
 flat_map (fun i=>[ReadEncoding i;WriteEncoding i]) (seq 0 4) ++
 [LaneOffset;ReadLanes;ReadLaneCount;WriteLanes;WriteLaneCount;PointOffset;AddQueue;
 Call MakeCandidate;LoadCount;IncCount;StoreCount;CompareFull;Mov 7 3;Mov 6 12;Mov 2 13;
 PopReg 13;PopReg 12;PopReg 3].
Definition instr (address:callee->Z) command : fragment := match command with
 | PushReg r=>fixed(reg_byte 0x50 r) | PopReg r=>fixed(reg_byte 0x58 r)
 | Mov d s=>fixed(LinkedCalls.encoding 0 (Copy d s))
 | SetReg r v=>fixed(reg_byte 0xb8 r ++ X86.le32 v)
 | LoadInput d n=>fixed[0x49;0x8b;0x44+8*Z.of_nat d;0x24;n]
 | Reserve=>fixed[0x48;0x81;0xec;0x08;0x02;0;0] | Release=>fixed[0x48;0x81;0xc4;0x08;0x02;0;0]
 | LoadCount=>fixed([0x48;0x8b;0x83]++X86.le32 12928) | StoreCount=>fixed([0x48;0x89;0x83]++X86.le32 12928)
 | ClearCount=>fixed([0x48;0xc7;0x83]++X86.le32 12928++X86.le32 0)
 | IncCount=>fixed[0xff;0xc0] | CompareFull=>fixed[0x83;0xf8;8] | EncodingOffset=>fixed[0x49;0xc1;0xe0;8]
 | LaneOffset=>fixed[0x4c;0x6b;0xc0;80] | PointOffset=>fixed([0x48;0x69;0xf8]++X86.le32 1280)
 | AddQueue=>fixed[0x48;1;0xdf]
 | ReadEncoding i=>fixed([0x62;0xf1;0xfe;0x48;0x6f]++if Nat.eqb i 0 then [2] else [0x42;Z.of_nat i])
 | WriteEncoding i=>fixed([0x62;0xb1;0xfd;0x48;0x7f;0x84;3]++X86.le32(10240+64*Z.of_nat i))
 | ReadLanes=>fixed[0x62;0xf1;0xfe;0x48;0x6f;1] | ReadLaneCount=>fixed[0xc5;0xfa;0x6f;0x49;64]
 | WriteLanes=>fixed([0x62;0xb1;0xfe;0x48;0x7f;0x84;3]++X86.le32 12288)
 | WriteLaneCount=>fixed([0xc4;0xa1;0x7a;0x7f;0x8c;3]++X86.le32 12352)
 | Call c=>invoke(address c) end.

(* Symbolic pointers carry allocation identity. A saved GPR or a borrowed
   buffer cannot alias the queue or an uninitialized stack slot in this model. *)
Inductive region := Stack | Queue | Inputs | Encodings | Metadata | Output | Result
 | Digests | BaseTable | Digits.
Inductive value := Ptr (r:region)(off:Z) | Number (n:Z) | Incoming (r:nat) | Unknown.
Definition off p n := match p with Ptr r a=>Ptr r (a+n) | _=>Unknown end.
Definition plus a b := match a,b with Number n,p | p,Number n=>off p n | _,_=>Unknown end.
Definition times a n := match a with Number x=>Number(x*n) | _=>Unknown end.
Inductive event := Invoke (c:callee)(args:list value)(stack:value)
 | Transfer (size:nat)(from to:value) | Occupied (dst count:value).
Record state := St {regs:nat->value; saved:Z->value; simd:nat->value;
 occupancy:value; zf:bool; events:list event}.
Definition put {T} (xs:nat->T) r v i := if Nat.eqb i r then v else xs i.
Definition initial n pad pushing :=
 let args:=if pushing:bool then [Ptr Queue 0;Ptr Inputs 0;Ptr Encodings 0;Ptr Metadata 0;Ptr Output 0;Incoming 9]
 else [Ptr Result 0;Ptr Inputs 0;Unknown;Unknown;Unknown;Unknown] in
 let rs:=fold_left (fun rs rv=>put rs (fst rv)(snd rv)) (combine [7;6;2;1;8;9]%nat args) Incoming in
 St (put rs 4 (Ptr Stack (8+16*Z.of_nat pad))) (fun _=>Unknown)(fun _=>Unknown)(Number(Z.of_nat n)) false [].

Definition step st op := let r:=regs st in let m:=saved st in let v:=simd st in
 let n:=occupancy st in let z:=zf st in let e:=events st in
 let reg i x:=St(put r i x)m v n z e in
 let load i addr:=St r m (put v i addr) n z e in
 let store i bytes disp:=St r m v n z (Transfer bytes (v i)(off (plus (r 3%nat)(r 8%nat)) disp)::e) in
 match op with
 | PushReg i=>let sp:=off(r 4%nat)(-8) in
   St(put r 4 sp)(match sp with Ptr Stack a=>fun j=>if j=?a then r i else m j | _=>m end)v n z e
 | PopReg i=>let sp:=r 4%nat in St(put(put r i (match sp with Ptr Stack a=>m a | _=>Unknown end))
    4 (off sp 8))m v n z e
 | Reserve=>reg 4%nat (off(r 4%nat)(-520)) | Release=>reg 4%nat (off(r 4%nat)520)
 | Mov d s=>reg d (r s) | SetReg d x=>reg d (Number x)
 | LoadInput d disp=>reg d (match off(r 12%nat)disp with
   | Ptr Inputs 80=>Ptr Digests 0 | Ptr Inputs 64=>Ptr BaseTable 0 | Ptr Inputs 72=>Ptr Digits 0 | _=>Unknown end)
 | LoadCount=>reg 0%nat (match r 3%nat with Ptr Queue 0=>n | _=>Unknown end)
 | StoreCount=>St r m v (r 0%nat) z (Occupied (off(r 3%nat)12928)(r 0%nat)::e)
 | ClearCount=>St r m v (Number 0) z (Occupied (off(r 3%nat)12928)(Number 0)::e)
 | IncCount=>reg 0%nat (match r 0%nat with Number x=>Number ((x+1) mod 2^32) | _=>Unknown end)
 | CompareFull=>St r m v n (match r 0%nat with Number x=>x=?8 | _=>false end)e
 | EncodingOffset=>reg 8%nat (times(r 8%nat)256) | LaneOffset=>reg 8%nat (times(r 0%nat)80)
 | PointOffset=>reg 7%nat (times(r 0%nat)1280) | AddQueue=>reg 7%nat (plus(r 7%nat)(r 3%nat))
 | ReadEncoding i=>load 0%nat (off(r 2%nat)(64*Z.of_nat i))
 | WriteEncoding i=>store 0%nat 64%nat (10240+64*Z.of_nat i)
 | ReadLanes=>load 0%nat (r 1%nat) | ReadLaneCount=>load 1%nat (off(r 1%nat)64)
 | WriteLanes=>store 0%nat 64%nat 12288 | WriteLaneCount=>store 1%nat 16%nat 12352
 | Call c=>let args:=map r (match c with MultiplyPoint=>[7;6;2;1;8;9] | _=>[7;6] end)%nat in
   let clobber i:=if existsb (Nat.eqb i) [3;4;5;12;13;14;15]%nat then r i else Unknown in
   St clobber m (fun _=>Unknown) n false (Invoke c args (r 4%nat)::e) end.
Definition restored st pad := map(regs st)[3;5;12;13;14;15]%nat=map Incoming [3;5;12;13;14;15]%nat /\
 regs st 4%nat=Ptr Stack(8+16*Z.of_nat pad).
Definition candidate_abi := forall pad,(pad<4)%nat ->
 let st:=fold_left step candidate_ops (initial 0 pad false) in
 let sp:=Ptr Stack(16*Z.of_nat pad-528) in
 restored st pad /\ rev(events st)=
 [Invoke Reduce [sp;Ptr Digests 0] sp;Invoke MultiplyPoint
  [Ptr Result 0;Ptr Inputs 0;Ptr BaseTable 0;Ptr Digits 0;sp;Number 1] sp].
Definition push_abi := forall n pad,(n<8)%nat -> (pad<4)%nat ->
 let st:=fold_left step push_ops (initial n pad true) in let i:=Z.of_nat n in
 restored st pad /\ map(regs st)[7;6;2]%nat=[Ptr Queue 0;Ptr Output 0;Incoming 9] /\
 zf st=(i+1=?8) /\ occupancy st=Number(i+1) /\
 rev(events st)=map (fun j=>let d:=64*Z.of_nat j in
  Transfer 64 (Ptr Encodings d)(Ptr Queue (10240+i*256+d))) (seq 0 4) ++
 [Transfer 64 (Ptr Metadata 0)(Ptr Queue(12288+i*80));Transfer 16 (Ptr Metadata 64)(Ptr Queue(12352+i*80));
  Invoke MakeCandidate [Ptr Queue(i*1280);Ptr Inputs 0](Ptr Stack (16*Z.of_nat pad-16));
  Occupied (Ptr Queue 12928)(Number(i+1))].
Lemma candidate_abi_ok : candidate_abi.
Proof. intros pad P;do 4 (destruct pad;[vm_compute;auto|]);lia. Qed.
Lemma push_abi_ok : push_abi.
Proof.
 intros n pad N P; do 8 (destruct n as [|n];[do 4 (destruct pad as [|pad];[vm_compute;auto 8|]);lia|]);lia.
Qed.
