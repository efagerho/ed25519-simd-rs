From Coq Require Import List ZArith Bool.
From Machine Require Import isa.X86 isa.ProgramLayout execution.LinkedCalls abi.SysV.
From Ed25519Simd.FullLadder Require Import LinkedBytes Seed.
From Ed25519Simd.LadderStep Require LinkedBytes.
Import ListNotations. Local Open Scope nat_scope.
Module L := Ed25519Simd.LadderStep.LinkedBytes.

Inductive ins := Simple (cmd:command) | Align | Allocate (n:Z)
 | Lea8 (d b:nat) (disp:Z) | Reload (wide:bool) (d b:nat) (disp:Z)
 | Zero (d:nat) | Compare (r:nat) (imm:Z) | Dec (r:nat) | Jne (disp:Z)
 | SeedBlock.
Definition rex (wide:bool) r b := let v:=(64+(if wide then 8 else 0)+4*Z.of_nat(r/8)+Z.of_nat(b/8))%Z in
 if Z.eqb v 64 then [] else [v].
Definition encoding pc op : list Z := match op with
 | Simple (Immediate r n)=>rex false 0 r ++ [(184+Z.of_nat(r mod 8))%Z] ++ le32 n
 | Simple cmd=>LinkedCalls.encoding pc cmd
 | Align=>op_bytes (Program [] []) AlignRsp64
 | Allocate n=>op_bytes (Program [] []) (AdjustRsp true n)
 | Lea8 r b d=>rex true r b ++ [0x8d%Z;modrm 1 (Z.of_nat r) (Z.of_nat b);(d mod 256)%Z]
 | Reload w r b d=>rex w r b ++ [0x8b%Z;modrm 1 (Z.of_nat r) (Z.of_nat b);(d mod 256)%Z]
 | Zero r=>rex false r r ++ [0x31%Z;modrm 3 (Z.of_nat r) (Z.of_nat r)]
 | Compare r n=>rex false 7 r ++ [0x83%Z;modrm 3 7 (Z.of_nat r);n]
 | Dec r=>rex false 1 r ++ [0xff%Z;modrm 3 1 (Z.of_nat r)]
 | Jne d=>exit_bytes (JneRel8 d) | SeedBlock=>flat_map Seed.encode Seed.code end.
Definition code :=
 map Simple [Save 5;Copy 5 4;Save 3;Save 12;Save 13;Save 14;Save 15;Save 8;Save 9] ++
 [Align;Allocate 3520] ++
 map Simple [Copy 3 7;Copy 12 6;Copy 13 2;Copy 14 1;Copy 7 4;Immediate 9 31;Invoke stage_pc] ++
 [SeedBlock] ++ map Simple [Copy 7 3;Invoke L.double4_pc;Copy 7 3;LeaSIB 6 4 1280;
 Immediate 2 1;Immediate 1 1;Invoke L.cached_pc;Copy 7 3;LeaSIB 6 4 2240] ++
 [Zero 2;Zero 1;Simple (Invoke L.cached_pc);Simple (Immediate 15 31)] ++
 map Simple [Copy 7 4;Copy 6 12;Copy 2 13;Copy 1 14] ++
 [Reload true 8 5 (-48);Lea8 9 15 (-1);Simple (Invoke stage_pc);Simple (Copy 7 3);
  Simple (Copy 6 4);Zero 2;Compare 15 1;Jne 3;Reload false 2 5 (-56);
  Simple (Invoke L.wrapper_pc);Dec 15;Jne (-52);Lea8 4 5 (-40)] ++
 map Simple [Restore 15;Restore 14;Restore 13;Restore 12;Restore 3;Restore 5;Return].
Fixpoint layout pc ops := match ops with
 | []=>[] | op::t=>let bs:=encoding pc op in let next:=(pc+Z.of_nat(length bs))%Z in
 (pc,(next,op,bs))::layout next t end.
Definition listing := layout entry_pc code.
Definition image := flat_map (fun pair=>snd (snd pair)) listing.

Inductive event := Stage (pair:nat) | SeedXYZ | DoubleFour | Cached (full affine:bool) (row:nat)
 | Ladder (full:bool).
Inductive val := Unknown | Arg (r:nat) | Stack (off:Z) | Num (n:Z) | Caller.
Scheme Equality for val.
Definition offset v d := match v with Stack n=>Stack (n+d) | Num n=>Num (n+d) | _=>Unknown end.
Record state := State { gp:nat->val; slot:Z->val; zf:option bool; trace:list event }.
Definition set s r v := State (Instructions.put (gp s) r v) (slot s) (zf s) (trace s).
Definition unknown_flags s := State (gp s) (slot s) None (trace s).
Definition flagged s r v f := State (Instructions.put (gp s) r v) (slot s) (Some f) (trace s).
Definition initial full := State
 (fun r=>if Nat.eqb r 4 then Stack 0 else if Nat.eqb r 9 then Num (if full:bool then 1 else 0) else Arg r)
 (fun x=>if Z.eqb x 0 then Caller else Unknown) None [].
Definition save s v := match gp s 4 with
 | Stack n=>let a:=(n-8)%Z in if ((-5032 <=? a) && (a+8 <=? 0))%Z then
 Some (State (Instructions.put (gp s) 4 (Stack a)) (fun x=>if Z.eqb x a then v else slot s x)
  (zf s) (trace s)) else None | _=>None end.
Definition known v := match v with Unknown=>false|_=>true end.
Definition mode v := match v with Num Z0=>Some false | Num (Zpos xH)=>Some true | _=>None end.
Definition aligned pad n := Z.eqb ((pad+n) mod 64) 0.
Definition staging pad := (-64-pad-3520)%Z.
Definition return_offset e : Z := match e with
 | Stage n=>if Nat.eqb n 31 then 0x36%Z else 0x355%Z
 | DoubleFour=>0x308%Z | Cached _ true _=>0x322%Z | Cached _ false _=>0x336%Z
 | Ladder _=>0x36b%Z | SeedXYZ=>0%Z end.
Definition call pad next target s :=
 let base:=staging pad in let is r v:=val_beq (gp s r) v in
 let which :=
 if Z.eqb target stage_pc then
   if is 7 (Stack base) && is 6 (Arg 6) && is 2 (Arg 2) && is 1 (Arg 1) && is 8 (Arg 8)
   then match gp s 9 with Num n=>if ((0<=?n)&&(n<?32))%Z then Some (Stage (Z.to_nat n)) else None
                  | _=>None end else None
 else if negb (is 7 (Arg 7)) then None
 else if Z.eqb target L.double4_pc then Some DoubleFour
 else match mode (gp s 2) with None=>None | Some f=>
  if Z.eqb target L.wrapper_pc then if is 6 (Stack base) then Some (Ladder f) else None
  else if Z.eqb target L.cached_pc then match gp s 6,mode (gp s 1) with
   | Stack a,Some aff=>let d:=(a-base)%Z in
     if ((0<=?d)&&(d+(if aff then 960 else 1280)<=?3520)&&(d mod 64 =?0))%Z
     then Some (Cached f aff (Z.to_nat (d/64))) else None | _,_=>None end else None end in
 if is 4 (Stack base) && aligned pad base && ((-5032<=?base-1360)&&(base+3520<=?0))%Z
 then match which with None=>None | Some e=>if Z.eqb next (entry_pc+return_offset e) then
 Some (State (fun r=>if Nat.eqb r 4 || existsb (Nat.eqb r) sysv_saved then gp s r else Unknown)
  (fun x=>if ((x <? base+3520) && (base-1360 <? x+8))%Z then Unknown else slot s x)
  None (e::trace s)) else None end else None.
Definition fetch pc (table:list (Z * (Z * ins * list Z))) := find (fun p=>Z.eqb (fst p) pc) table.
Definition returned s := val_beq (gp s 4) (Stack 0) && val_beq (slot s 0%Z) Caller &&
 forallb (fun r=>val_beq (gp s r) (Arg r)) sysv_saved.
Fixpoint walk table fuel (pad pc:Z) s : option (list event) := match fuel with
 | O=>None | S n=>match fetch pc table with None=>None | Some (_, (next,op,_))=>
 let go := walk table n pad next in
 let load w d addr := match addr with Stack a=>let v:=slot s a in
  if known v then match w,v with true,_=>go (set s d v) | false,Num k=>go (set s d (Num (k mod 2^32))) | _,_=>None end else None
 | _=>None end in
 match op with
 | Simple (Save r)=>match save s (gp s r) with Some t=>go t|_=>None end
 | Simple (Restore r)=>match gp s 4 with Stack a=>if known (slot s a) then
   go (set (set s r (slot s a)) 4 (Stack (a+8))) else None | _=>None end
 | Simple (Copy d r)=>go (set s d (gp s r))
 | Simple (Immediate d k)=>go (set s d (Num (k mod 2^32)))
 | Simple (LeaSIB d b k) | Lea8 d b k=>go (set s d (offset (gp s b) k))
 | Simple (Invoke target)=>match call pad next (call_destination pc target) s with Some t=>go t|_=>None end
 | Simple Return=>if returned s then Some (rev (trace s)) else None
 | Align=>match gp s 4 with Stack a=>go (unknown_flags (set s 4 (Stack (a-(pad+a) mod 64))))|_=>None end
 | Allocate k=>go (unknown_flags (set s 4 (offset (gp s 4) (-k))))
 | Reload w d b k=>load w d (offset (gp s b) k)
 | Zero r=>go (flagged s r (Num 0) true)
 | Compare r k=>match gp s r with Num v=>go (State (gp s) (slot s) (Some (Z.eqb (v mod 2^32) k)) (trace s))|_=>None end
 | Dec r=>match gp s r with Num v=>let t:=((v-1) mod 2^32)%Z in go (flagged s r (Num t) (Z.eqb t 0))|_=>None end
 | Jne k=>match zf s with Some true=>go s | Some false=>walk table n pad (next+k)%Z s | None=>None end
 | SeedBlock=>if val_beq (gp s 4) (Stack (staging pad)) && val_beq (gp s 3) (Arg 7)
   then go (State (Instructions.put (gp s) 0 Unknown) (slot s) (zf s) (SeedXYZ::trace s)) else None
 end end end.
Definition run full pad := walk listing 600 pad entry_pc (initial full).
Definition schedule full := [Stage 31;SeedXYZ;DoubleFour;Cached true true 20;Cached false false 35] ++
 flat_map (fun n=>[Stage n;Ladder (full && Nat.eqb n 0)]) (rev (seq 0 31)).

Definition legal pc op := match op with
 | Simple (Immediate r v)=>Nat.ltb r 16 && unsigned 32 v
 | Simple cmd=>encodable pc cmd | Align=>true | Allocate k=>unsigned 31 k
 | Lea8 d b k | Reload _ d b k=>Nat.ltb d 16 && Nat.ltb b 16 && negb (Nat.eqb (b mod 8) 4) && signed 8 k
 | Zero r | Dec r=>Nat.ltb r 16 | Compare r k=>Nat.ltb r 16 && unsigned 7 k
 | Jne k=>signed 8 k | SeedBlock=>forallb Seed.valid Seed.code end.
Definition valid := forallb (fun p=>let '(pc,(_,op,_)):=p in legal pc op) listing.
