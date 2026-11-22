From Coq Require Import List ZArith Bool.
From Machine Require Import isa.X86 isa.Instructions execution.MaskTrace.
From Ed25519Simd.Decode Require Import Glue Image.
From Ed25519Simd.Dalek Require Import Caller FieldOps.
From Ed25519Simd.PostHash Require Staging.
Import ListNotations. Local Open Scope Z_scope.

(* Each block includes the instructions setting its outgoing condition flags.
   Both the control-flow interpreter and the encoder consume [exit_of]. *)
Inductive symbol := Candidate | Scatter | Decoded | Push | CheckR | Flush
 | Digest | Ladder | Torsion | DecodeR | Exact.
Inductive label :=
 | MakeProduct
 | LaneCount | StartLanes | ReadIndex | WriteLane | Success | BadIndex
 | DecodedCheck
 | Enqueue | Queued
 | CheckFirst | CheckSecond | ReturnChecked
 | Count | Empty | Setup | StartProbe | Probe | ProbeHit | AdvanceProbe | NoExact | Recompress | Resolve | Chunk | ChooseOne | Adjacent | ChoosePair | Check | SaveOne | SavePair | Next | StartScore | Score | NextScore | Restore
 .
Scheme Equality for label.
Definition order s : list label := match s with
 | Candidate=>[MakeProduct]
 | Scatter=>[LaneCount;StartLanes;ReadIndex;WriteLane;Success;BadIndex]
 | Decoded=>[DecodedCheck]
 | Push=>[Enqueue;Queued]
 | CheckR=>[CheckFirst;CheckSecond;ReturnChecked]
 | Flush=>[Count;Empty;Setup;StartProbe;Probe;ProbeHit;AdvanceProbe;NoExact;Recompress;Resolve;Chunk;ChooseOne;Adjacent;ChoosePair;Check;SaveOne;SavePair;Next;StartScore;Score;NextScore;Restore]
 | _=>[] end.
Inductive condition := Eq | Ne | Below | AtLeast | Above | Always.
Inductive target := Local (l:label) | Entry (s:symbol).
Inductive exit := Fall | Ret | Jump (cc:condition)(short_form:bool)(dest:target).
Definition exit_of l := match l with
 | MakeProduct=>Ret
 | LaneCount=>Jump Above true (Local BadIndex)
 | StartLanes=>Jump Eq true (Local Success)
 | ReadIndex=>Jump AtLeast true (Local BadIndex)
 | WriteLane=>Jump Below true (Local ReadIndex)
 | Success=>Ret
 | BadIndex=>Ret
 | DecodedCheck=>Jump Always false (Entry Scatter)
 | Enqueue=>Jump Eq false (Entry Flush)
 | Queued=>Ret
 | CheckFirst=>Jump Eq true (Local ReturnChecked)
 | ReturnChecked=>Ret
 | Count=>Jump Ne true (Local Setup)
 | Empty=>Ret
 | Setup=>Jump Below false (Local Resolve)
 | Probe=>Jump Ne true (Local AdvanceProbe)
 | ProbeHit=>Jump Eq true (Local Recompress)
 | AdvanceProbe=>Jump Ne false (Local Probe)
 | NoExact=>Jump Always true (Local Resolve)
 | Chunk=>Jump Eq true (Local Next)
 | ChooseOne=>Jump AtLeast true (Local Check)
 | Adjacent=>Jump Eq true (Local Check)
 | Check=>Jump Eq true (Local SavePair)
 | SaveOne=>Jump Always true (Local Next)
 | Next=>Jump Below true (Local Chunk)
 | Score=>Jump Eq true (Local Restore)
 | NextScore=>Jump Below true (Local Score)
 | Restore=>Ret
 | _=>Fall end.
Definition opcode cc := match cc with Eq=>0x74 | Ne=>0x75 | Below=>0x72 | AtLeast=>0x73
 | Above=>0x77 | Always=>0xeb end.
Definition tail cc (short_form:bool) dst : fragment := if short_form then short (opcode cc) dst else
 near (match cc with Always=>[0xe9] | _=>[0x0f;opcode cc+16] end) dst.
Definition probe_y d h := group [word_loads 6 (d+0xb00);y_limbs;
 fixed(field_rows false 5 7 640);
 group(map (fun i=>let '(dst,bias):=seed_operands i in
 fixed(rm_memory 1 1 0xfb dst bias 7 (320+64*Z.of_nat i))) (seq 0 5));
 invoke(h+0xbae);invoke(d+0xa7e);ones;Glue.test 1 (d+0xb88)].

Definition staging pc:=Staging.instr (fun c=>match c with Staging.Reduce=>pc Digest
 | Staging.MultiplyPoint=>pc Ladder | Staging.MakeCandidate=>pc Candidate end).
Definition body (pc:symbol->Z) l : fragment := match l with
 | MakeProduct=>group(map (staging pc) (Staging.candidate_ops true))
 | LaneCount=>group [
   fixed [0x48;0x8b;0x4f;0x48] (* mov rcx,qword ptr [rdi+0x48] *);
   fixed [0x48;0x83;0xf9;0x08] (* cmp rcx,0x8 *)]
 | StartLanes=>group [
   fixed [0x45;0x31;0xc0] (* xor r8d,r8d *);
   fixed [0x48;0x85;0xc9] (* test rcx,rcx *)]
 | ReadIndex=>group [
   fixed [0x4e;0x8b;0x4c;0xc7;0x08] (* mov r9,qword ptr [rdi+r8*8+0x8] *);
   fixed [0x49;0x39;0xd1] (* cmp r9,rdx *)]
 | WriteLane=>group [
   fixed [0x46;0x8a;0x14;0x07] (* mov r10b,byte ptr [rdi+r8*1] *);
   fixed [0x41;0x20;0xc2] (* and r10b,al *);
   fixed [0x46;0x88;0x14;0x0e] (* mov byte ptr [rsi+r9*1],r10b *);
   fixed [0xd1;0xe8] (* shr eax,1 *);
   fixed [0x49;0xff;0xc0] (* inc r8 *);
   fixed [0x49;0x39;0xc8] (* cmp r8,rcx *)]
 | Success=>group [
   fixed [0xb8;0x01;0x00;0x00;0x00] (* mov eax,0x1 *)]
 | BadIndex=>group [
   fixed [0x31;0xc0] (* xor eax,eax *)]
 | DecodedCheck=>group [
   fixed [0x55] (* push rbp *);
   fixed [0x48;0x89;0xe5] (* mov rbp,rsp *);
   fixed [0x53] (* push rbx *);
   fixed [0x41;0x54] (* push r12 *);
   fixed [0x41;0x55] (* push r13 *);
   fixed [0x41;0x56] (* push r14 *);
   fixed [0x41;0x57] (* push r15 *);
   fixed [0x48;0x83;0xe4;0xc0] (* and rsp,0xffffffffffffffc0 *);
   fixed [0x48;0x81;0xec;0x00;0x05;0x00;0x00] (* sub rsp,0x500 *);
   fixed [0x48;0x89;0xf3] (* mov rbx,rsi *);
   fixed [0x44;0x0f;0xb6;0xe2] (* movzx r12d,dl *);
   fixed [0x49;0x89;0xcd] (* mov r13,rcx *);
   fixed [0x4d;0x89;0xc6] (* mov r14,r8 *);
   fixed [0x4d;0x89;0xcf] (* mov r15,r9 *);
   fixed [0x48;0x89;0xfe] (* mov rsi,rdi *);
   fixed [0x48;0x89;0xe7] (* mov rdi,rsp *);
   invoke (pc Candidate);
   fixed [0x48;0x89;0xe7] (* mov rdi,rsp *);
   fixed [0x48;0x89;0xde] (* mov rsi,rbx *);
   invoke (pc Torsion);
   fixed [0x44;0x21;0xe0] (* and eax,r12d *);
   fixed [0x4c;0x89;0xef] (* mov rdi,r13 *);
   fixed [0x4c;0x89;0xf6] (* mov rsi,r14 *);
   fixed [0x4c;0x89;0xfa] (* mov rdx,r15 *);
   fixed [0x48;0x8d;0x65;0xd8] (* lea rsp,[rbp-0x28] *);
   fixed [0x41;0x5f] (* pop r15 *);
   fixed [0x41;0x5e] (* pop r14 *);
   fixed [0x41;0x5d] (* pop r13 *);
   fixed [0x41;0x5c] (* pop r12 *);
   fixed [0x5b] (* pop rbx *);
   fixed [0x5d] (* pop rbp *)]
 | Enqueue=>group(map (staging pc) Staging.push_ops)
 | Queued=>group [
   fixed [0xb8;0x01;0x00;0x00;0x00] (* mov eax,0x1 *)]
 | CheckFirst=>group [
   fixed [0x55] (* push rbp *);
   fixed [0x48;0x89;0xe5] (* mov rbp,rsp *);
   fixed [0x53] (* push rbx *);
   fixed [0x41;0x54] (* push r12 *);
   fixed [0x41;0x55] (* push r13 *);
   fixed [0x48;0x83;0xe4;0xc0] (* and rsp,0xffffffffffffffc0 *);
   fixed [0x48;0x81;0xec;0x00;0x0a;0x00;0x00] (* sub rsp,0xa00 *);
   fixed [0x48;0x89;0xfb] (* mov rbx,rdi *);
   fixed [0x41;0x89;0xd4] (* mov r12d,edx *);
   fixed [0x48;0x89;0xe7] (* mov rdi,rsp *);
   invoke (pc DecodeR);
   fixed [0x41;0x89;0xc5] (* mov r13d,eax *);
   fixed [0x48;0x89;0xdf] (* mov rdi,rbx *);
   fixed [0x48;0x89;0xe6] (* mov rsi,rsp *);
   invoke (pc Torsion);
   fixed [0x41;0x20;0xc5] (* and r13b,al *);
   fixed [0x41;0x83;0xfc;0x01] (* cmp r12d,0x1 *)]
 | CheckSecond=>group [
   fixed [0x48;0x8d;0xbb;0x00;0x05;0x00;0x00] (* lea rdi,[rbx+0x500] *);
   fixed [0x48;0x8d;0xb4;0x24;0x00;0x05;0x00;0x00] (* lea rsi,[rsp+0x500] *);
   invoke (pc Torsion);
   fixed [0x0f;0xb6;0xc0] (* movzx eax,al *);
   fixed [0xc1;0xe0;0x08] (* shl eax,0x8 *);
   fixed [0x0d;0xff;0x00;0x00;0x00] (* or eax,0xff *);
   fixed [0x41;0x21;0xc5] (* and r13d,eax *)]
 | ReturnChecked=>group [
   fixed [0x44;0x89;0xe8] (* mov eax,r13d *);
   fixed [0x44;0x89;0xe2] (* mov edx,r12d *);
   fixed [0x48;0x8d;0x65;0xe8] (* lea rsp,[rbp-0x18] *);
   fixed [0x41;0x5d] (* pop r13 *);
   fixed [0x41;0x5c] (* pop r12 *);
   fixed [0x5b] (* pop rbx *);
   fixed [0x5d] (* pop rbp *)]
 | Count=>group [
   fixed [0x48;0x8b;0x87;0x80;0x32;0x00;0x00] (* mov rax,qword ptr [rdi+0x3280] *);
   fixed [0x48;0x85;0xc0] (* test rax,rax *)]
 | Empty=>group [
   fixed [0xb8;0x01;0x00;0x00;0x00] (* mov eax,0x1 *)]
 | Setup=>group [
   fixed [0x53] (* push rbx *);
   fixed [0x41;0x54] (* push r12 *);
   fixed [0x41;0x55] (* push r13 *);
   fixed [0x41;0x56] (* push r14 *);
   fixed [0x41;0x57] (* push r15 *);
   fixed [0x48;0x83;0xec;0x10] (* sub rsp,0x10 *);
   fixed [0x48;0x89;0xfb] (* mov rbx,rdi *);
   fixed [0x49;0x89;0xc4] (* mov r12,rax *);
   fixed [0x49;0x89;0xf6] (* mov r14,rsi *);
   fixed [0x49;0x89;0xd7] (* mov r15,rdx *);
   staging pc (Staging.ClearCount 3);
   fixed [0x31;0xc0] (* xor eax,eax *);
   fixed [0x49;0x83;0xfc;0x02] (* cmp r12,0x2 *)]
 | StartProbe=>group [
   fixed [0x48;0x89;0xdf] (* mov rdi,rbx *);
   fixed [0x48;0x8d;0xb3;0x00;0x28;0x00;0x00] (* lea rsi,[rbx+0x2800] *);
   fixed [0x4c;0x89;0xe2] (* mov rdx,r12 *);
   fixed [0xb9;0x02;0x00;0x00;0x00] (* mov ecx,0x2 *);
   constants (pc Torsion)]
 | Probe=>group [
   probe_y (pc DecodeR) (pc Torsion);
   fixed [0xc5;0xf8;0x93;0xc1] (* kmovw eax,k1 *);
   fixed [0x3c;0xff] (* cmp al,0xff *)]
 | ProbeHit=>group [
   fixed [0xff;0xc9] (* dec ecx *)]
 | AdvanceProbe=>group [
   fixed [0x48;0x81;0xc7;0x00;0x05;0x00;0x00] (* add rdi,0x500 *);
   fixed [0x48;0x81;0xc6;0x00;0x01;0x00;0x00] (* add rsi,0x100 *);
   fixed [0xff;0xca] (* dec edx *)]
 | NoExact=>group [
   fixed [0x31;0xc0] (* xor eax,eax *)]
 | Recompress=>group [
   fixed [0x48;0x89;0xdf] (* mov rdi,rbx *);
   fixed [0x48;0x8d;0xb3;0x00;0x28;0x00;0x00] (* lea rsi,[rbx+0x2800] *);
   fixed [0x4c;0x89;0xe2] (* mov rdx,r12 *);
   invoke (pc Exact)]
 | Resolve=>group [
   fixed [0x48;0x89;0x04;0x24] (* mov qword ptr [rsp],rax *);
   fixed [0x45;0x31;0xed] (* xor r13d,r13d *)]
 | Chunk=>group [
   fixed [0x42;0x80;0x3c;0x2c;0xff] (* cmp byte ptr [rsp+r13*1],0xff *)]
 | ChooseOne=>group [
   fixed [0xba;0x01;0x00;0x00;0x00] (* mov edx,0x1 *);
   fixed [0x49;0x8d;0x4d;0x01] (* lea rcx,[r13+0x1] *);
   fixed [0x4c;0x39;0xe1] (* cmp rcx,r12 *)]
 | Adjacent=>group [
   fixed [0x80;0x3c;0x0c;0xff] (* cmp byte ptr [rsp+rcx*1],0xff *)]
 | ChoosePair=>group [
   fixed [0xff;0xc2] (* inc edx *)]
 | Check=>group [
   fixed [0x49;0x69;0xfd;0x00;0x05;0x00;0x00] (* imul rdi,r13,0x500 *);
   fixed [0x48;0x01;0xdf] (* add rdi,rbx *);
   fixed [0x4c;0x89;0xee] (* mov rsi,r13 *);
   fixed [0x48;0xc1;0xe6;0x08] (* shl rsi,0x8 *);
   fixed [0x48;0x8d;0xb4;0x33;0x00;0x28;0x00;0x00] (* lea rsi,[rbx+rsi*1+0x2800] *);
   invoke (pc CheckR);
   fixed [0x83;0xfa;0x02] (* cmp edx,0x2 *)]
 | SaveOne=>group [
   fixed [0x42;0x88;0x04;0x2c] (* mov byte ptr [rsp+r13*1],al *)]
 | SavePair=>group [
   fixed [0x66;0x42;0x89;0x04;0x2c] (* mov word ptr [rsp+r13*1],ax *);
   fixed [0x49;0xff;0xc5] (* inc r13 *)]
 | Next=>group [
   fixed [0x49;0xff;0xc5] (* inc r13 *);
   fixed [0x4d;0x39;0xe5] (* cmp r13,r12 *)]
 | StartScore=>group [
   fixed [0x48;0x8d;0x9b;0x00;0x30;0x00;0x00] (* lea rbx,[rbx+0x3000] *);
   fixed [0x45;0x31;0xed] (* xor r13d,r13d *)]
 | Score=>group [
   fixed [0x42;0x0f;0xb6;0x04;0x2c] (* movzx eax,byte ptr [rsp+r13*1] *);
   fixed [0x48;0x89;0xdf] (* mov rdi,rbx *);
   fixed [0x4c;0x89;0xf6] (* mov rsi,r14 *);
   fixed [0x4c;0x89;0xfa] (* mov rdx,r15 *);
   invoke (pc Scatter);
   fixed [0x85;0xc0] (* test eax,eax *)]
 | NextScore=>group [
   fixed [0x48;0x83;0xc3;0x50] (* add rbx,0x50 *);
   fixed [0x49;0xff;0xc5] (* inc r13 *);
   fixed [0x4d;0x39;0xe5] (* cmp r13,r12 *)]
 | Restore=>group [
   fixed [0x48;0x83;0xc4;0x10] (* add rsp,0x10 *);
   fixed [0x41;0x5f] (* pop r15 *);
   fixed [0x41;0x5e] (* pop r14 *);
   fixed [0x41;0x5d] (* pop r13 *);
   fixed [0x41;0x5c] (* pop r12 *);
   fixed [0x5b] (* pop rbx *)]
 end.

Definition branch_bytes (addr:target->Z) e : fragment := match e with
 | Fall=>fixed [] | Ret=>fixed [0xc3] | Jump cc s t=>tail cc s (addr t) end.
Definition block_bytes pc addr l := group [body pc l;branch_bytes addr (exit_of l)].
Fixpoint offset pc l blocks := match blocks with []=>0 | h::t=>
 if label_beq h l then 0 else Z.of_nat(length(block_bytes pc (fun _=>0) h 0))+offset pc l t end.
Definition target_pc pc s t := match t with Entry r=>pc r | Local l=>pc s+offset pc l (order s) end.
Definition image pc s := group(map (block_bytes pc (target_pc pc s)) (order s)) (pc s).
Definition fits pc s l := match exit_of l with Jump _ short_form t=>
 let endpc:=target_pc pc s (Local l)+Z.of_nat(length(block_bytes pc (target_pc pc s) l 0)) in
 let d:=target_pc pc s t-endpc in let bound:=if short_form then 128 else 2^31 in
 (-bound<=?d)&&(d<?bound) | _=>true end.
Fixpoint following l blocks := match blocks with []=>None | h::t=>
 if label_beq h l then hd_error t else following l t end.
Definition successor s l equal below := let fall:=following l (order s) in
 match exit_of l with Ret=>None | Fall=>fall | Jump cc _ target=>
 let taken:=match cc with Eq=>equal | Ne=>negb equal | Below=>below
 | AtLeast=>negb below | Above=>negb(equal||below) | Always=>true end in
 if taken then match target with Local dst=>Some dst | Entry _=>None end else fall end.
