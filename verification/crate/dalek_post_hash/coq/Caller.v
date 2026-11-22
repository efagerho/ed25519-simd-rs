From Coq Require Import List ZArith Bool.
From Machine Require Import isa.X86 isa.Instructions execution.MaskTrace.
From Ed25519Simd.Decode Require Import Image Glue.
From Ed25519Simd.Dalek Require Import FieldOps.
From Ed25519Simd.PostHash Require Staging.
From Ed25519Simd.Zip215 Require Caller.
Import ListNotations. Local Open Scope Z_scope.

Inductive symbol := Candidate | Push | Flush | Decoded | Filter | Scatter | Digest | Ladder | Small | Exact | Decoder | Helper.
Inductive label := CandidateCall
 | FirstWord | StartScreen | ReadLow | LowUpper | LowNext | HighLow | HighUpper | NextEncoding | Screened | Enqueue | Queued
 | Count | Recompress | SaveMask | Score | Advance | Restore | Empty
 | Eligible | Canonical | Weak | MatchY | MatchX | Reject | Done
 | FirstDifference | SecondDifference | KeysDone.
Scheme Equality for label.
Definition order s := match s with
 | Candidate=>[CandidateCall]
 | Push=>[FirstWord;StartScreen;ReadLow;LowUpper;LowNext;HighLow;HighUpper;NextEncoding;Screened;Enqueue;Queued]
 | Flush=>[Count;Recompress;SaveMask;Score;Advance;Restore;Empty]
 | Decoded=>[Eligible;Canonical;Weak;MatchY;MatchX;Reject;Done]
 | Filter=>[FirstDifference;SecondDifference;KeysDone]
 | _=>[] end.

Inductive target := Local (l:label) | External (s:symbol).
Inductive exit := Fall | Ret | Jump (cc:Caller.condition)(is_short:bool)(to:target).
Definition staging pc := Staging.instr (fun c=>match c with Staging.Reduce=>pc Digest
 | Staging.MultiplyPoint=>pc Ladder | Staging.MakeCandidate=>pc Candidate end).
Inductive axis := AxisX | AxisY.
Definition coord_row a := match a with AxisX=>0%nat | AxisY=>5%nat end.
Definition match_coordinate pc a := let row:=64*Z.of_nat(coord_row a) in group [field_mem false 3 row;
 fixed(field_rows false 5 7 640); group(map (fun i=>let '(dst,bias):=seed_operands i in
 fixed(rm_memory 1 1 0xfb dst bias 7 (row+64*Z.of_nat i))) (seq 0 5));
 invoke(pc Helper+0xbae);invoke(pc Decoder+0xa7e);ones;Glue.test 1 (pc Decoder+0xb88)].

(* VSIB index ZMM20 holds the eight absolute table addresses. K3 is
   replenished before each gather, which clears completed mask bits. *)
Definition gather dst offset := group [fixed [0xc5;0xe4;0x46;0xdb];
 fixed([0x62;0xf2-0x80*((Z.of_nat dst/8)mod 2)-0x10*(Z.of_nat dst/16);
        0xfd;0x43;0x91;8*(Z.of_nat dst mod 8)+4;0x25]++le32 offset)].
Definition table_disp field i := 16*160 + 40*field + 8*Z.of_nat i.
Definition key_column (second:bool) i :=
 let saved:=(15+i)%nat in let bias:=if Nat.eqb i 0 then 30%nat else 31%nat in
 if second then group [gather 10%nat (table_disp 3 i);alu i (Add saved saved);
   alu i (Add i bias);alu i (Sub i 10)]
 else group [gather saved (table_disp 0 i);gather i (table_disp 1 i);
   alu i (Add i bias);alu i (Sub i saved)].
Definition key_zero pc second := group [group(map (key_column second)(seq 0 5));
 invoke(pc Decoder+0xa7e);ones;Glue.test 1 (pc Decoder+0xb88)].

Definition body (pc:symbol->Z) l : fragment := match l with
 | CandidateCall=>group (map (staging pc) (Staging.candidate_ops false))
 | FirstWord=>group [
   fixed [0x8b;0x02] (* mov    eax,DWORD PTR [rdx] *);
   fixed [0x83;0xc0;0x14] (* add    eax,0x14 *);
   fixed [0x83;0xf8;0x15] (* cmp    eax,0x15 *)]
 | StartScreen=>group [
   fixed [0x49;0x89;0xd2] (* mov    r10,rdx *);
   fixed [0x4c;0x8d;0x9a;0x00;0x01;0x00;0x00] (* lea    r11,[rdx+0x100] *)]
 | ReadLow=>group [
   fixed [0x49;0x8b;0x42;0x18] (* mov    rax,QWORD PTR [r10+0x18] *);
   fixed [0x49;0x83;0x3a;0x01] (* cmp    QWORD PTR [r10],0x1 *)]
 | LowUpper=>group [
   fixed [0x48;0xd1;0xe0] (* shl    rax,1 *);
   fixed [0x49;0x0b;0x42;0x10] (* or     rax,QWORD PTR [r10+0x10] *);
   fixed [0x49;0x0b;0x42;0x08] (* or     rax,QWORD PTR [r10+0x8] *)]
 | LowNext=>fixed []
 | HighLow=>group [
   fixed [0x49;0x83;0x3a;0xec] (* cmp    QWORD PTR [r10],0xffffffffffffffec *)]
 | HighUpper=>group [
   fixed [0x48;0x0f;0xba;0xe8;0x3f] (* bts    rax,0x3f *);
   fixed [0x49;0x23;0x42;0x10] (* and    rax,QWORD PTR [r10+0x10] *);
   fixed [0x49;0x23;0x42;0x08] (* and    rax,QWORD PTR [r10+0x8] *);
   fixed [0x48;0x83;0xf8;0xff] (* cmp    rax,0xffffffffffffffff *)]
 | NextEncoding=>group [
   fixed [0x49;0x83;0xc2;0x20] (* add    r10,0x20 *);
   fixed [0x4d;0x39;0xda] (* cmp    r10,r11 *)]
 | Screened=>group [
   fixed [0x31;0xc0] (* xor    eax,eax *);
   fixed [0x48;0x89;0xcf] (* mov    rdi,rcx *);
   fixed [0x4c;0x89;0xc6] (* mov    rsi,r8 *);
   fixed [0x4c;0x89;0xca] (* mov    rdx,r9 *)]
 | Enqueue=>group (map (staging pc) Staging.push_ops)
 | Queued=>group [
   fixed [0xb8;0x01;0x00;0x00;0x00] (* mov    eax,0x1 *)]
 | Count=>group [
   fixed [0x48;0x8b;0x87;0x80;0x32;0x00;0x00] (* mov    rax,QWORD PTR [rdi+0x3280] *);
   fixed [0x48;0x85;0xc0] (* test   rax,rax *)]
 | Recompress=>group [
   fixed [0x53] (* push   rbx *);
   fixed [0x41;0x54] (* push   r12 *);
   fixed [0x41;0x55] (* push   r13 *);
   fixed [0x41;0x56] (* push   r14 *);
   fixed [0x41;0x57] (* push   r15 *);
   fixed [0x48;0x8d;0x9f;0x00;0x30;0x00;0x00] (* lea    rbx,[rdi+0x3000] *);
   fixed [0x49;0x89;0xf4] (* mov    r12,rsi *);
   fixed [0x49;0x89;0xd5] (* mov    r13,rdx *);
   fixed [0x49;0x89;0xc7] (* mov    r15,rax *);
   staging pc (Staging.ClearCount 7);
   fixed [0x48;0x8d;0xb7;0x00;0x28;0x00;0x00] (* lea    rsi,[rdi+0x2800] *);
   fixed [0x4c;0x89;0xfa] (* mov    rdx,r15 *);
   invoke (pc Exact)]
 | SaveMask=>group [
   fixed [0x49;0x89;0xc6] (* mov    r14,rax *)]
 | Score=>group [
   fixed [0x41;0x0f;0xb6;0xc6] (* movzx  eax,r14b *);
   fixed [0x48;0x89;0xdf] (* mov    rdi,rbx *);
   fixed [0x4c;0x89;0xe6] (* mov    rsi,r12 *);
   fixed [0x4c;0x89;0xea] (* mov    rdx,r13 *);
   invoke (pc Scatter);
   fixed [0x85;0xc0] (* test   eax,eax *)]
 | Advance=>group [
   fixed [0x49;0xc1;0xee;0x08] (* shr    r14,0x8 *);
   fixed [0x48;0x83;0xc3;0x50] (* add    rbx,0x50 *);
   fixed [0x49;0xff;0xcf] (* dec    r15 *)]
 | Restore=>group [
   fixed [0x41;0x5f] (* pop    r15 *);
   fixed [0x41;0x5e] (* pop    r14 *);
   fixed [0x41;0x5d] (* pop    r13 *);
   fixed [0x41;0x5c] (* pop    r12 *);
   fixed [0x5b] (* pop    rbx *)]
 | Empty=>group [
   fixed [0xb8;0x01;0x00;0x00;0x00] (* mov    eax,0x1 *)]
 | Eligible=>group [
   fixed [0x55] (* push   rbp *);
   fixed [0x48;0x89;0xe5] (* mov    rbp,rsp *);
   fixed [0x53] (* push   rbx *);
   fixed [0x41;0x54] (* push   r12 *);
   fixed [0x41;0x55] (* push   r13 *);
   fixed [0x41;0x56] (* push   r14 *);
   fixed [0x41;0x57] (* push   r15 *);
   fixed [0x48;0x83;0xe4;0xc0] (* and    rsp,0xffffffffffffffc0 *);
   fixed [0x48;0x81;0xec;0x00;0x05;0x00;0x00] (* sub    rsp,0x500 *);
   fixed [0x48;0x89;0xf3] (* mov    rbx,rsi *);
   fixed [0x48;0x89;0x3c;0x24] (* mov    QWORD PTR [rsp],rdi *);
   fixed [0x44;0x0f;0xb6;0xe2] (* movzx  r12d,dl *);
   fixed [0x49;0x89;0xcd] (* mov    r13,rcx *);
   fixed [0x4d;0x89;0xc6] (* mov    r14,r8 *);
   fixed [0x4d;0x89;0xcf] (* mov    r15,r9 *);
   fixed [0xc5;0xfa;0x7e;0x01] (* vmovq  xmm0,QWORD PTR [rcx] *);
   fixed [0x62;0xf2;0x7d;0x48;0x26;0xc8] (* vptestmb k1,zmm0,zmm0 *);
   fixed [0xc5;0xf8;0x93;0xc1] (* kmovw  eax,k1 *);
   fixed [0x41;0x21;0xc4] (* and    r12d,eax *)]
 | Canonical=>group [
   field_mem false 3 320;
   broadcast 29 (pc Helper+0xde8);
   ones;
   (fun ip=>mask_bytes 1 (rip_bcst 3 1 0x1e 2 0 (pc Decoder+0xb88-ip-11))++[5]);
   fixed [0xc5;0xf8;0x93;0xc2] (* kmovw  eax,k2 *);
   fixed [0xf7;0xd0] (* not    eax *);
   fixed [0x41;0x21;0xc4] (* and    r12d,eax *)]
 | Weak=>group [
   fixed [0x48;0x89;0xdf] (* mov    rdi,rbx *);
   invoke (pc Small);
   fixed [0xf7;0xd0] (* not    eax *);
   fixed [0x41;0x21;0xc4] (* and    r12d,eax *)]
 | MatchY=>group [
   fixed [0x48;0x8b;0x34;0x24] (* mov    rsi,QWORD PTR [rsp] *);
   fixed [0x48;0x89;0xe7] (* mov    rdi,rsp *);
   invoke (pc Candidate);
   fixed [0x48;0x89;0xe7] (* mov    rdi,rsp *);
   constants (pc Helper);
   match_coordinate pc AxisY;
   fixed [0xc5;0xf8;0x93;0xc1] (* kmovw  eax,k1 *);
   fixed [0x41;0x21;0xc4] (* and    r12d,eax *)]
 | MatchX=>group [
   match_coordinate pc AxisX;
   fixed [0xc5;0xf8;0x93;0xc1] (* kmovw  eax,k1 *);
   fixed [0x44;0x21;0xe0] (* and    eax,r12d *)]
 | Reject=>group [
   fixed [0x31;0xc0] (* xor    eax,eax *)]
 | Done=>group [
   fixed [0x4c;0x89;0xef] (* mov    rdi,r13 *);
   fixed [0x4c;0x89;0xf6] (* mov    rsi,r14 *);
   fixed [0x4c;0x89;0xfa] (* mov    rdx,r15 *);
   fixed [0x48;0x8d;0x65;0xd8] (* lea    rsp,[rbp-0x28] *);
   fixed [0x41;0x5f] (* pop    r15 *);
   fixed [0x41;0x5e] (* pop    r14 *);
   fixed [0x41;0x5d] (* pop    r13 *);
   fixed [0x41;0x5c] (* pop    r12 *);
   fixed [0x5b] (* pop    rbx *);
   fixed [0x5d] (* pop    rbp *)]
 | FirstDifference=>group [
   fixed [0x48;0x83;0xec;0x08] (* sub    rsp,0x8 *);
   fixed [0x62;0xe1;0xfe;0x48;0x6f;0x27] (* vmovdqu64 zmm20,ZMMWORD PTR [rdi] *);
   constants (pc Helper);
   key_zero pc false;
   fixed [0xc5;0xf8;0x98;0xc9] (* kortestw k1,k1 *)]
 | SecondDifference=>group [
   fixed [0xc5;0xf8;0x93;0xc9] (* kmovw  ecx,k1 *);
   key_zero pc true;
   fixed [0xc5;0xf8;0x92;0xd1] (* kmovw  k2,ecx *);
   fixed [0xc5;0xf4;0x41;0xca] (* kandw  k1,k1,k2 *);
   fixed [0x62;0xf2;0x7e;0x48;0x28;0xc1] (* vpmovm2b zmm0,k1 *);
   fixed [0xc5;0xfa;0x7e;0x0e] (* vmovq  xmm1,QWORD PTR [rsi] *);
   fixed [0xc5;0xf9;0xdf;0xc1] (* vpandn xmm0,xmm0,xmm1 *);
   fixed [0xc5;0xf9;0xd6;0x06] (* vmovq  QWORD PTR [rsi],xmm0 *)]
 | KeysDone=>group [
   fixed [0x48;0x83;0xc4;0x08] (* add    rsp,0x8 *);
   fixed [0xc5;0xf8;0x77] (* vzeroupper *)] end.
Definition exit_of l := match l with
 | CandidateCall=>Ret
 | FirstWord=>Jump Caller.Above true (Local Enqueue)
 | StartScreen=>Fall
 | ReadLow=>Jump Caller.Above true (Local HighLow)
 | LowUpper=>Jump Caller.Ne true (Local Enqueue)
 | LowNext=>Jump Caller.Always true (Local NextEncoding)
 | HighLow=>Jump Caller.Below true (Local Enqueue)
 | HighUpper=>Jump Caller.Ne true (Local Enqueue)
 | NextEncoding=>Jump Caller.Ne true (Local ReadLow)
 | Screened=>Jump Caller.Always false (External Scatter)
 | Enqueue=>Jump Caller.Eq false (External Flush)
 | Queued=>Ret
 | Count=>Jump Caller.Eq true (Local Empty)
 | Recompress=>Fall
 | SaveMask=>Fall
 | Score=>Jump Caller.Eq true (Local Restore)
 | Advance=>Jump Caller.Ne true (Local Score)
 | Restore=>Ret
 | Empty=>Ret
 | Eligible=>Jump Caller.Eq false (Local Reject)
 | Canonical=>Jump Caller.Eq false (Local Reject)
 | Weak=>Jump Caller.Eq false (Local Reject)
 | MatchY=>Jump Caller.Eq false (Local Reject)
 | MatchX=>Jump Caller.Always true (Local Done)
 | Reject=>Fall
 | Done=>Jump Caller.Always false (External Scatter)
 | FirstDifference=>Jump Caller.Eq false (Local KeysDone)
 | SecondDifference=>Fall
 | KeysDone=>Ret end.

Definition expand pc addr l := group [body pc l;match exit_of l with
 | Fall=>fixed [] | Ret=>fixed [0xc3] | Jump cc small to=>Caller.tail cc small (addr to) end].
Fixpoint offset l blocks := match blocks with []=>0 | h::t=>
 if label_beq h l then 0 else Z.of_nat(length(expand (fun _=>0) (fun _=>0) h 0))+offset l t end.
Definition target_pc pc s t := match t with External r=>pc r | Local l=>pc s+offset l (order s) end.
Definition image pc s := group(map (expand pc (target_pc pc s)) (order s)) (pc s).
Definition fits pc s l := match exit_of l with Jump _ short to=>
 let a:=target_pc pc s (Local l) in let delta:=target_pc pc s to-a-Z.of_nat(length(expand pc (target_pc pc s) l a)) in
 let b:=if short then 128 else 2^31 in (-b<=?delta)&&(delta<?b) | _=>true end.
Fixpoint following l blocks := match blocks with []=>None | a::rest=>
 if label_beq a l then option_map Local (hd_error rest) else following l rest end.
Definition next s l equal below := let fall:=following l (order s) in match exit_of l with
 | Ret=>None | Fall=>fall | Jump cc _ to=>if match cc with Caller.Eq=>equal | Caller.Ne=>negb equal
 | Caller.Below=>below | Caller.Above=>negb(equal||below) | Caller.AtLeast=>negb below | Caller.Always=>true end
 then Some to else fall end.
Definition reaches s l eq below dst := match next s l eq below with
 | Some(Local target)=>label_beq target dst | _=>false end.
