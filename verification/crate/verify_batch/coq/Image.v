From Coq Require Import List ZArith Bool.
From Machine Require Import isa.X86 isa.ProgramLayout execution.LinkedCalls.
From Ed25519Simd.VerifyBatch Require Import Routing Arguments.
Import ListNotations. Local Open Scope Z_scope.

Inductive block := Entry | Prologue | Choose | Full | Stage | PrepareArgs | CallPrepare | Prepared | HashArgs | CallHash | ScoreArgs | CallScore | AfterScore | RejectArgs | CallScatter | Continue | More | Epilogue | Empty | Tail | Pad | TailDone.
Scheme Equality for block.
Inductive target := Prepare | Hash | Score | Scatter.
Inductive condition := Equal | Below | Unequal | Always.
Inductive terminator := Next | Jump (c:condition) (short:bool) (dest:block)
 | Call (callee:target) | Ret.
Definition order := [Entry;Prologue;Choose;Full;Stage;PrepareArgs;CallPrepare;Prepared;HashArgs;CallHash;ScoreArgs;CallScore;AfterScore;RejectArgs;CallScatter;Continue;More;Epilogue;Empty;Tail;Pad;TailDone].
Definition ending b := match b with
 | Entry=>Jump Equal false Empty
 | Prologue=>Next
 | Choose=>Jump Below false Tail
 | Full=>Next
 | Stage=>Next
 | PrepareArgs=>Next
 | CallPrepare=>Call Prepare
 | Prepared=>Jump Equal false RejectArgs
 | HashArgs=>Next
 | CallHash=>Call Hash
 | ScoreArgs=>Next
 | CallScore=>Call Score
 | AfterScore=>Jump Always true Continue
 | RejectArgs=>Next
 | CallScatter=>Call Scatter
 | Continue=>Jump Equal true Epilogue
 | More=>Jump Unequal false Choose
 | Epilogue=>Ret
 | Empty=>Ret
 | Tail=>Next
 | Pad=>Jump Unequal true Pad
 | TailDone=>Jump Always false Stage end.

Definition saved := [3;12;13;14;15]%nat.
Definition saves := flat_map (fun r=>encoding 0 (Save r)) saved.
Definition restores := flat_map (fun r=>encoding 0 (Restore r)) (rev saved).
Definition index_copy i :=
 let source:=40*Z.of_nat i+32 in
 (if source <? 128 then [0x48;0x8b;0x43;source] else [0x48;0x8b;0x83]++le32 source) ++
 [0x48;0x89;0x84;0x24]++le32 (864+8*Z.of_nat i).

Definition body b : list Z := match b with
 | Entry=> [0x48;0x85;0xf6] (* test rsi,rsi *)
 | Prologue=> saves ++
     [0x48;0x81;0xec;0xc0;0x03;0x00;0x00] (* sub rsp,0x3c0 *) ++
     Arguments.encoded setup
 | Choose=> [0x49;0x83;0xfc;0x08] (* cmp r12,0x8 *)
 | Full=> [0x48;0xc7;0x84;0x24;0xa0;0x03;0x00;0x00;0x08;0x00;0x00;0x00] (* mov QWORD PTR [rsp+0x3a0],0x8 *) ++
     [0x49;0x83;0xec;0x08] (* sub r12,0x8 *)
 | Stage=> route_bytes ++
     flat_map index_copy (seq 0 8) ++
     [0x48;0x81;0xc3;0x40;0x01;0x00;0x00] (* add rbx,0x140 *)
 | PrepareArgs=> Arguments.encoded Arguments.prepare
 | CallPrepare=> []
 | Prepared=> [0x85;0xc0] (* test eax,eax *)
 | HashArgs=> [0x62;0xf2;0x7d;0x48;0x32;0x44;0x24;0x68] (* vpmovzxbq zmm0,QWORD PTR [rsp+0x340] *) ++
     [0x62;0xf2;0xfd;0x48;0x27;0xc8] (* vptestmq k1,zmm0,zmm0 *) ++
     [0x62;0xf1;0xfe;0xc9;0x6f;0x44;0x24;0x0b] (* vmovdqu64 zmm0{k1}{z},ZMMWORD PTR [rsp+0x2c0] *) ++
     [0x62;0xf1;0xfe;0x48;0x7f;0x44;0x24;0x0b] (* vmovdqu64 ZMMWORD PTR [rsp+0x2c0],zmm0 *) ++
     Arguments.encoded Arguments.hash
 | CallHash=> []
 | ScoreArgs=> Arguments.encoded Arguments.score
 | CallScore=> []
 | AfterScore=> []
 | RejectArgs=> Arguments.encoded Arguments.reject
 | CallScatter=> []
 | Continue=> [0x85;0xc0] (* test eax,eax *)
 | More=> [0x4d;0x85;0xe4] (* test r12,r12 *)
 | Epilogue=> [0x48;0x81;0xc4;0xc0;0x03;0x00;0x00] (* add rsp,0x3c0 *) ++
     restores
 | Empty=> [0xb8;0x01;0x00;0x00;0x00] (* mov eax,0x1 *)
 | Tail=> [0x4c;0x89;0xa4;0x24;0xa0;0x03;0x00;0x00] (* mov QWORD PTR [rsp+0x3a0],r12 *) ++
     [0x48;0x89;0xde] (* mov rsi,rbx *) ++
     [0x4b;0x8d;0x04;0xa4] (* lea rax,[r12+r12*4] *) ++
     [0x48;0x8d;0x7c;0xc3;0xd8] (* lea rdi,[rbx+rax*8-0x28] *) ++
     [0x48;0x8d;0x1c;0x24] (* lea rbx,[rsp] *) ++
     [0x45;0x31;0xe4] (* xor r12d,r12d *) ++
     [0x31;0xc9] (* xor ecx,ecx *)
 | Pad=> [0xc5;0xfe;0x6f;0x06] (* vmovdqu ymm0,YMMWORD PTR [rsi] *) ++
     [0x48;0x8b;0x46;0x20] (* mov rax,QWORD PTR [rsi+0x20] *) ++
     [0xc5;0xfe;0x7f;0x04;0x0b] (* vmovdqu YMMWORD PTR [rbx+rcx*1],ymm0 *) ++
     [0x48;0x89;0x44;0x0b;0x20] (* mov QWORD PTR [rbx+rcx*1+0x20],rax *) ++
     [0x48;0x8d;0x46;0x28] (* lea rax,[rsi+0x28] *) ++
     [0x48;0x39;0xfe] (* cmp rsi,rdi *) ++
     [0x48;0x0f;0x42;0xf0] (* cmovb rsi,rax *) ++
     [0x83;0xc1;0x28] (* add ecx,0x28 *) ++
     [0x81;0xf9;0x40;0x01;0x00;0x00] (* cmp ecx,0x140 *)
 | TailDone=> [] end.

Definition opcode c short : list Z := match c,short with
 | Always,true=>[0xeb] | Always,false=>[0xe9]
 | Equal,true=>[0x74] | Equal,false=>[0x0f;0x84]
 | Below,true=>[0x72] | Below,false=>[0x0f;0x82]
 | Unequal,true=>[0x75] | Unequal,false=>[0x0f;0x85] end.
Definition width e := match e with Next=>0 | Ret=>1 | Call _=>5
 | Jump c s _=>Z.of_nat (length (opcode c s)) + if s then 1 else 4 end.
Definition size b := Z.of_nat (length (body b))+width (ending b).
Fixpoint offset_in b bs := match bs with []=>0 | h::t=>
 if block_beq b h then 0 else size h+offset_in b t end.
Definition offset b := offset_in b order.
Definition next b := offset b+size b.
Definition displacement pc address b := match ending b with
 | Jump _ _ d=>offset d-next b | Call t=>address t-(pc+next b) | _=>0 end.
Definition fits pc address b := match ending b with
 | Jump _ short _=>signed (if short then 8 else 32) (displacement pc address b)
 | Call _=>signed 32 (displacement pc address b) | _=>true end.
Definition ending_bytes pc address b := let d:=displacement pc address b in
 match ending b with Next=>[] | Ret=>[0xc3] | Call _=>[0xe8]++le32 d
 | Jump c short _=>opcode c short ++ if short then [d mod 256] else le32 d end.
Definition image pc address := flat_map (fun b=>body b++ending_bytes pc address b) order.
Definition matches pc address bs := image pc address=bs /\ forallb (fits pc address) order=true.
