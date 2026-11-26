From Coq Require Import List ZArith Znumtheory Lia.
From Machine Require Import isa.X86 execution.LinkedCalls execution.LinkedRun abi.RegisterSpill memory.MemoryGeometry memory.FlatMemory.
Import ListNotations. Local Open Scope Z_scope.

Definition saves := [3;12;13;14;15]%nat.
Definition allocation := 960.
Definition saved_size := 8*Z.of_nat(S(length saves)).
Definition prologue := [0x55;0x48;0x89;0xe5] ++ flat_map (reg_byte 0x50) saves ++
 [0x48;0x83;0xe4;0xc0;0x48;0x81;0xec] ++ le32 allocation.
Definition epilogue :=
 [0x48;0x8d;0x65;(-8*Z.of_nat(length saves)) mod 256] ++
 flat_map (reg_byte 0x58) (rev saves) ++ [0x5d;0xc5;0xf8;0x77].
Definition align64 sp := sp-sp mod 64.
Definition staging sp := align64(sp-saved_size)-allocation.
(* RSP immediately before CALL is 64-aligned. The cached-add frame saves
   RBP, aligns RSP down, uses 1280 scratch bytes and two nested return slots. *)
Definition lowest sp := align64(staging sp-8-8)-1280-16.
Definition stack_depth := 2424.
Lemma aligned z : align64 z mod 64=0.
Proof. unfold align64;rewrite Zminus_mod,Z.mod_mod,Z.sub_diag by lia;reflexivity. Qed.
Lemma frame_geometry sp : sp mod 16=8 ->
 staging sp mod 64=0 /\ sp-stack_depth<=lowest sp /\
 lowest sp=staging sp-1360 /\ staging sp+960<=sp-48.
Proof.
 intro ABI;set(t:=staging sp).
 assert(A:t mod 64=0) by (unfold t,staging,allocation;rewrite Zminus_mod,aligned;reflexivity).
 assert(F:(t-8-8) mod 64=48) by (replace (t-8-8) with (t+(-16)) by ring;
   rewrite Zplus_mod,A;reflexivity).
 assert(P:(sp-48) mod 64<=56).
 { pose proof(Z.mod_pos_bound (sp-48) 64 ltac:(lia)).
   assert (((sp-48) mod 64) mod 16=8).
   { rewrite <-(Zmod_div_mod 16 64 (sp-48)) by (try lia;exists 4;reflexivity).
     rewrite Zminus_mod,ABI;reflexivity. }
   pose proof(Z.div_mod ((sp-48) mod 64) 16 ltac:(lia));lia. }
 unfold lowest;fold t;unfold align64;rewrite !F.
 unfold t,staging,align64,stack_depth,allocation;change saved_size with 48.
 pose proof(Z.mod_pos_bound (sp-48) 64 ltac:(lia));split;[exact A|];repeat split;lia.
Qed.

Definition placement images count sp pt dst :=
 sp mod 16=8 /\ pt mod 64=0 /\ dst mod 8=0 /\
 fits64 (sp-stack_depth) (stack_depth+8) /\ fits64 pt 1280 /\ fits64 dst (2720*Z.of_nat count) /\
 let regions:=[(sp-stack_depth,stack_depth+8);(pt,1280);(dst,2720*Z.of_nat count)] in
 disjoint pt 1280 dst (2720*Z.of_nat count) /\
 disjoint (sp-stack_depth) (stack_depth+8) pt 1280 /\
 disjoint (sp-stack_depth) (stack_depth+8) dst (2720*Z.of_nat count) /\
 forall r c,In r regions -> In c images -> disjoint (fst r) (snd r) (fst c) (snd c-fst c).

Definition saved_regs:=5%nat::saves.
Definition keep sp pt dst x:=
 ~(staging sp-1360<=x<staging sp-1360+2320) /\
 ~(pt<=x<pt+1280) /\ ~(dst<=x<dst+21760).
Definition saved sp p:=spill (regs(machine p)) (mem(machine p)) sp saved_regs.
