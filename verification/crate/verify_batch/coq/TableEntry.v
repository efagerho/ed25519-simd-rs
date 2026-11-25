From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.PrepareChunk Require CommonBytes.
From Ed25519Simd.KeyTable Require ObjectBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require EligibleLanes.
Import ListNotations. Local Open Scope Z_scope.

Definition origin:=KeyTable.ObjectBytes.address.
Definition site:=PrepareNative.common.
Definition point e:=scratch e+1024.
Definition tables e:=scratch e+3584.
Definition frame pol e:=common_top pol e-112.
Definition code:list line:=[(161,7%nat,LeaG 7 (Address 3 None 1024));(168,7%nat,LeaG 6 (Address 3 None 3584));
 (175,5%nat,Imm32 2 8);(180,5%nat,CallRelative (origin-(site+185)))].
Lemma linked_code : linked CommonBytes.symbol_bytes code.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma image pol:In (origin,KeyTable.ObjectBytes.symbol_bytes) (children pol).
Proof. apply in_or_app;left;do 8 right;left;reflexivity. Qed.

Definition enter bias:=segment (bias+site) CommonBytes.symbol_bytes 4.
Record entry pol bias e p q:Prop:=Entry {
 address:ip q=bias+origin;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 arguments:regs(machine q) 4%nat=frame pol e /\ regs(machine q) 7%nat=point e /\
   regs(machine q) 6%nat=tables e /\ regs(machine q) 2%nat=8;
 link:read_word (mem(machine q)) (frame pol e)=bias+site+185;
 caller_regs:forall r,r<>4%nat -> r<>7%nat -> r<>6%nat -> r<>2%nat -> regs(machine q) r=regs(machine p) r;
 memory_after:mem(machine q)=store_word (mem(machine p)) (frame pol e) (bias+site+185);
 call_log:log q=log p++[qword (word(bias+site+180)) (frame pol e) (bias+site+185)]
}.

Theorem checked pol bias e before p : placement e -> loaded pol bias (mem e) (writable e) ->
 EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q,enter bias p=Some q /\ entry pol bias e p q.
Proof.
 intros P I E Live;pose proof(EligibleLanes.destination _ _ _ _ _ E) as PC;unfold EligibleLanes.next in PC;
 rewrite (proj2(Z.eqb_neq _ _) Live) in PC.
 set (o:=bias+site) in *;set (s:=machine p).
 pose proof(EligibleLanes.scratch_base _ _ _ _ _ E) as BX;pose proof(EligibleLanes.stack _ _ _ _ _ E) as SP;fold s in BX,SP.
 assert (Slot:word(regs s 4%nat-8)=frame pol e).
 { rewrite SP;unfold frame;replace (common_top pol e-104-8) with (common_top pol e-112) by ring;apply word_fits;
   destruct(stack_ok _ P) as [[Lo Hi] _];unfold common_top,Rows.frame,sp,word64 in *;destruct pol;lia. }
 assert (Dest:word64(bias+origin)) by exact (mapped_word _ _ _ I _ _ (image pol) ltac:(vm_compute;reflexivity)).
 assert (Ret:word64(o+185)) by (destruct(proj1(symbols _ _ _ _ I _ _ (in_common pol))) as [L H];
   change (Z.of_nat(length CommonBytes.symbol_bytes)) with 290 in H;unfold o,site,word64;lia).
 set (args:=set (set (set s 7 (point e)) 6 (tables e)) 2 8).
 set (callee:=push args (o+185));set (w:=qword (word(o+180)) (frame pol e) (o+185)).
 assert (Run:run 4 (ScalarBytes.fetch o CommonBytes.symbol_bytes) (State (Running 161) s (LinkedRun.carry p))=
     Some(State (Running(origin-site)) callee (LinkedRun.carry p),[w])).
 { apply (InstructionRoute.checked _ _ _ linked_code);cbn [code follow step loc cpu_state cf option_map app effective set set_regs regs mem put Nat.eqb].
   rewrite BX,!Z.add_0_r;fold (point e) (tables e).
   rewrite (word_fits (point e)),(word_fits (tables e)) by (destruct(scratch_ok _ P) as [[L H] _];unfold point,tables,word64;lia).
   replace (o+(180+Z.of_nat 5+(origin-(site+185)))) with (bias+origin) by (unfold o;ring).
   rewrite (word_fits _ Dest);replace (bias+origin-o) with (origin-site) by (unfold o;ring);rewrite Slot;reflexivity. }
 assert (Safe:confined (writable e) [w]) by (constructor;[intros x X;left;
   change (frame pol e<=x<frame pol e+8) in X;unfold span,frame,common_top,Rows.frame,sp in *;destruct pol;lia|constructor]).
 pose proof(EligibleLanes.writes _ _ _ _ _ E) as Acc;destruct(mapped_now _ _ _ I _ _ _ Acc (in_common pol)) as [Map Sep].
 destruct(at_segment _ _ p o CommonBytes.symbol_bytes 4 161 _ _ Acc PC Map Sep Run Safe) as [Next Paid].
 set (q:=LinkedRun.finish o p (State(Running(origin-site)) callee (LinkedRun.carry p),[w])) in *.
 assert (G:regs callee=put (regs args) 4 (frame pol e)).
 { unfold callee,args;cbn [push push_words with_words regs set set_regs put Nat.eqb];now rewrite Slot. }
 assert (M:mem callee=store_word (mem s) (frame pol e) (o+185)).
 { unfold callee,args;cbn [push push_words with_words regs set set_regs mem put Nat.eqb];now rewrite Slot. }
 exists q;split;[exact Next|constructor];change (machine q) with callee.
 - change (o+(origin-site)=bias+origin);unfold o;ring.
 - exact Paid.
 - exact (segment_wf _ _ _ p q (EligibleLanes.words _ _ _ _ _ E) Next).
 - rewrite G;repeat split;reflexivity.
 - rewrite M;apply read_word_exact;[exact Ret|intros k B;unfold store_word;apply write_at,B].
 - intros r A B C D;rewrite G;unfold args;cbn [set set_regs regs];unfold put.
   repeat match goal with |-context[(?n=?r)%nat]=>rewrite (proj2(Nat.eqb_neq n r) ltac:(lia)) end;reflexivity.
 - exact M.
 - reflexivity.
Qed.
