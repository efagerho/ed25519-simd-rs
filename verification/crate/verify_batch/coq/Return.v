From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds
 abi.SysV memory.ByteMemory memory.FlatMemory memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Image Rows Scatter.
Import ListNotations. Local Open Scope Z_scope.

Definition sp e := regs e 4%nat.
Definition output e := regs e 2%nat.
Definition scratch e := regs e 1%nat.
Definition span a n x := a<=x<a+n.
Definition writable e x := span (sp e-16384) 16384 x \/ span (scratch e) 25344 x \/
 span (output e) (Z.of_nat(count e)) x.

(* The root caller owns 960 local bytes plus five saved qwords. Nested
   component calls expose live buffers at their ABI and a private stack.
   Model all other bytes in those writable regions as arbitrary. *)
Record placement e : Prop := {
  initial_cpu : well_formed e;
  stack_ok : fits64 (sp e-16384) 16393 /\ sp e mod 16=8;
  scratch_ok : fits64 (scratch e) 25344 /\ scratch e mod 64=0;
  out_ok : fits64 (output e) (Z.of_nat(count e));
  scratch_stack : disjoint (scratch e) 25344 (sp e-16384) 16392;
  out_stack : disjoint (output e) (Z.of_nat(count e)) (sp e-16384) 16392;
  out_scratch : disjoint (output e) (Z.of_nat(count e)) (scratch e) 25344
}.
Fixpoint spill rs m top (regs:list nat) := match regs with
 | []=>m | r::rest=>spill rs (store_word m (top-8) (rs r)) (top-8) rest end.
Definition saved_memory e := spill (regs e) (mem e) (sp e) saved.
Definition fill e stack_bytes scratch_bytes out :=
 let m:=write_bytes (saved_memory e) (sp e-16384) (16384-40) stack_bytes in
 let m:=write_bytes m (scratch e) 25344 scratch_bytes in
 write_bytes m (output e) (Z.of_nat(count e)) (fun off=>out (Z.to_nat off)).

Fixpoint reload rs m top (order:list nat) : (nat->Z)*Z := match order with
 | []=>(rs,top) | r::rest=>reload (put rs r (read_word m top)) m (top+8) rest end.
Definition resume e m noise :=
 let rs:=fun r=>if Nat.eqb r 5 then regs e 5%nat else regs noise r in
 let '(restored,top):=reload rs m (frame e+960) (rev saved) in
 (read_word m top,with_words noise (put (put restored 0 1) 4 (top+8)) m).
Definition empty_return e :=
 (* TEST RSI,RSI set ZF on the empty branch. MOV EAX,1 and RET preserve it. *)
 caller_step 0 0 Return (set (CPU (regs e) (vectors e) (Some true) (mem e)) 0 1).

Lemma outside_spill rs m top xs x : x<top-8*Z.of_nat(length xs) \/ top<=x ->
 spill rs m top xs x=m x.
Proof.
 revert m top;induction xs as [|r xs IH];intros m top X;[reflexivity|].
 cbn [length] in X;rewrite Nat2Z.inj_succ in X. cbn [spill].
 rewrite IH by lia. apply write_outside;lia.
Qed.
Lemma spilled_word rs m top xs i r : (forall r,word64 (rs r)) ->
 nth_error xs i=Some r ->
 read_word (spill rs m top xs) (top-8*(1+Z.of_nat i))=rs r.
Proof.
 revert m top i;induction xs as [|a xs IH];intros m top [|i] W N;try discriminate.
 - injection N as ->;cbn [spill]. replace (top-8*(1+Z.of_nat 0)) with (top-8) by ring.
   apply read_word_exact;[apply W|]. intros k K;rewrite outside_spill by lia.
   unfold store_word;rewrite write_at by lia;reflexivity.
 - cbn [spill];replace (top-8*(1+Z.of_nat(S i))) with ((top-8)-8*(1+Z.of_nat i)) by lia.
   apply IH;assumption.
Qed.
Lemma saved_slots e stack_bytes scratch_bytes out a : placement e -> sp e-40<=a<sp e+8 ->
 fill e stack_bytes scratch_bytes out a=saved_memory e a.
Proof.
 intros P R. destruct P. unfold fill,disjoint in *;rewrite !write_outside by lia;reflexivity.
Qed.
Lemma rip e a b out : placement e -> read_word (fill e a b out) (sp e)=read_word (mem e) (sp e).
Proof.
 intro P. apply PrepareChunk.Staging.read_block;intros i I;rewrite saved_slots by (auto;lia).
 unfold saved_memory;apply outside_spill;lia.
Qed.
Lemma pop_slot e a b out i r : placement e -> (i<5)%nat -> nth_error saved i=Some r ->
 read_word (fill e a b out) (sp e-8*(1+Z.of_nat i))=regs e r.
Proof.
 intros P I N. rewrite <- (spilled_word (regs e) (mem e) (sp e) saved i r (proj1(initial_cpu _ P)) N).
 apply PrepareChunk.Staging.read_block;intros k K;apply saved_slots;auto;lia.
Qed.
Lemma finish e a b out noise : placement e ->
 let '(ip,s):=resume e (fill e a b out) noise in
 ip=read_word (mem e) (sp e) /\ regs s 0%nat=1 /\ regs s 4%nat=sp e+8 /\
 (forall r,In r sysv_saved -> regs s r=regs e r) /\
 (forall i,(i<count e)%nat ->mem s(output e+Z.of_nat i)=out i) /\
 preserved (fun x=>~writable e x) (mem e) (mem s).
Proof.
 intro P. unfold resume;cbn [saved rev app reload fst snd regs mem with_words].
 unfold frame;fold (sp e).
 replace (sp e-1000+960+8+8+8+8+8) with (sp e) by ring.
 rewrite rip by exact P. split;[reflexivity|]. split;[reflexivity|]. split;[reflexivity|]. split.
 - intros r [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];cbn [put Nat.eqb];try reflexivity.
   all: match goal with |-read_word _ ?x=regs ?s ?r =>
    let i:=(eval compute in (match r with 3%nat=>0%nat|12%nat=>1%nat|13%nat=>2%nat|14%nat=>3%nat|_=>4%nat end)) in
    replace x with (sp s-8*(1+Z.of_nat i)) by ring;
    apply pop_slot;[exact P|lia|reflexivity] end.
 - split.
   + intros i I;unfold fill;rewrite write_at by lia;now rewrite Nat2Z.id.
   + intros x X;unfold fill,saved_memory,writable,span in *.
     rewrite !write_outside by (intro H;apply X;intuition lia).
     apply outside_spill;change (x<sp e-8*5 \/ sp e<=x);unfold writable,span in X;lia.
Qed.
Lemma empty e : well_formed e -> word64(sp e+8) ->
 let '(ip,s):=empty_return e in ip=read_word (mem e) (sp e) /\
 regs s 0%nat=1 /\ regs s 4%nat=sp e+8 /\
 (forall r,In r sysv_saved ->regs s r=regs e r) /\ mem s=mem e.
Proof.
 intros W End;unfold empty_return,caller_step,returning,stack_step,stack_top,advance_rsp,apply_stack,
   set,set_regs,with_words;cbn [target_ip result_regs result_mem regs mem put Nat.eqb].
 fold (sp e);rewrite !(word_fits (sp e)) by apply W;rewrite (word_fits _ (read_word_bound _ _ (proj2(proj2 W)))),(word_fits _ End).
 repeat split;intros r [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity.
Qed.

Lemma all_bytes e a b out : well_formed e -> byte_memory a -> byte_memory b ->
 (forall j,(j<count e)%nat -> 0<=out j<256) -> byte_memory (fill e a b out).
Proof.
 intros [_ [_ M]] A B Out. unfold fill,saved_memory.
 apply write_bytes_well_formed;[|intros k K;apply Out;lia].
 apply write_bytes_well_formed;[|intros;apply B].
 apply write_bytes_well_formed;[|intros;apply A].
 assert (Spill:forall rs top xs m,byte_memory m -> byte_memory (spill rs m top xs)).
 { intros rs top xs;revert top;induction xs;intros top m Bytes;cbn;[exact Bytes|].
   apply IHxs,write_bytes_well_formed;[exact Bytes|intros;apply word_byte_bound]. }
 now apply Spill.
Qed.
