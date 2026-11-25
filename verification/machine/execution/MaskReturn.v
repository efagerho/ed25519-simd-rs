From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordBounds
 execution.WordSemantics execution.MaskTrace execution.MaskStores memory.ByteMemory memory.FlatMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

Fixpoint select {A} (t:trace A) input initial : option (circuit * arg * A) := match t with
 | Fault=>None | Exit gs a r=>Some(gs,a,r)
 | Written _ rest=>select rest input initial
 | Branch gs a imm yes no=>select (if mask_value gs a input initial=?imm then yes else no) input initial end.
Lemma selected_result {A} (t:trace A) input initial :
 option_map (fun '(gs,a,_)=>mask_value gs a input initial) (select t input initial)=result t input initial.
Proof. induction t;cbn [select MaskTrace.result option_map];try reflexivity;try assumption;destruct (_=?_);assumption. Qed.

Definition known_flags (zero carry:bool):=(Some zero,Some carry).
Definition status shift gs input initial (zf cf:option bool) f:=let mask a:=mask_value gs a input initial in
 match f with
 | IncomingFlags=>(zf,cf)
 | MaskTest a=>known_flags (mask a=?0) (mask a=?65535)
 | EaxCompare a imm=>let ax:=mask a mod 2^32 in known_flags (ax=?imm) (ax<?imm)
 | AlignedStack new=>known_flags (word(shift+new)=?0) false
 | SubtractedStack old imm=>let sp:=word(shift+old) in known_flags (word(sp-word imm)=?0) (sp<?word imm)
 end.
Definition predicate gs input initial incoming (v:exit_registers) k j:=
 match final_masks v k with None=>incoming k j
 |Some a=>(j<?8)%nat && Z.testbit (value j gs (input j) (initial j) a) 0 end.

Definition saved_log slide pad (t:trace exit_registers) input p:=let s:=machine p in
 events slide (LinkedCalls.regs s 4%nat) pad (LinkedCalls.regs s 5%nat) t input (vectors s).
Definition resume slide pad t input p bank gs a (v:exit_registers):=
 let s:=machine p in let top:=LinkedCalls.regs s 4%nat in let initial:=vectors s in
 let ws:=saved_log slide pad t input p in let m:=replay (mem s) ws in
 let rs:=put (put (LinkedCalls.regs s) 0 (word(mask_value gs a input initial))) 4 (word(top+8)) in
 let vec:=fun j r=>word (value j gs (input j) (initial j) (final_vectors v r)) in
 let '(zf,cf):=status (top-MaskStores.origin pad) gs input initial (flag s) (carry p) (final_flags v) in
 (Cursor (word(read_word m top)) (CPU rs vec zf m) cf (log p++ws),predicate gs input initial bank v).
Definition execute slide pad (t:trace exit_registers) input p bank:=
 option_map (fun '(gs,a,v)=>resume slide pad t input p bank gs a v) (select t input (vectors(machine p))).

Definition source_rows rows s input:=forall (b i j:nat),(i<rows b)%nat -> (j<8)%nat ->
 input j b i=read_word (mem s) (word(LinkedCalls.regs s b+64*Z.of_nat i+8*Z.of_nat j)).
Lemma rendered_bytes slide top pad bp t input initial (m:FlatMemory.bytes):byte_memory m ->
 byte_memory(replay m (events (A:=exit_registers) slide top pad bp t input initial)).
Proof.
 unfold events;remember (writes_on t input initial) as sites;clear Heqsites;revert m;
 induction sites as [|u sites IH];intros m B;[exact B|];cbn [map replay fold_left];apply IH.
 unfold render;destruct(stored u);unfold commit;apply write_bytes_well_formed;try exact B;
 intros;apply word_byte_bound.
Qed.

Record returned slide pad depth (t:trace exit_registers) input p mask q:Prop:=Returned {
 stores:confined (fun x=>LinkedCalls.regs(machine p) 4%nat-depth<=x<LinkedCalls.regs(machine p) 4%nat) (saved_log slide pad t input p);
 history:log q=log p++saved_log slide pad t input p;
 memory:mem(machine q)=replay (mem(machine p)) (saved_log slide pad t input p);
 back:ip q=word(read_word (mem(machine p)) (LinkedCalls.regs(machine p) 4%nat));
 stack:LinkedCalls.regs(machine q) 4%nat=word(LinkedCalls.regs(machine p) 4%nat+8);
 eax:LinkedCalls.regs(machine q) 0%nat=word mask;
 other:forall i,i<>0%nat -> i<>4%nat -> LinkedCalls.regs(machine q) i=LinkedCalls.regs(machine p) i;
 words:LinkedCalls.well_formed(machine q)
}.
Theorem checked slide pad depth t input p bank mask :
 stack_writes depth pad t -> LinkedCalls.well_formed(machine p) ->
 result t input (vectors(machine p))=Some mask ->
 exists q ks,execute slide pad t input p bank=Some(q,ks) /\ returned slide pad depth t input p mask q.
Proof.
 intros Bound W R;set(s:=machine p) in *;set(initial:=vectors s) in *.
 pose proof(selected_result t input initial) as Selected;rewrite R in Selected;
 destruct(select t input initial) as [[[gs a] v]|] eqn:Pick;try discriminate;injection Selected as <-.
 pose proof(proj1(Bound input initial)) as Range.
 pose proof(footprint slide (LinkedCalls.regs s 4%nat) pad (LinkedCalls.regs s 5%nat) t depth input initial Range) as Safe.
 fold (saved_log slide pad t input p) in Safe.
 unfold execute;fold s initial;rewrite Pick;cbn [option_map];unfold resume;fold s initial.
 destruct(status _ _ _ _ _ _ _) as [zf cf];eexists;eexists;split;[reflexivity|constructor];cbn [ip machine log LinkedCalls.regs mem vectors].
 - exact Safe.
 - reflexivity.
 - reflexivity.
 - change (word(read_word (replay (mem s) (saved_log slide pad t input p)) (LinkedCalls.regs s 4%nat))=word(read_word (mem s) (LinkedCalls.regs s 4%nat))).
   f_equal;apply preserved_read with (outside:=fun x=>LinkedCalls.regs s 4%nat<=x);
   [intros x X;apply (WriteTrace.frame _ _ Safe);unfold s in *;lia|intros off O;change (0<=off<8) in O;lia].
 - reflexivity.
 - reflexivity.
 - intros i A B;destruct i as [|[|[|[|[|i]]]]];congruence || reflexivity.
 - split.
   + intro i;destruct i as [|[|[|[|[|i]]]]];apply mod64_word || apply (proj1 W).
   + split;[intros;apply mod64_word|apply rendered_bytes,(proj2(proj2 W))].
Qed.
