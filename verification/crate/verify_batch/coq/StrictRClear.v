From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictRStart.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).

(* Both strict-R tests clear the rejected lanes in R12D and take the same
   rejection branch if the intersection is empty. NOT leaves flags alone. *)
Definition start (weak:bool):=if weak then 170 else 151.
Definition next weak m:=if m=?0 then 554 else start weak+11.
Definition code weak:list line:=let off:=start weak in [(off,2%nat,Not32 0);
 (off+2,3%nat,And32 12 0);(off+5,6%nat,Branch Equal (554-(off+11)))].
Lemma image weak:linked text (code weak).
Proof. destruct weak;repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Definition clear live rejected:=Z.land live (Z.lnot rejected mod 2^32) mod 2^32.
Lemma bounded live rejected : 0<=live<256 -> 0<=clear live rejected<256.
Proof. intro L;unfold clear;rewrite Z.land_comm;pose proof(EligibleLanes.masked_byte (Z.lnot rejected mod 2^32) live L);rewrite Z.mod_small by lia;assumption. Qed.
Lemma bits live rejected j : (j<8)%nat -> Z.testbit (clear live rejected) (Z.of_nat j)=
 (Z.testbit live (Z.of_nat j) && negb(Z.testbit rejected (Z.of_nat j)))%bool.
Proof. intro J;unfold clear;rewrite Z.mod_pow2_bits_low,Z.land_spec,Z.mod_pow2_bits_low,Z.lnot_spec by lia;reflexivity. Qed.
Definition execute bias:=segment (bias+pc) text 3.
Definition post weak bias e p q:=let s:=machine p in let m:=clear (regs s 12%nat) (regs s 0%nat) in
 ip q=bias+pc+next weak m /\ accounted e (writable e) q /\ well_formed(machine q) /\
 mem(machine q)=mem s /\ log q=log p /\ regs(machine q) 12%nat=m /\
 forall g,g<>0%nat -> g<>12%nat -> regs(machine q) g=regs s g.

Lemma checked weak bias e p : loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+pc+start weak -> accounted e (writable e) p -> well_formed(machine p) ->
 exists q,execute bias p=Some q /\ post weak bias e p q.
Proof.
 intros I PC A W;set (o:=bias+pc);set (s:=machine p);set (m:=clear (regs s 12%nat) (regs s 0%nat)).
 set (v:=with_zf (set (set s 0 (Z.lnot(regs s 0%nat) mod 2^32)) 12 m) (m=?0)).
 assert (R:run 3 (ScalarBytes.fetch o text) (State(Running(start weak)) s (carry p))=
    Some(State(Running(next weak m)) v (Some false),[])).
 { apply (InstructionRoute.checked _ _ _ (image weak));unfold code.
   cbn [follow step loc cpu_state cf option_map with_zf set set_regs put Nat.eqb eval_condition flag regs app].
   unfold clear in m;fold m;unfold v,next;destruct weak;cbn [start];destruct (m=?0);reflexivity. }
 destruct(mapped_now _ _ _ I _ _ _ A (ScoreSetup.image Dalek)) as [Map Sep].
 destruct(at_segment _ _ _ o text 3 _ _ _ A PC Map Sep R (Forall_nil _)) as [Step Paid].
 eexists;split;[exact Step|];unfold post;cbv zeta;split;[reflexivity|split;[exact Paid|split]].
 - exact (segment_wf _ _ _ _ _ W Step).
 - split;[reflexivity|split;[apply app_nil_r|split;[reflexivity|]]].
   intros g X Y;change (put (put (regs s) 0 (Z.lnot (regs s 0%nat) mod 2^32)) 12 m g=regs s g).
   unfold put;destruct(Nat.eqb_spec 12 g), (Nat.eqb_spec 0 g);congruence.
Qed.
