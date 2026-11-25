From Coq Require Import List ZArith Lia.
From Machine Require Import isa.VectorMoves execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.ScalarBytes
 execution.MappedFetch execution.InstructionRoute memory.FlatMemory memory.ByteMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

Inductive part:=Full | Half (high:bool).
Record output:=Out { source:nat; base:nat; displacement:Z; piece:part }.
Definition native w:=match piece w with Full=>Output (source w) (base w) (displacement w)
 | Half h=>Extract (source w) (base w) (displacement w) h end.
Definition width w:=length(VectorMoves.encoding (native w)).
Fixpoint route pc ws:list line:=match ws with []=>[]|w::rest=>
 (pc,width w,VectorMove(native w))::route (pc+Z.of_nat(width w)) rest end.
Fixpoint after pc ws:=match ws with []=>pc | w::rest=>after (pc+Z.of_nat(width w)) rest end.
Definition size w:=match piece w with Full=>64%nat | _=>32%nat end.
Definition shift w:=match piece w with Half true=>4%nat | _=>0%nat end.
Definition address s w:=word(regs s (base w)+displacement w).
Definition event o pc s w:=Store (word(o+pc)) (address s w) (size w)
 (vector_byte (fun j=>vectors s (shift w+j)%nat (source w))).
Fixpoint events o pc s ws:=match ws with []=>[] | w::rest=>event o pc s w::events o (pc+Z.of_nat(width w)) s rest end.

Lemma same o pc ws s t : regs s=regs t -> vectors s=vectors t -> events o pc s ws=events o pc t ws.
Proof. intros G V;revert pc;induction ws as [|w rest IH];intro pc;cbn [events];[reflexivity|unfold event,address;now rewrite G,V,IH]. Qed.
Theorem execute o text ws : forall pc s c, linked text (route pc ws) ->
 exists t,run (length ws) (ScalarBytes.fetch o text) (State(Running pc) s c)=Some(State(Running(after pc ws)) t c,events o pc s ws) /\
 regs t=regs s /\ vectors t=vectors s /\ flag t=flag s /\ mem t=WriteTrace.replay (mem s) (events o pc s ws).
Proof.
 induction ws as [|w rest IH];intros pc s c B;[exists s;repeat split;reflexivity|].
 cbn [route] in B;apply Forall_cons_iff in B as [[Pos Dec] Tail].
 set (b:=with_words s (regs s) (commit (mem s) (event o pc s w))).
 assert (Store:step o pc (width w) (VectorMove(native w)) s c=Some(State(Running(pc+Z.of_nat(width w))) b c,[event o pc s w])).
 { destruct w as [src reg disp [|[|]]];reflexivity. }
 destruct(IH _ b c Tail) as [t [R [G [V [F M]]]]]. rewrite (same _ _ _ b s eq_refl eq_refl) in R,M.
 exists t;split.
 - cbn [length run ScalarBytes.fetch loc cpu_state cf after events];now rewrite (proj2(Z.ltb_ge _ _) Pos),Dec,Store,R.
 - split;[exact G|split;[exact V|split;[exact F|exact M]]].
Qed.
Lemma read_back o pc s w m j : (8*j<size w)%nat -> word64(vectors s (shift w+j)%nat (source w)) ->
 read_word (commit m (event o pc s w)) (address s w+8*Z.of_nat j)=vectors s (shift w+j)%nat (source w).
Proof.
 intros J Fit;apply read_word_exact;[exact Fit|];intros k K;unfold event,commit;cbn [WriteTrace.address WriteTrace.size payload].
 replace (address s w+8*Z.of_nat j+k) with (address s w+(8*Z.of_nat j+k)) by ring.
 rewrite write_at;[rewrite vector_byte_lane by exact K;reflexivity|].
 destruct (piece w) eqn:E;unfold size in *;rewrite E in *;lia.
Qed.
