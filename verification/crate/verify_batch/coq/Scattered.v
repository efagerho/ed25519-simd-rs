From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.ScalarBytes execution.ScalarByteMemory execution.PreservedRegister execution.MappedFetch
 memory.FlatMemory memory.MemoryGeometry memory.ByteMemory memory.WriteTrace abi.SysV.
From Ed25519Simd.Zip215 Require ScatterBytes ScatterTrace ScatterReturn.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
Import ListNotations. Local Open Scope Z_scope.
Module S:=Zip215.ScatterTrace.
Local Notation base:=Zip215.ScatterBytes.address.
Definition execute bias:=returning (bias+base) (length Zip215.ScatterBytes.symbol_bytes) 88.
Definition region e x:=output e<=x<output e+Z.of_nat(Scatter.count e).

Lemma live_preserves r o l s c t ws : In r sysv_saved ->
 ScalarBytes.fetch o S.code (State(Running(S.offset l)) s c)=Some(t,ws) ->
 regs(cpu_state t) r=regs s r.
Proof.
 intros Member;rewrite S.fetched;destruct l;
 match goal with |-context[S.fetch_at ?lab]=>let d:=eval vm_compute in (S.fetch_at lab) in change (S.fetch_at lab) with d end;
 apply step_keeps;destruct Member as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity.
Qed.
Lemma saved_after r o a n s ws t : In r sysv_saved -> ScalarBytes.steps o S.code s ws t ->
 word64 n -> fits64 a n -> S.invariant a n s -> regs(cpu_state t) r=regs(cpu_state s) r.
Proof.
 intros Member;induction 1 as [s|s mid last own tail F R IH];intros N Range Inv;[reflexivity|].
 destruct s as [[off|back] s c];[|discriminate]. destruct Inv as [D [L [l [PC Guard]]]];cbn [loc] in PC;subst off.
 destruct(S.live_step o a n l s c N Range D L Guard) as [u [log [Step [_ Next]]]].
 rewrite F in Step;injection Step as <- <-;rewrite (IH N Range Next);exact (live_preserves _ _ _ _ _ _ _ Member F).
Qed.
Record result e p q back:Prop:=Result {
 target:ip q=word back; stack:regs(machine q) 4%nat=Rows.frame e;
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 writes:accounted e (writable e) q; bytes:byte_memory(mem(machine q));
 stores:exists ws,confined (region e) ws /\ log q=log p++ws /\ mem(machine q)=replay (mem(machine p)) ws
}.
Theorem checked pol bias e p back : placement e -> loaded pol bias (mem e) (writable e) ->
 accounted e (writable e) p -> ip p=bias+base -> regs(machine p) 4%nat=Rows.frame e-8 ->
 read_word(mem(machine p))(Rows.frame e-8)=back -> regs(machine p) 6%nat=output e ->
 regs(machine p) 2%nat=Z.of_nat(Scatter.count e) -> byte_memory(mem(machine p)) ->
 exists q,execute bias p=Some q /\ result e p q back.
Proof.
 intros P I Prev At SP Back D N B;set (len:=Z.of_nat(Scatter.count e)) in *;set (top:=Rows.frame e-8) in *.
 destruct(stack_ok _ P) as [[L H] _];assert(T:word64 top) by (unfold top,Rows.frame,sp,word64 in *;lia).
 assert (Len:word64 len) by (unfold len,Scatter.count;rewrite Z2Nat.id by apply (initial_cpu _ P);apply (initial_cpu _ P)).
 destruct(mapped_now _ _ _ I _ _ _ Prev (LoadedImage.scatter pol)) as [Map Sep].
 assert (Const:forall x,bias+base<=x<bias+base+Z.of_nat(length Zip215.ScatterBytes.symbol_bytes) -> ~S.output (output e) len x).
 { intros x X Y;apply (Sep x X);right;right;exact Y. }
 destruct(Zip215.ScatterReturn.mapped_termination _ _ (carry p) _ _ eq_refl Len (out_ok _ P) D N Map Const)
   as [k [t [ws [dest [Bound [Steps [Trace Ret]]]]]]].
 assert (Protect:forall j,0<=j<8 -> ~S.output (output e) len (top+j)).
 { intros j J X;destruct(out_stack _ P);unfold top,len,S.output,Rows.frame,sp in *;lia. }
 destruct(Zip215.ScatterReturn.mapped_prefix _ _ _ _ _ _ _ _ _ eq_refl Len (out_ok _ P) T D N SP Back Protect Map Const Trace)
    as [Pos [Safe [M _]]];unfold Zip215.ScatterReturn.stack_position in Pos;rewrite Ret in Pos;destruct Pos as [PC Next].
 assert (All:forall xs u,ScalarBytes.steps (bias+base) S.code (State(Running 0)(machine p)(carry p)) xs u -> confined (S.output (output e) len) xs).
 { intros xs u Run;pose proof(S.scatter_confined (bias+base)(machine p)(carry p) xs u) as Eff;
   unfold S.destination,S.length64 in Eff;rewrite D,N in Eff;exact (proj1(Eff Len (out_ok _ P) Run)). }
 pose proof(proj1(MappedFetch.same_prefixes (bias+base) S.code (State(Running 0)(machine p)(carry p)) _ Map Const All ws t) Trace) as Static.
 set (q:=LinkedRun.finish (bias+base) p (t,ws)).
 assert (Returned:execute bias p=Some q).
 { unfold execute,returning;rewrite At,Z.sub_diag,(until_exact _ _ k 88 _ _ _ _ Bound Steps Ret);reflexivity. }
 exists q;split;[exact Returned|constructor];unfold q;cbn [LinkedRun.finish absolute ip log machine].
 - unfold absolute;rewrite Ret;exact PC.
 - rewrite Next;unfold top;replace (Rows.frame e-8+8) with (Rows.frame e) by ring;apply word_fits;unfold Rows.frame,sp,word64 in *;lia.
 - intros r Member;apply (saved_after r (bias+base) (output e) len _ _ _ Member Static Len (out_ok _ P)).
   split;[exact D|split;[exact N|exists S.Count;split;[reflexivity|exact Logic.I]]].
 - apply append_accounted;[exact Prev| |intros x;rewrite M;reflexivity].
   eapply Forall_impl;[|exact Safe];intros z Z x X;right;right;exact (Z x X).
 - exact (ScalarByteMemory.run_bytes k (bias+base) (length S.code) (State(Running 0)(machine p)(carry p)) t ws B Steps).
 - exists ws;auto.
Qed.

Lemma outside e p q back : result e p q back -> preserved (fun x=>~region e x) (mem(machine p)) (mem(machine q)).
Proof. intros R x X;destruct(stores _ _ _ _ R) as [ws [Safe [_ M]]];rewrite M;apply (WriteTrace.frame _ _ Safe),X. Qed.
