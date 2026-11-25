From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordBounds execution.WordSemantics
 execution.StoreInstructions execution.MappedFetch execution.StoreHistory abi.CallHistory abi.TracedCalls abi.RunCalls abi.SysV
 memory.MemoryGeometry memory.ByteMemory memory.WriteTrace.
From Ed25519Simd Require Import Wide51 PointResults.
From Curve25519.group Require Representation.
From Ed25519Simd.LadderStep Require Import LinkedBytes Callees Audit Calls Execution LeafHistory.
Import ListNotations. Local Open Scope Z_scope.

Definition execute slide sc pad p:=
 if ip p=?slide+wrapper_pc then
 if list_eq_dec Z.eq_dec (snapshot (mem(machine p)) (ip p) (length symbol_bytes)) symbol_bytes then
 option_map (fun '(back,v,ws)=>Cursor back v None (log p++ws))
 (RunCalls.execute (leaf slide sc pad) slide wrapper_pc program (machine p))
 else None else None.

Section Trace.
Variables slide sc pad pt cache:Z.
Hypothesis P:placement_ok slide sc pad pt cache.
Local Notation region:=(writable sc pad pt).
Local Notation call:=(checked_call slide sc pad pt).
Local Notation runner:=(RunCalls.execute (leaf slide sc pad) slide).
Definition finished pc code s ret out := exists ws,runner pc code s=Some(ret,out,ws) /\
 confined region ws /\ mem out=replay (mem s) ws.
Definition covers pc code s ret out := images slide (mem s) -> runs call slide pc code s ret out -> finished pc code s ret out.

Lemma save pc g tail s ret out : let op:=Save g in let pushed:=push s (regs s g) in
 confined region (caller_stores slide pc op s) -> covers (next_pc pc op) tail pushed ret out ->
 covers pc (op::tail) s ret out.
Proof.
 intros op pushed Safe Next Map R.
 assert (M:mem pushed=replay (mem s) (caller_stores slide pc op s)) by reflexivity.
 destruct(Next ltac:(rewrite M;eapply keep;[exact P|exact Map|exact Safe]) R) as [ws [Run [C F]]].
 exists (caller_stores slide pc op s++ws);split.
 - change (option_map (prepend (caller_stores slide pc op s)) (runner (next_pc pc op) tail pushed)=Some(ret,out,caller_stores slide pc op s++ws));
   rewrite Run;reflexivity.
 - split;[now apply Forall_app|now rewrite replay_app,<-M].
Qed.

Lemma three_pushes s ret out : regs s 4%nat=sc+1320+pad -> covers wrapper_pc program s ret out.
Proof.
 intros SP;pose proof(stack_fits _ _ _ _ _ P) as Fit;pose proof(padding_bounds _ _ _ _ _ P) as Pad.
 let body:=eval cbv [skipn program prologue app] in (skipn 3 program) in
 change (covers wrapper_pc (Save 3::Save 12::Save 13::body) s ret out).
 assert (Stack:forall d,0<=d<=24 ->word(sc+1320+pad-d)=sc+1320+pad-d)
   by (intros;apply word_fits;unfold word64,fits64 in *;lia).
 apply save;[constructor;[intros x X;change (word(regs s 4%nat-8)<=x<word(regs s 4%nat-8)+8) in X;rewrite SP,Stack in X by lia;right;lia|constructor]|].
 set(a:=push s (regs s 3%nat)).
 assert (A:regs a 4%nat=sc+1320+pad-8) by (change (word(regs s 4%nat-8)=sc+1320+pad-8);now rewrite SP,Stack by lia).
 assert (B:word(regs a 4%nat-8)=sc+1320+pad-16) by
  (rewrite A;replace (sc+1320+pad-8-8) with (sc+1320+pad-16) by ring;apply Stack;lia).
 apply save;[constructor;[intros x X;change (word(regs a 4%nat-8)<=x<word(regs a 4%nat-8)+8) in X;rewrite B in X;right;lia|constructor]|].
 set(b:=push a (regs a 12%nat)).
 assert (D:word(regs b 4%nat-8)=sc+1320+pad-24).
 { change (word(word(regs a 4%nat-8)-8)=sc+1320+pad-24);rewrite B;
   replace (sc+1320+pad-16-8) with (sc+1320+pad-24) by ring;apply Stack;lia. }
 apply save;[constructor;[intros x X;change (word(regs b 4%nat-8)<=x<word(regs b 4%nat-8)+8) in X;rewrite D in X;right;lia|constructor]|].
 intros Code Run;destruct(CallHistory.collect call (fun a e r f ws=>leaf slide sc pad a e=Some(r,f,ws)) region (images slide)
   (keep _ _ _ _ _ P) (fun a e r f=>slot slide sc pad pt a e r f (proj1 Pad))
   (fun a e r f=>invoke slide sc pad pt a e r f (proj1 Pad)) slide (skipn 3 program) _ _ _ _ eq_refl Code Run)
   as [ws [Trace [Safe F]]].
 exists ws;split;[exact (RunCalls.checked _ _ _ _ _ _ _ _ Trace)|auto].
Qed.
End Trace.

Record result sc pad pt cache full p q:Prop:=Result {
 back:ip q=read_word (mem(machine p)) (regs(machine p) 4%nat);
 stack:regs(machine q) 4%nat=regs(machine p) 4%nat+8;
 saved:forall g,In g sysv_saved -> regs(machine q) g=regs(machine p) g;
 words:well_formed(machine q);
 writes:StoreHistory.extends (writable sc pad pt) p q;
 bound:Wide51.strict(buffer_words(mem(machine q))pt);
 value:group_result full (mem(machine p)) (mem(machine q)) pt cache;
 omitted:full=false ->forall i j,(i<5)%nat ->(j<8)%nat -> Wide51.cell(buffer_words(mem(machine q))pt)(15+i)%nat j=0
}.

Theorem checked slide sc pad pt cache full p : ip p=slide+wrapper_pc ->
 images slide (mem(machine p)) -> placement_ok slide sc pad pt cache -> well_formed(machine p) ->
 regs(machine p) 4%nat=sc+1320+pad -> regs(machine p) 7%nat=pt -> regs(machine p) 6%nat=cache ->
 regs(machine p) 2%nat=CachedAddABI.flag_word full -> Wide51.loose_xyz(buffer_words(mem(machine p))pt) ->
 cache_bounds false (buffer_words(mem(machine p))cache) -> cache_bounds true (buffer_words(mem(machine p))(cache+1280)) ->
 cache_bounds false (buffer_words(mem(machine p))(cache+2240)) ->
 exists q,execute slide sc pad p=Some q /\ result sc pad pt cache full p q.
Proof.
 intros PC Images Place W SP Pt Cache Mode Bound Odd Base Even.
 destruct(Execution.execute _ _ _ _ _ _ _ Place W SP Pt Cache Mode Bound Odd Base Even)
  as [out [WF [R [Stack [Kept [Frame [Reduced [Math T]]]]]]]].
 destruct(three_pushes _ _ _ _ _ Place _ _ _ SP Images R) as [ws [Run [Safe Replay]]].
 set(ret:=read_word (mem(machine p)) (sc+1320+pad)).
 set(q:=Cursor ret out None (log p++ws)).
 exists q;split.
 - unfold execute;rewrite PC,Z.eqb_refl,(snapshot_mapped _ _ _ (proj1 Images)).
   destruct(list_eq_dec _ _ _) as [_|Bad];[now rewrite Run|contradiction].
 - constructor;try exact WF;try exact Reduced;try exact T;try exact Kept.
   + unfold q,ret;cbn [ip];now rewrite SP.
   + change (regs out 4%nat=regs(machine p) 4%nat+8);now rewrite SP.
   + exists ws;split;[reflexivity|split;[exact Safe|intro x;exact (f_equal (fun m=>m x) Replay)]].
   + intros j P A B E J I U V X;eapply Representation.represents_equivalent;[apply (Math j J)|].
     eapply Representation.ladder_represents;eassumption.
Qed.
