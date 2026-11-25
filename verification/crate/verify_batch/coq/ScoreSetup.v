From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls abi.SysV execution.LinkedRun execution.ScalarBytes
 execution.InstructionRoute execution.MappedFetch execution.ScalarWords execution.WordBounds execution.WordSemantics
 memory.FlatMemory memory.ByteMemory memory.WriteTrace memory.MemoryGeometry.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
Import ListNotations. Local Open Scope Z_scope.

Definition callee pol:=match pol with Zip215=>Zip215.DecodedBytes.address | Dalek=>DalekPostHash.DecodedBytes.address end.
Definition code pol:=match pol with Zip215=>Zip215.DecodedBytes.symbol_bytes | Dalek=>DalekPostHash.DecodedBytes.symbol_bytes end.
Lemma image pol: In (callee pol,code pol) (children pol).
Proof. apply in_or_app;right;destruct pol;cbn [callee code];[left|right;left];reflexivity. Qed.

(* The validity byte and eligibility qword are read before the caller reuses
   those stack slots for two of the candidate's input pointers. *)
Definition capture:list line:=[
 (458,8%nat,LeaG 7 (Address 4 None 768));(466,4%nat,Load64 0 (Address 7 None 64));
 (470,8%nat,Store64 0 (Address 4 None 856));(478,4%nat,LoadZX8 2 (Address 7 None 72));
 (482,8%nat,Load64 0 (Address 4 None 944))].
Definition stage:list line:=[(490,4%nat,Store64 0 (Address 7 None 64));
 (494,7%nat,LeaG 0 (Address 15 None 512));(501,4%nat,Store64 0 (Address 7 None 72));
 (505,4%nat,LeaG 0 (Address 4 None 0));(509,4%nat,Store64 0 (Address 7 None 80));
 (513,7%nat,LeaG 6 (Address 15 None 2304))].
Definition call pol pc:list line:=[(520,8%nat,LeaG 1 (Address 4 None 856));
 (528,3%nat,CopyG 8 14);(531,3%nat,CopyG 9 13);(534,5%nat,CallRelative(callee pol-(pc+539)))].
Definition path pol pc:=capture++stage++call pol pc.
Definition bound pol pc text:=linked text (path pol pc) /\ (539<length text)%nat.
Definition execute o text:=segment o text 15.
Definition events o t dst m:=[
 qword (word(o+470)) (t+856) (read_word m (t+832));qword (word(o+490)) (t+832) (read_word m (t+944));
 qword (word(o+501)) (t+840) (dst+512);qword (word(o+509)) (t+848) t;qword (word(o+534)) (t-8) (o+539)].
Definition arguments s t dst valid out n:=regs s 4%nat=t-8 /\ regs s 7%nat=t+768 /\ regs s 6%nat=dst+2304 /\
 regs s 2%nat=valid /\ regs s 1%nat=t+856 /\ regs s 8%nat=out /\ regs s 9%nat=n.

Ltac alu := cbn [capture stage call follow step loc cpu_state cf option_map push push_words regs effective set set_regs with_words mem put Nat.eqb app];
 rewrite ?Z.add_0_r.
Ltac fit := repeat match goal with |-context[word ?x]=>rewrite (word_fits x ltac:(unfold word64 in *;lia)) end.
Ltac keep_gpr := intros;cbn [regs set set_regs with_words push push_words];unfold put;
 repeat match goal with |-context[Nat.eqb ?i ?j]=>destruct(Nat.eqb_spec i j);subst;try congruence end;reflexivity.

Lemma capture_run o text s c t : linked text capture -> regs s 4%nat=t -> 8<=t -> t+960<2^64 -> byte_memory(mem s) ->
 let w:=qword (word(o+470)) (t+856) (read_word (mem s) (t+832)) in
 exists u,run 5 (ScalarBytes.fetch o text) (State(Running 458) s c)=Some(State(Running 490) u c,[w]) /\
 regs u 7%nat=t+768 /\ regs u 2%nat=mem s (t+840) /\ regs u 0%nat=read_word(mem s)(t+944) /\
 (forall r,r<>0%nat -> r<>2%nat -> r<>7%nat -> regs u r=regs s r).
Proof.
 intros Code SP L H Bytes w.
 assert (Mask:commit (mem s) w (t+840)=mem s (t+840)) by (apply write_outside;unfold w;cbn [qword address size];lia).
 assert (Base:read_word (commit (mem s) w) (t+944)=read_word(mem s)(t+944)).
 { apply preserved_read with (outside:=fun x=>~span (t+856) 8 x);[intros x X;apply write_outside,X|intros k K;change (0<=k<8) in K;unfold span;lia]. }
 eexists;split;[apply (InstructionRoute.checked _ _ _ Code)|].
 all: cbn [capture];alu;rewrite ?SP,?Z.add_0_r;fit.
 all: replace (t+768+64) with (t+832) by ring;replace (t+768+72) with (t+840) by ring;fold w.
 all: rewrite ?Mask,?Base,?(Z.mod_small (mem s (t+840)) _ (Bytes _));repeat split;try reflexivity.
 keep_gpr.
Qed.

Lemma stage_run o text s c t d base : linked text stage -> regs s 4%nat=t -> regs s 7%nat=t+768 -> regs s 15%nat=d ->
 regs s 0%nat=base -> 8<=t -> t+960<2^64 -> 0<=d -> d+2304<2^64 ->
 exists u,run 6 (ScalarBytes.fetch o text) (State(Running 490) s c)=Some(State(Running 520) u c,
 [qword (word(o+490)) (t+832) base;qword (word(o+501)) (t+840) (d+512);qword (word(o+509)) (t+848) t]) /\
 regs u 6%nat=d+2304 /\ (forall r,r<>0%nat -> r<>6%nat -> regs u r=regs s r).
Proof.
 intros Code SP DI DS AX L H D DH;eexists;split;[apply (InstructionRoute.checked _ _ _ Code)|].
 all: cbn [stage];alu;rewrite ?SP,?DI,?DS,?AX,?Z.add_0_r;fit.
 all: replace (t+768+64) with (t+832) by ring;replace (t+768+72) with (t+840) by ring;replace (t+768+80) with (t+848) by ring.
 all: repeat split;try reflexivity.
 keep_gpr.
Qed.

Lemma call_run pol bias pc text s c t : linked text (call pol pc) -> regs s 4%nat=t ->
 8<=t -> t+960<2^64 -> word64(bias+callee pol) ->
 let o:=bias+pc in exists u,run 4 (ScalarBytes.fetch o text) (State(Running 520) s c)=Some(State(Running(callee pol-pc)) u c,
 [qword (word(o+534)) (t-8) (o+539)]) /\ regs u 4%nat=t-8 /\ regs u 1%nat=t+856 /\
 regs u 8%nat=regs s 14%nat /\ regs u 9%nat=regs s 13%nat /\
 (forall r,r<>1%nat -> r<>4%nat -> r<>8%nat -> r<>9%nat -> regs u r=regs s r).
Proof.
 intros Code SP L H Target o;eexists;split.
 - apply (InstructionRoute.checked _ _ _ Code);alu;rewrite ?SP,?Z.add_0_r;fit.
   replace (o+(534+Z.of_nat 5+(callee pol-(pc+539)))) with (bias+callee pol) by (unfold o;ring).
   rewrite ?(word_fits _ Target);replace (bias+callee pol-o) with (callee pol-pc) by (unfold o;ring);reflexivity.
 - cbn [with_words regs put Nat.eqb];repeat split;try reflexivity. keep_gpr.
Qed.

Lemma raw pol bias pc text s c t dst : linked text (path pol pc) -> regs s 4%nat=t -> regs s 15%nat=dst ->
 8<=t -> t+960<2^64 -> 0<=dst -> dst+2304<2^64 -> word64(bias+callee pol) -> byte_memory(mem s) ->
 let o:=bias+pc in exists last,
 run 15 (ScalarBytes.fetch o text) (State(Running 458) s c)=Some(last,events o t dst (mem s)) /\
 loc last=Running(callee pol-pc) /\ arguments (cpu_state last) t dst (mem s (t+840)) (regs s 14%nat) (regs s 13%nat) /\
 (forall r,In r sysv_saved -> regs(cpu_state last) r=regs s r).
Proof.
 intros Code SP DS L H D DH Target Bytes o;unfold path,linked in Code;rewrite !Forall_app in Code;destruct Code as [A [B C]].
 destruct(capture_run o text s c t A SP L H Bytes) as [a [RunA [DI [DX [AX G]]]]].
 destruct(stage_run o text a c t dst _ B ltac:(now rewrite G by discriminate) DI ltac:(now rewrite G by discriminate) AX L H D DH)
   as [b [RunB [SI K]]].
 destruct(call_run pol bias pc text b c t C ltac:(now rewrite K,G by discriminate) L H Target) as [u [RunC [Stack [CX [R8 [R9 U]]]]]].
 exists(State(Running(callee pol-pc)) u c);split.
 - exact (run_append _ _ _ _ _ RunA _ _ _ (run_append _ _ _ _ _ RunB _ _ _ RunC)).
 - split;[reflexivity|split].
   + unfold arguments;cbn [cpu_state];repeat apply conj.
     * exact Stack.
     * rewrite U,K by discriminate;exact DI.
     * rewrite U by discriminate;exact SI.
     * rewrite U,K by discriminate;exact DX.
     * exact CX.
     * rewrite R8,K,G by discriminate;reflexivity.
     * rewrite R9,K,G by discriminate;reflexivity.
   + cbn [cpu_state];intros r [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];rewrite U,K,G by discriminate;reflexivity.
Qed.

Definition slots t x:=span (t-8) 8 x \/ span (t+832) 32 x.
Lemma footprint o t d m:confined (slots t) (events o t d m).
Proof.
 apply Forall_forall;intros w [<-|[<-|[<-|[<-|[<-|[]]]]]] x X;
 unfold touches in X;cbn [qword address size] in X;change (Z.of_nat 8) with 8 in X;unfold slots,span;cbn [qword address] in X;lia.
Qed.

Lemma read_other m ip a v b : b+8<=a \/ a+8<=b ->
 read_word (commit m (qword ip a v)) b=read_word m b.
Proof.
 intro Apart;apply preserved_read with (outside:=fun x=>~span a 8 x);
 [intros x X;apply write_outside,X|intros k K;change (0<=k<8) in K;unfold span;lia].
Qed.

(* Outputs are reread from the very memory that contains the overlapping
   scorer argument block and the return address pushed by CALL. *)
Lemma readback o t dst m : word64(o+539) -> word64 t -> word64(dst+512) -> byte_memory m ->
 let out:=replay m (events o t dst m) in read_word out (t-8)=o+539 /\
 read_word out (t+832)=read_word m (t+944) /\ read_word out (t+840)=dst+512 /\
 read_word out (t+848)=t /\ read_word out (t+856)=read_word m (t+832).
Proof.
 intros O T D W;cbn [events replay fold_left];repeat split;repeat rewrite read_other by lia;
 apply write_read_word;auto using read_word_bound.
Qed.

Record entry pol bias pc e p q:Prop:=Entry {
 target:ip q=bias+callee pol;
 stack_args:arguments (machine q) (Rows.frame e) (scratch e) (mem(machine p)(Rows.frame e+840))
                    (regs(machine p) 14%nat) (regs(machine p) 13%nat);
 saved:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 writes:accounted e (writable e) q; words:well_formed(machine q);
 store_log:log q=log p++events (bias+pc) (Rows.frame e) (scratch e) (mem(machine p));
 memory:mem(machine q)=replay (mem(machine p)) (events (bias+pc) (Rows.frame e) (scratch e) (mem(machine p)))
}.

Theorem checked pol bias pc text e p : bound pol pc text -> placement e -> loaded pol bias (mem e) (writable e) ->
 mapped (mem e) (bias+pc) text -> (forall x,bias+pc<=x<bias+pc+Z.of_nat(length text) -> ~writable e x) ->
 ip p=bias+pc+458 -> regs(machine p) 4%nat=Rows.frame e -> regs(machine p) 15%nat=scratch e ->
 accounted e (writable e) p -> well_formed(machine p) -> exists q,
 execute (bias+pc) text p=Some q /\ entry pol bias pc e p q.
Proof.
 intros [Code N] P I Map Sep IP SP DS Acc W;set (t:=Rows.frame e) in *.
 destruct(stack_ok _ P) as [[L H] Al];destruct(scratch_ok _ P) as [[D Dh] _].
 assert (Dest:word64(bias+callee pol)) by
   (apply (mapped_word _ _ _ I _ _ (image pol));destruct pol;vm_compute;reflexivity).
 destruct(raw pol bias pc text (machine p) (carry p) t (scratch e) Code SP DS ltac:(unfold t,Rows.frame,sp in *;lia)
   ltac:(unfold t,Rows.frame,sp in *;lia) D ltac:(lia) Dest (proj2(proj2 W))) as [s [Run [PC [Args Keep]]]].
 pose proof(footprint (bias+pc) t (scratch e) (mem(machine p))) as Safe.
 assert (All:confined (writable e) (events (bias+pc) t (scratch e) (mem(machine p)))).
 { eapply Forall_impl;[|exact Safe];intros w A x X;left;specialize(A x X);unfold slots,span,t,Rows.frame,sp in *;lia. }
 destruct(at_segment _ _ p _ text 15 458 _ _ Acc IP (image_after _ _ _ _ _ Acc Map Sep) Sep Run All) as [Next Paid].
 eexists;split;[exact Next|constructor].
 - cbn [LinkedRun.finish ip];unfold absolute;rewrite PC;ring.
 - exact Args.
 - exact Keep.
 - exact Paid.
 - exact (segment_wf _ _ _ _ _ W Next).
 - reflexivity.
 - exact (steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ Run)).
Qed.
