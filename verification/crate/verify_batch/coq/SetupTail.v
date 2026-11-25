From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.MappedFetch execution.InstructionRoute execution.AlignedRows
 execution.VectorProcedure memory.MemoryGeometry memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Machine Require execution.VectorWindow execution.Dependencies.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode DecoderSave KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderKernel DecoderProduct DecoderFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition step_at bias n:=segment (base bias) text n.
Definition carry_call bias:=wrapped (base bias) text (base bias) text (DecoderProduct.native bias DecoderKernel.Carry).
Definition finish_setup bias:=then_run (step_at bias 43) (then_run (carry_call bias)
 (then_run (step_at bias 5) (then_run (step_at bias 5) (then_run (step_at bias 1)
 (then_run (DecoderProduct.multiply_call bias) (then_run (step_at bias 5) (step_at bias 1))))))).

Definition retained signature pol e x:=link_slot pol e<=x<link_slot pol e+8 \/ address signature e<=x<address signature e+320 \/ caller_bytes pol e x.
From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Record stage signature pol bias e off p : Prop := {
 position:ip p=base bias+off; paid:accounted e (writable e) p;
 dest:regs(machine p) 7%nat=point e signature; stack:regs(machine p) 4%nat=link_slot pol e;
 link:read_word (mem(machine p)) (link_slot pol e)=word(base bias+resume_offset signature);
 encoding:raw signature e (machine p); caller: setup_caller signature pol bias e (machine p);
 constants: forall i j,(i<4)%nat -> vectors(machine p) j (28+i)%nat=DecoderFrame.constant i
}.
Definition finished signature pol bias e p := ip p=base bias+resume_offset signature /\ accounted e (writable e) p /\
 regs(machine p) 4%nat=link_slot pol e+8 /\ regs(machine p) 7%nat=point e signature /\ raw signature e (machine p) /\
 setup_caller signature pol bias e (machine p) /\
 forall i j,(i<4)%nat -> vectors(machine p) j (28+i)%nat=DecoderFrame.constant i.

Section Proof.
Variables (signature:bool) (pol:policy) (bias:Z) (e:cpu).
Hypothesis P:placement e.
Hypothesis Loaded:loaded pol bias (mem e) (writable e).
Local Notation o:=(base bias).
Local Notation st:=(link_slot pol e).
Local Notation buffer:=(point e signature).
Local Notation state:=(stage signature pol bias e).

Lemma caller_above : st+8<=common_top pol e-112 /\ common_top pol e-104<=sp e /\ sp e-2048<=common_top pol e-112.
Proof. clear Loaded P;unfold link_slot,DecoderFrame.top;pose proof(Z.mod_pos_bound (common_top pol e-112-40) 64 ltac:(lia));
 unfold common_top,Rows.frame,sp in *;destruct pol;lia. Qed.
Lemma paper off p : squared signature pol bias e p -> off=509 -> state off p.
Proof. intros [At [A [[DI [SP [Link [C Env]]]] [Raw _]]]] ->;now constructor. Qed.
Lemma transfer from to p q : state from p -> ip q=o+to -> accounted e (writable e) q ->
 (forall r,r<>8%nat -> regs(machine q) r=regs(machine p) r) ->
 (forall i j,(i<4)%nat -> vectors(machine q) j (28+i)%nat=vectors(machine p) j (28+i)%nat) ->
 preserved (retained signature pol e) (mem(machine p)) (mem(machine q)) -> state to q.
Proof.
 intros [At A DI SP Link Raw Caller C] End Done G V M;constructor;try assumption.
 - rewrite G by discriminate;exact DI.
 - rewrite G by discriminate;exact SP.
 - rewrite <-Link;apply preserved_read with (outside:=retained signature pol e);[exact M|intros k K;left;lia].
 - intros j J;destruct(Raw j J) as [B [Y Sign]].
   assert (D:forall i,(i<5)%nat -> digits signature e (machine q) j i=digits signature e (machine p) j i).
   { intros i I;apply preserved_read with (outside:=retained signature pol e);[exact M|intros k K;right;left;change (0<=k<8) in K;lia]. }
   split;[intros i I;rewrite D by exact I;apply B,I|split;[rewrite <-Y;apply Radix51.limbs_ext,D|rewrite G by discriminate;exact Sign]].
 - apply (keep_caller _ _ _ _ _ _ Caller);[intros r R;apply G;intros ->;unfold caller_reg in R;cbn in R;lia|intros x X;apply M;right;right;exact X].
 - intros i j I;rewrite V by exact I;apply C,I.
Qed.

Lemma window off last n lo hi p : VectorWindow.scan text 7 lo hi off n=Some last -> VectorWindow.check_registers text 28 off n=true ->
 (0<=lo /\ hi<=1280) -> (hi<=320 \/ 640<=lo) -> state off p ->
 exists q,step_at bias n p=Some q /\ state last q.
Proof.
 intros Scan Upper Bounds Away State;destruct State as [At A DI SP Link Raw Caller C].
 destruct(scratch_ok _ P) as [[L H] Al].
 assert (Aligned:buffer mod 64=0) by (apply point_aligned;exact Al).
 destruct(VectorWindow.execute o text 7 lo hi buffer n off last (machine p) (carry p) Scan DI Aligned
    ltac:(unfold point,point_offset;destruct signature;lia) ltac:(unfold point,point_offset;destruct signature;lia)) as [s [ws [R [G W]]]].
 assert (Safe:confined (writable e) ws).
 { apply Forall_impl with (P:=permits (VectorWindow.interval buffer lo hi));[|exact W].
   intros w V x X;specialize(V x X);right;left;unfold VectorWindow.interval,span,point,point_offset in *;destruct signature;lia. }
 destruct(mapped_now _ _ _ Loaded _ _ _ A (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text _ off _ _ A At Map Sep R Safe) as [Next Done].
 eexists;split;[exact Next|eapply transfer;[constructor;eassumption|reflexivity|exact Done| | |]].
 - intros r _;exact (f_equal (fun rs=>rs r) G).
 - intros i j I;exact (VectorWindow.upper_registers _ _ _ _ _ _ _ _ _ Upper R j (28+i)%nat ltac:(lia)).
 - pose proof(steps_memory _ _ _ _ _ (run_steps _ _ _ _ _ _ R)) as Mem;change (mem s=WriteTrace.replay (mem(machine p)) ws) in Mem.
   intros x Protect;change (mem s x=mem(machine p) x);rewrite Mem;apply (WriteTrace.frame _ _ W).
   pose proof(depth pol e);pose proof caller_above;destruct(scratch_stack _ P);unfold retained,caller_bytes,address,VectorWindow.interval,disjoint,point,point_offset in *;destruct signature;lia.
Qed.

Lemma arithmetic_call effect depth off last p f :
 effect_contract e (writable e) (DecoderProduct.area e) (o+off) (o+last) depth effect f ->
 (forall s t,effect s t -> forall i j,(i<4)%nat -> vectors t j (28+i)%nat=vectors s j (28+i)%nat) ->
 0<=depth<=24 -> state off p -> exists q,f p=Some q /\ state last q /\ effect_result e (writable e) p q depth (o+last) effect.
Proof.
 intros Call Upper D State;destruct State as [At A DI SP Link Raw Caller C].
 pose proof(KeySquare.depth pol e) as Deep.
 destruct(Call p At A ltac:(change (sp e-16384+depth<=regs(machine p) 4%nat<=sp e);rewrite SP;lia))
   as [q [R [End Done G Keep V]]].
 exists q;split;[exact R|split;[|now constructor]];eapply (transfer off last p q);[constructor;eassumption|exact End|exact Done|intros;apply G|apply (Upper _ _ V)|].
 intros x X;apply Keep;rewrite SP;pose proof caller_above;destruct(scratch_stack _ P);unfold retained,caller_bytes,address,disjoint,point,point_offset in *;destruct signature;lia.
Qed.

Lemma carry_checked : contract e (writable e) (DecoderProduct.area e) (o+779) (o+784) 8
 (DecoderKernel.body DecoderKernel.Carry) (carry_call bias).
Proof.
 apply (invoke _ _ _ o text 779 (0xa7e-784) o text 0xadd 0).
 - apply DecoderProduct.stack,P.
 - lia.
 - exact (DecoderProduct.placed pol bias e Loaded DecoderKernel.Carry).
 - exact (DecoderProduct.placed pol bias e Loaded DecoderKernel.Carry).
 - lia.
 - vm_compute;reflexivity.
 - lia.
 - vm_compute;reflexivity.
 - replace (o+(779+5)+(0xa7e-784)) with (o+0xa7e) by ring;exact (DecoderProduct.address_fits pol bias e Loaded DecoderKernel.Carry 0xa7e ltac:(vm_compute;split;discriminate || reflexivity)).
 - exact (DecoderProduct.address_fits pol bias e Loaded DecoderKernel.Carry 784 ltac:(vm_compute;split;discriminate || reflexivity)).
 - replace (o+(779+5)+(0xa7e-784)) with (o+0xa7e) by ring;exact (DecoderProduct.calc pol bias e Loaded DecoderKernel.Carry).
Qed.

Lemma reload p : state 819 p -> exists q,step_at bias 5 p=Some q /\ state 853 q /\ mem(machine q)=mem(machine p) /\
 forall j i,(i<5)%nat -> vectors(machine q) j i=read_word (mem(machine p)) (buffer+64*Z.of_nat i+8*Z.of_nat j).
Proof.
 intros S;destruct S as [At A DI SP Link Raw Caller C];destruct(scratch_ok _ P) as [[L H] Al].
 assert (Aligned:buffer mod 64=0) by (apply point_aligned;exact Al).
 assert (Bytes:linked text (AlignedRows.route false 819 0 7 0 5)) by (repeat constructor;vm_compute;discriminate || reflexivity).
 destruct(AlignedRows.loads o _ 5 819 0 7 0 buffer (machine p) (carry p) Bytes ltac:(lia) Aligned ltac:(unfold fits64,point,point_offset;destruct signature;lia))
    as [s [R [G [M [_ [Rows High]]]]]].
 destruct(mapped_now _ _ _ Loaded _ _ _ A (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text _ 819 _ _ A At Map Sep R (Forall_nil _)) as [Next Done].
 eexists;split;[exact Next|split;[|exact (conj M Rows)]].
 eapply transfer;[constructor;eassumption|reflexivity|exact Done|intros r _;exact (f_equal (fun rs=>rs r) G)|intros i j I;apply High;lia|intros x _;exact (f_equal (fun m=>m x) M)].
Qed.

Definition operand_address:list line:=[(853,7%nat,LeaG 8 (Address 7 None 640))].
Lemma pointer p : state 853 p -> exists q,step_at bias 1 p=Some q /\ state 860 q /\ regs(machine q) 8%nat=buffer+640 /\
 mem(machine q)=mem(machine p) /\ vectors(machine q)=vectors(machine p).
Proof.
 intros S;destruct S as [At A DI SP Link Raw Caller C];destruct(scratch_ok _ P) as [[L H] Al].
 assert (B:linked text operand_address) by (repeat constructor;vm_compute;discriminate || reflexivity).
 set (s:=set (machine p) 8 (buffer+640)).
 assert (R:run 1 (ScalarBytes.fetch o text) (State (Running 853) (machine p) (carry p))=Some(State (Running 860) s (carry p),[])).
 { apply (checked _ _ _ B);cbn [operand_address follow loc cf cpu_state step effective option_map];rewrite DI,Z.add_0_r,word_fits by (unfold word64,point,point_offset;destruct signature;lia);reflexivity. }
 destruct(mapped_now _ _ _ Loaded _ _ _ A (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text _ 853 _ _ A At Map Sep R (Forall_nil _)) as [Next Done].
 eexists;split;[exact Next|split;[|repeat split;reflexivity]].
 eapply (transfer 853 860 p);[now constructor|reflexivity|exact Done| |intros;reflexivity|intros x X;reflexivity].
 intros r Other;change (Instructions.put (regs(machine p)) 8 (buffer+640) r=regs(machine p) r);
 unfold Instructions.put;now rewrite (proj2 (Nat.eqb_neq 8 r) ltac:(lia)).
Qed.

Lemma times p : state 860 p -> regs(machine p) 8%nat=buffer+640 ->
 let args:=DecoderProduct.arguments (push (machine p) (o+865)) in
 exists q,DecoderProduct.multiply_call bias p=Some q /\ state 865 q /\
 effect_result e (writable e) p q 24 (o+865) (DecoderProduct.multiplied args).
Proof.
 intros S Ptr;destruct S as [At A DI SP Link Raw Caller C].
 set (s:=push (machine p) (o+865));set (args:=DecoderProduct.arguments s).
 assert (R8:regs s 8%nat=buffer+640) by exact Ptr.
 assert (Need:DecoderProduct.readable args s).
 { destruct(scratch_ok _ P) as [[L H] Al];unfold DecoderProduct.readable;rewrite R8.
   split;[replace 640 with (10*64) by reflexivity;rewrite Z.mod_add by lia;apply point_aligned,Al|
          split;[unfold fits64,point,point_offset;destruct signature;lia|reflexivity]]. }
 pose proof(depth pol e) as Deep.
 destruct(DecoderProduct.call_at pol bias e 860 args P Loaded ltac:(lia) ltac:(lia) ltac:(vm_compute;reflexivity)
   p Need At A ltac:(change (sp e-16384+24<=regs(machine p) 4%nat<=sp e);rewrite SP;lia))
   as [q [R [End Done G Keep Result]]].
 exists q;split;[exact R|split;[|now constructor]];eapply (transfer 860 865 p q);[now constructor|exact End|exact Done|intros;apply G| |].
 - intros i j I;rewrite Result;destruct ((proj2 DecoderProduct.multiplication) no_read no_read (args j) (args j) ltac:(reflexivity)) as [_ High].
   rewrite High by lia;unfold args,DecoderProduct.arguments;rewrite (proj2(Nat.ltb_ge (28+i) 10) ltac:(lia)),andb_false_r;reflexivity.
 -
 intros x X;apply Keep;rewrite SP;pose proof caller_above;destruct(scratch_stack _ P);unfold retained,caller_bytes,address,disjoint,point,point_offset in *;destruct signature;lia.
Qed.

Lemma back p : state 900 p -> exists q,step_at bias 1 p=Some q /\ finished signature pol bias e q /\ mem(machine q)=mem(machine p).
Proof.
 intros [At A DI SP Link Raw Caller C];pose proof(depth pol e) as Deep;destruct(Return.stack_ok _ P) as [[L H] _].
 assert (Fits:word64(o+resume_offset signature)) by exact (DecoderProduct.address_fits pol bias e Loaded DecoderKernel.Carry (resume_offset signature)
    ltac:(destruct signature;vm_compute;split;discriminate || reflexivity)).
 assert (Ret:ScalarBytes.decode (skipn (Z.to_nat 900) text)=Some(1%nat,Ret)) by (vm_compute;reflexivity).
 set (s:=LinkedCalls.returning (machine p)).
 assert (R:run 1 (ScalarBytes.fetch o text) (State (Running 900) (machine p) (carry p))=
     Some(State (Returned (o+resume_offset signature)) s (carry p),[])).
 { cbn [run ScalarBytes.fetch loc cf cpu_state];rewrite (proj2(Z.ltb_ge 900 0) ltac:(lia)),Ret.
   change (Some(State (Returned (word(read_word (mem(machine p)) (word(regs(machine p) 4%nat))))) s (carry p),@nil store)=
       Some(State (Returned (o+resume_offset signature)) s (carry p),@nil store)).
   rewrite SP,(word_fits st ltac:(unfold word64;lia)),Link,(word_fits _ Fits),(word_fits _ Fits);reflexivity. }
 destruct(mapped_now _ _ _ Loaded _ _ _ A (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text _ 900 _ _ A At Map Sep R (Forall_nil _)) as [Next Done].
 eexists;split;[exact Next|split;[|reflexivity]];split;[reflexivity|split;[exact Done|split]].
 - change (word(regs(machine p) 4%nat+8)=st+8);rewrite SP;apply word_fits;unfold word64;lia.
 - split;[exact DI|split;[exact Raw|split;[|exact C]]].
   eapply keep_caller;[exact Caller| |intros x X;reflexivity].
   intros r K;change (Instructions.put (regs(machine p)) 4 (word(regs(machine p) 4%nat+8)) r=regs(machine p) r).
   unfold Instructions.put;destruct (Nat.eqb_spec 4 r);[subst;unfold caller_reg in K;cbn in K;lia|reflexivity].
Qed.

Inductive tail_path (p q:cursor) : Prop :=
| path a b c d f g h :
  step_at bias 43 p=Some a ->
  state 779 a -> state 784 b -> state 860 f -> state 865 g ->
  carry_call bias a=Some b ->
  effect_result e (writable e) a b 8 (o+784) (projects (DecoderKernel.body DecoderKernel.Carry)) ->
  step_at bias 5 b=Some c ->
  step_at bias 5 c=Some d -> mem(machine d)=mem(machine c) ->
  (forall j i,(i<5)%nat -> vectors(machine d) j i=read_word (mem(machine c)) (buffer+64*Z.of_nat i+8*Z.of_nat j)) ->
  step_at bias 1 d=Some f -> regs(machine f) 8%nat=buffer+640 ->
  mem(machine f)=mem(machine d) -> vectors(machine f)=vectors(machine d) ->
  DecoderProduct.multiply_call bias f=Some g ->
  effect_result e (writable e) f g 24 (o+865)
    (DecoderProduct.multiplied (DecoderProduct.arguments (push (machine f) (o+865)))) ->
  step_at bias 5 g=Some h -> mem(machine q)=mem(machine h) ->
  tail_path p q.

Theorem trace_tail p : squared signature pol bias e p -> exists q,finish_setup bias p=Some q /\ finished signature pol bias e q /\ tail_path p q.
Proof.
 intro Square;pose proof(paper _ _ Square eq_refl) as Start.
 destruct(window 509 779 43 0 320 p ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity) ltac:(lia) ltac:(lia) Start) as [a [Scale A]].
 assert (CarryFrame:forall s t,projects (DecoderKernel.body DecoderKernel.Carry) s t ->
   forall i j,(i<4)%nat -> vectors t j (28+i)%nat=vectors s j (28+i)%nat).
 { intros s t Run i j I;rewrite Run;apply Dependencies.untouched.
   apply forallb_forall;intros ins Member.
   assert (Check:forallb (fun k=>Nat.ltb (fst k) 28) (DecoderKernel.body DecoderKernel.Carry)=true) by (vm_compute;reflexivity).
   apply forallb_forall with (x:=ins) in Check;[apply Nat.ltb_lt in Check;apply Bool.negb_true_iff,Nat.eqb_neq;lia|exact Member]. }
 destruct(arithmetic_call _ 8 779 784 a _ carry_checked CarryFrame ltac:(lia) A) as [b [Carry [B CarryEffect]]].
 destruct(window 784 819 5 640 960 b ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity) ltac:(lia) ltac:(lia) B) as [c [Save C]].
 destruct(reload _ C) as [d [Load [D [LoadMem LoadRegs]]]];destruct(pointer _ D) as [f [Ptr [F [Arg [PtrMem PtrRegs]]]]].
 destruct(times _ F Arg) as [g [Mul [G Product]]].
 destruct(window 865 900 5 960 1280 g ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity) ltac:(lia) ltac:(lia) G) as [h [UV H]].
 destruct(back _ H) as [q [End [Q RetMem]]].
 exists q;split;[unfold finish_setup,then_run;rewrite Scale;cbn [bind];rewrite Carry;cbn [bind];rewrite Save;cbn [bind];
   rewrite Load;cbn [bind];rewrite Ptr;cbn [bind];rewrite Mul;cbn [bind];rewrite UV;exact End|].
 split;[exact Q|econstructor;eassumption].
Qed.
Theorem to_caller p : squared signature pol bias e p -> exists q,finish_setup bias p=Some q /\ finished signature pol bias e q.
Proof. intro S;destruct(trace_tail _ S) as [q [R [F _]]];now exists q. Qed.
End Proof.

Record checkpoints:=Checkpoints { after_square:cursor; in_decoder:cursor; masks:MaskTransfer.bank }.
Definition input_setup bias p incoming:=bind (square_input bias p incoming) (fun '(sq,k)=>
 option_map (fun q=>Checkpoints sq q k) (finish_setup bias sq)).
Definition observe bias p incoming:=bind (inner bias p) (fun q=>input_setup bias q incoming).
Definition post signature pol bias e r:=squared signature pol bias e (after_square r) /\ finished signature pol bias e (in_decoder r).

Theorem from_setup signature pol bias e p incoming : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> setup signature pol bias e p ->
 exists r,input_setup bias p incoming=Some r /\ post signature pol bias e r.
Proof.
 intros P M Al E;destruct(KeySquare.from_setup signature _ _ _ _ incoming P M Al E) as [sq [k [Trace [Value _]]]].
 destruct(to_caller signature _ _ _ P M _ Value) as [q [Run Back]].
 exists (Checkpoints sq q k);split;[unfold input_setup;rewrite Trace;cbn [bind];now rewrite Run|exact (conj Value Back)].
Qed.
Theorem from_decoder pol bias e p incoming : placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> entry pol bias e p -> exists r,observe bias p incoming=Some r /\ post false pol bias e r.
Proof.
 intros P M Al E;destruct(BatchDecode.from_decoder _ _ _ _ P M E) as [q [Run Start]].
 unfold observe;rewrite Run;exact (from_setup false _ _ _ _ incoming P M Al Start).
Qed.
End Iteration.
