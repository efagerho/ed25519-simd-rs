From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.ScalarBytes
 execution.Dependencies execution.VectorProcedure execution.WordBounds memory.ByteMemory memory.FlatMemory.
From Ed25519Simd.Decode Require Scale DecoderBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterColumns SetupValues.
Local Open Scope Z_scope.

Definition offset phase:=Z.of_nat(FilterColumns.offset phase+FilterColumns.size phase).
Definition target:=DecoderFrame.origin+0xa7e.
Definition execute bias:=wrapped (bias+FilterLoad.site) FilterLoad.text (bias+DecoderFrame.origin) DecoderFrame.code
   (DecoderProduct.native bias DecoderKernel.Carry).
Lemma call phase:decode (skipn (Z.to_nat(offset phase)) FilterLoad.text)=Some(5%nat,CallRelative(target-(FilterLoad.site+offset phase+5))).
Proof. destruct phase;vm_compute;reflexivity. Qed.
Lemma ret:ScalarBytes.decode (skipn 0xadd DecoderFrame.code)=Some(1%nat,Ret).
Proof. vm_compute;reflexivity. Qed.
Definition constants s:=forall i j,(i<4)%nat -> vectors s j (28+i)%nat=DecoderFrame.constant i.
Record result phase bias e p q:Prop:=Result {
 pc:ip q=bias+FilterLoad.site+(offset phase+5); writes:accounted e (writable e) q; words:well_formed(machine q);
 registers:forall r,regs(machine q) r=regs(machine p) r;
 memory_after:preserved (fun x=>~(regs(machine p) 4%nat-8<=x<regs(machine p) 4%nat)) (mem(machine p)) (mem(machine q));
 reduced:forall i j,(i<5)%nat -> vectors(machine q) j i=Scale.reduced (vectors(machine p) j) i;
 kept:forall j r,(15<=r)%nat -> vectors(machine q) j r=vectors(machine p) j r
}.

Theorem checked phase bias e p : placement e -> loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+FilterLoad.site+offset phase -> accounted e (writable e) p -> well_formed(machine p) ->
 regs(machine p) 4%nat=StrictFilterCall.slot e-8 -> constants(machine p) ->
 exists q,execute bias p=Some q /\ result phase bias e p q.
Proof.
 intros P I PC Acc W SP C;set (o:=bias+FilterLoad.site);set (d:=bias+DecoderFrame.origin);set (calloff:=offset phase).
 set (disp:=target-(FilterLoad.site+calloff+5)).
 assert (T:o+(calloff+5)+disp=d+DecoderKernel.start DecoderKernel.Carry) by (unfold disp,o,d,target;change (DecoderKernel.start DecoderKernel.Carry) with 0xa7e;ring).
 assert (Body:contract e (writable e) (DecoderProduct.area e) (o+(calloff+5)+disp) (d+0xadd) 0
     (DecoderKernel.body DecoderKernel.Carry) (DecoderProduct.native bias DecoderKernel.Carry)).
 { rewrite T;exact (DecoderProduct.calc _ _ _ I DecoderKernel.Carry). }
 assert (Site:available e (writable e) o FilterLoad.text).
 { split;[apply (proj2(symbols _ _ _ _ I _ _ StrictFilterCall.in_filter))|intros x X;apply (immutable _ _ _ _ I);left;eexists;eexists;
   split;[exact StrictFilterCall.in_filter|exact X]]. }
 assert (R:word64(o+(calloff+5))).
 { destruct(proj1(symbols _ _ _ _ I _ _ StrictFilterCall.in_filter)) as [L H];change (0<=o) in L;change (o+551<=2^64) in H;
   assert (calloff=260 \/ calloff=478) by (destruct phase;[right|left];reflexivity);unfold word64;lia. }
 destruct (invoke e (writable e) (DecoderProduct.area e) o FilterLoad.text calloff disp d DecoderFrame.code 0xadd 0
    _ _ (DecoderProduct.stack e P) ltac:(lia) Site (DecoderProduct.placed _ _ _ I DecoderKernel.Carry)
    ltac:(unfold calloff,offset;lia) (call phase) ltac:(lia) ret
    ltac:(rewrite T;exact (DecoderProduct.address_fits _ _ _ I DecoderKernel.Carry 0xa7e ltac:(change (0<=0xa7e<2984);lia))) R Body p PC Acc
    ltac:(change (sp e-16384+(8+0)<=regs(machine p) 4%nat<=sp e);rewrite SP;unfold StrictFilterCall.slot,common_top,Rows.frame,sp;lia))
   as [q [Run [End Paid G M V]]].
 exists q;split;[exact Run|constructor];[exact End|exact Paid| |exact G|exact M| |].
 - exact (NativeWords.call _ _ _ _ _ (NativeWords.block _ _ _) p q W Run).
 - intros i j N;rewrite V;apply SetupValues.carry_lane;[reflexivity|exact (C 0%nat j ltac:(lia))|exact (C 1%nat j ltac:(lia))|exact N].
 - intros j r High;rewrite V;apply untouched,forallb_forall;intros op InCode.
   assert (Check:forallb (fun i=>(fst i<?15)%nat) (DecoderKernel.body DecoderKernel.Carry)=true) by (vm_compute;reflexivity).
   apply forallb_forall with (x:=op) in Check;[|exact InCode];apply Nat.ltb_lt in Check;apply Bool.negb_true_iff,Nat.eqb_neq;lia.
Qed.
