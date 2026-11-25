From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.MappedFetch execution.MaskTransfer memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require StrictRCompare StrictRClear.
Import ListNotations. Local Open Scope Z_scope.
Local Notation pc:=(ScoreSetup.callee Dalek).
Local Notation text:=(ScoreSetup.code Dalek).

Definition execute bias p ks:=bind (StrictRY.execute bias p) (fun y=>
 bind (StrictRCompare.execute bias y ks) (fun '(cmp,bank)=>bind (MaskTransfer.tick (ToEax 2) cmp bank)
 (fun '(r,k)=>option_map (fun t=>(t,k)) (StrictRClear.execute bias r)))).
Lemma kmov:MaskTransfer.encoding (ToEax 2)=firstn 4 (skipn 147 text).
Proof. vm_compute;reflexivity. Qed.
Definition eligible e j:=HashLayout.eligible Dalek e j /\ BatchDecode.original_encoding true e j mod 2^255<Field.prime.
Record result bias e p t:Prop:=Result {
 address:ip t=bias+pc+(if regs(machine t) 12%nat=?0 then 554 else 162);
 writes:accounted e (writable e) t; words:well_formed(machine t);
 memory:mem(machine t)=mem(machine p); history:log t=log p;
 unchanged_regs:forall g,g<>0%nat -> g<>12%nat -> regs(machine t) g=regs(machine p) g;
 mask_byte:0<=regs(machine t) 12%nat<256;
 lane:forall j,(j<8)%nat -> (Z.testbit (regs(machine t) 12%nat) (Z.of_nat j)=true <-> eligible e j);
 continues:regs(machine t) 12%nat<>0 <-> exists j,(j<8)%nat /\ eligible e j
}.

Local Opaque StrictRY.execute StrictRCompare.execute StrictRClear.execute MaskTransfer.tick
 HashLayout.eligible BatchDecode.original_encoding.

Lemma nonempty (eligible:nat->Prop) m : 0<=m<256 ->
 (forall j,(j<8)%nat -> (Z.testbit m (Z.of_nat j)=true <-> eligible j)) ->
 (m<>0 <-> exists j,(j<8)%nat /\ eligible j).
Proof.
 intros B Bits;rewrite (PrepareChunk.Dispatch.flag_nonzero _ B);split;intros [j [J V]];exists j;
 split;[exact J|exact (proj1(Bits j J) V)|exact J|exact (proj2(Bits j J) V)].
Qed.

Lemma filtered_bits live rejected final (enabled canonical:nat->Prop) :
 final=StrictRClear.clear live (mask16 rejected) ->
 (forall j,(j<8)%nat -> (Z.testbit live (Z.of_nat j)=true <-> enabled j)) ->
 (forall j,(j<8)%nat -> (rejected j=false <-> canonical j)) ->
 forall j,(j<8)%nat -> (Z.testbit final (Z.of_nat j)=true <-> enabled j /\ canonical j).
Proof.
 intros -> Bits Low j J;rewrite StrictRClear.bits,(proj2(kmov_value rejected) j ltac:(lia)) by exact J.
 split.
 - intros V;apply Bool.andb_true_iff in V as [On Under];apply Bool.negb_true_iff in Under.
   exact (conj (proj1(Bits j J) On) (proj1(Low j J) Under)).
 - intros [On Under];apply Bool.andb_true_iff;split;[exact (proj2(Bits j J) On)|].
   apply Bool.negb_true_iff;exact (proj2(Low j J) Under).
Qed.

Theorem checked bias parent e h r child score p ks : placement e -> loaded Dalek bias (mem e) (writable e) ->
 ScoreStart.reached Dalek bias parent e h r child score -> StrictRStart.reached bias e score p ->
 exists t bank,execute bias p ks=Some(t,bank) /\ result bias e p t.
Proof.
 intros P I S T;destruct(StrictRY.checked _ _ _ _ _ _ _ _ P I S T) as [y [Y Rows]].
 destruct(StrictRCompare.checked _ _ _ _ ks I Rows) as [q [k [Cmp Q]]].
 set (o:=bias+pc) in *;set (m:=mask16(k 2%nat));set (a:=Cursor (word(ip q+4)) (set (machine q) 0 m) (carry q) (log q)).
 pose proof(StrictRCompare.at_kmov _ _ _ _ _ Q) as PC;fold o in PC.
 destruct(mapped_now _ _ _ I _ _ _ (StrictRCompare.writes _ _ _ _ _ Q) (ScoreSetup.image Dalek)) as [Map _].
 assert (Read:mapped (mem(machine q)) (ip q) (MaskTransfer.encoding (ToEax 2))).
 { rewrite PC;apply subimage with (off:=147%nat) (text:=text);[exact Map|change (147+4<=584)%nat;lia|exact (eq_sym kmov)]. }
 assert (Move:MaskTransfer.tick (ToEax 2) q k=Some(a,k)) by exact (MaskTransfer.fetched (ToEax 2) q k eq_refl Read).
 destruct(proj1(symbols _ _ _ _ I _ _ (ScoreSetup.image Dalek))) as [L H];fold o in L,H;change (o+584<=2^64) in H.
 assert (At:ip a=o+151) by (change (word(ip q+4)=o+151);rewrite PC,word_fits by (unfold word64;lia);ring).
 assert (Regs:regs(machine q)=regs(machine p)) by (rewrite (StrictRCompare.machine_after _ _ _ _ _ Q);apply (StrictRY.registers _ _ _ _ Rows)).
 assert (Old:regs(machine a) 12%nat=regs(machine p) 12%nat) by (change (regs(machine q) 12%nat=regs(machine p) 12%nat);now rewrite Regs).
 assert (W:well_formed(machine a)).
 { apply set_wf;[rewrite (StrictRCompare.machine_after _ _ _ _ _ Q);apply (StrictRY.words _ _ _ _ Rows)|
   unfold m,word64;pose proof(proj1(kmov_value(k 2%nat)));lia]. }
 destruct(StrictRClear.checked false bias e a I At (StrictRCompare.writes _ _ _ _ _ Q) W) as [t [End Post]].
 destruct Post as [Dest [Paid [Wt [Mem [Log [Mask G]]]]]].
 assert (AX:regs(machine a) 0%nat=m) by reflexivity.
 assert (Bits:forall j,(j<8)%nat -> (Z.testbit (regs(machine t) 12%nat) (Z.of_nat j)=true <-> eligible e j)).
 { exact (filtered_bits (regs(machine p) 12%nat) (k 2%nat) (regs(machine t) 12%nat)
     (HashLayout.eligible Dalek e) (fun j=>BatchDecode.original_encoding true e j mod 2^255<Field.prime)
     (eq_trans Mask (f_equal2 StrictRClear.clear Old AX))
     (StrictRStart.eligible _ _ _ _ T) (StrictRCompare.noncanonical _ _ _ _ _ Q)). }
 assert (Byte:0<=regs(machine t) 12%nat<256) by (rewrite Mask,Old;apply StrictRClear.bounded,(StrictRStart.mask_byte _ _ _ _ T)).
 exists t,k;split;[unfold execute;rewrite Y;cbn [bind];rewrite Cmp;cbn [bind];rewrite Move;cbn [bind];rewrite End;reflexivity|constructor].
 - rewrite Mask;exact Dest.
 - exact Paid.
 - exact Wt.
 - rewrite Mem;change (mem(machine q)=mem(machine p));rewrite (StrictRCompare.machine_after _ _ _ _ _ Q);apply (StrictRY.memory _ _ _ _ Rows).
 - rewrite Log;change (log q=log p);rewrite (StrictRCompare.history _ _ _ _ _ Q);apply (StrictRY.history _ _ _ _ Rows).
 - intros g A B;rewrite G by assumption;change (put (regs(machine q)) 0 m g=regs(machine p) g).
   unfold put;rewrite Regs;destruct (Nat.eqb_spec 0 g);congruence.
 - exact Byte.
 - exact Bits.
 - exact (nonempty _ _ Byte Bits).
Qed.
