From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.Instructions execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.MaskedResult execution.ScalarBytes memory.ByteMemory.
From Ed25519Simd.DalekPostHash Require Caller Keys.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require FilterLoad.
Import ListNotations. Local Open Scope Z_scope.

Definition fetch_column d c i:=[XnorWord 3 3 3;GatherQ d 3 20 (DalekPostHash.Caller.table_disp c i)].
Definition cell s j c i:=read_word (mem s) (word(vectors s j 20%nat+DalekPostHash.Caller.table_disp c i)).
Definition column second i:=let saved:=(15+i)%nat in let b:=if Nat.eqb i 0 then 30%nat else 31%nat in
 if second:bool then fetch_column 10 3 i++[AddQ i 0 saved saved;AddQ i 0 i b;Subtract i 0 i 10]
 else fetch_column saved 0 i++fetch_column i 1 i++[AddQ i 0 i b;Subtract i 0 i saved].
Definition block second:=flat_map (column second) (seq 0 5).
Definition offset second:=if second:bool then 313%nat else 50%nat.
Definition size second:=if second:bool then 165%nat else 210%nat.
Lemma image second:assemble (Z.of_nat(offset second)) (block second)=Some(firstn (size second) (skipn (offset second) FilterLoad.text)).
Proof. destruct second;vm_compute;reflexivity. Qed.

Lemma app_eval o xs : forall ys s k v b,evaluate o s k xs=Some(v,b) ->
 evaluate o s k (xs++ys)=evaluate o v b ys.
Proof.
 induction xs as [|op xs IH];intros ys s k v b R;[injection R as <- <-;reflexivity|].
 cbn [app evaluate] in *;destruct(MaskedResult.step o s k op) as [[u bank]|];[apply IH,R|discriminate].
Qed.

Lemma fetch o s k d c i : exists v b,evaluate o s k (fetch_column d c i)=Some(v,b) /\
 regs v=regs s /\ mem v=mem s /\ (forall j,(j<8)%nat -> vectors v j d=cell s j c i) /\
 forall r j,r<>d -> vectors v j r=vectors s j r.
Proof.
 do 2 eexists;split;[reflexivity|];split;[reflexivity|split;[reflexivity|split]].
 - intros j J;unfold merge,set_mask;cbn [ScalarBytes.vector_dest vectors];unfold put;rewrite !Nat.eqb_refl;cbn [Nat.eqb orb].
   rewrite (proj2(Nat.ltb_lt j 16) ltac:(lia)),Bool.eqb_reflx;reflexivity.
 - intros r j R;unfold merge;cbn [ScalarBytes.vector_dest vectors];unfold put;now rewrite (proj2(Nat.eqb_neq d r) ltac:(congruence)).
Qed.

Definition bias_reg i:=if Nat.eqb i 0 then 30%nat else 31%nat.
Definition minus_plus s j i:=Arithmetic.vpsubq (Arithmetic.vpaddq (cell s j 1 i) (vectors s j (bias_reg i))) (cell s j 0 i).
Lemma first o s k i : (i<5)%nat ->
 exists v b,evaluate o s k (column false i)=Some(v,b) /\ regs v=regs s /\ mem v=mem s /\
 (forall j,(j<8)%nat -> vectors v j i=minus_plus s j i /\ vectors v j (15+i)%nat=cell s j 0 i) /\
 forall r j,r<>i -> r<>(15+i)%nat -> vectors v j r=vectors s j r.
Proof.
 intro I;set (d:=(15+i)%nat);set (br:=bias_reg i).
 assert (Regs:i<>d /\ d<>20%nat /\ i<>20%nat /\ br<>i /\ br<>d) by (unfold br,bias_reg,d;destruct(Nat.eqb i 0);lia).
 destruct(fetch o s k d 0 i) as [a [ak [A [AG [AM [AV AX]]]]]].
 destruct(fetch o a ak i 1 i) as [b [bk [B [BG [BM [BV BX]]]]]].
 unfold column;fold (bias_reg i);fold d br;rewrite (app_eval _ _ _ _ _ _ _ A),(app_eval _ _ _ _ _ _ _ B).
 do 2 eexists;split;[reflexivity|split;[exact (eq_trans BG AG)|split;[exact (eq_trans BM AM)|split]]].
 - intros j J;unfold merge;cbn [ScalarBytes.vector_dest vectors Nat.eqb orb];unfold put.
   rewrite !Nat.eqb_refl;rewrite (proj2(Nat.eqb_neq i d) ltac:(lia)).
   rewrite (BV j J),(BX br j ltac:(lia)),(AX br j ltac:(lia)),(BX d j ltac:(lia)),(AV j J).
   unfold cell,minus_plus;rewrite AM,(AX 20%nat j ltac:(lia));split;reflexivity.
 - intros r j R D;unfold merge;cbn [ScalarBytes.vector_dest vectors];unfold put;rewrite !(proj2(Nat.eqb_neq i r) ltac:(congruence)).
   rewrite BX,AX;congruence.
Qed.

Definition twice_minus_z s j i:=
 let a:=vectors s j (15+i)%nat in Arithmetic.vpsubq (Arithmetic.vpaddq (Arithmetic.vpaddq a a) (vectors s j (bias_reg i))) (cell s j 3 i).
Lemma second o s k i : (i<5)%nat ->
 exists v b,evaluate o s k (column true i)=Some(v,b) /\ regs v=regs s /\ mem v=mem s /\
 (forall j,(j<8)%nat -> vectors v j i=twice_minus_z s j i) /\
 forall r j,r<>i -> r<>10%nat -> vectors v j r=vectors s j r.
Proof.
 intro I;set (d:=(15+i)%nat);set (br:=bias_reg i).
 assert (Regs:i<>d /\ d<>10%nat /\ i<>10%nat /\ br<>i /\ br<>10%nat) by (unfold br,bias_reg,d;destruct(Nat.eqb i 0);lia).
 destruct(fetch o s k 10 3 i) as [a [ak [A [AG [AM [AV AX]]]]]].
 unfold column;fold (bias_reg i);fold d br;rewrite (app_eval _ _ _ _ _ _ _ A).
 do 2 eexists;split;[reflexivity|split;[exact AG|split;[exact AM|split]]].
 - intros j J;unfold merge;cbn [ScalarBytes.vector_dest vectors Nat.eqb orb];unfold put;rewrite !Nat.eqb_refl.
   rewrite !(proj2(Nat.eqb_neq i 10) ltac:(lia)),(proj2(Nat.eqb_neq i br) ltac:(lia)).
   rewrite (AX d j ltac:(lia)),(AX br j ltac:(lia)),(AV j J);reflexivity.
 - intros r j R D;unfold merge;cbn [ScalarBytes.vector_dest vectors];unfold put;rewrite !(proj2(Nat.eqb_neq i r) ltac:(congruence)).
   apply AX,D.
Qed.

(* Registers 0..4 accumulate the difference. Registers 15..19 save the
   first table column until after the conditional comparison against 2Z. *)
Definition kept second start count r:=
 ((r<start \/ start+count<=r) /\ (if second:bool then r<>10 else r<15+start \/ 15+start+count<=r))%nat.
Definition differences second s j i:=if second:bool then twice_minus_z s j i else minus_plus s j i.
Lemma columns phase n : forall start o s k,(start+n<=5)%nat ->
 exists v b,evaluate o s k (flat_map (column phase) (seq start n))=Some(v,b) /\ mem v=mem s /\
 (forall i j,(start<=i<start+n)%nat -> (j<8)%nat -> vectors v j i=differences phase s j i /\
     (phase=false -> vectors v j (15+i)%nat=cell s j 0 i)) /\
 forall r j,kept phase start n r -> vectors v j r=vectors s j r.
Proof.
 induction n as [|n IH];intros i o s k Bound.
 - exists s,k;repeat split;try reflexivity;intros;lia.
 - assert (One:exists a ak,evaluate o s k (column phase i)=Some(a,ak) /\ mem a=mem s /\
       (forall j,(j<8)%nat -> vectors a j i=differences phase s j i /\ (phase=false -> vectors a j (15+i)%nat=cell s j 0 i)) /\
       forall r j,kept phase i 1 r -> vectors a j r=vectors s j r).
   { destruct phase.
     - destruct(second o s k i ltac:(lia)) as [a [b [R [_ [M [V X]]]]]];exists a,b;split;[exact R|split;[exact M|split]].
       + intros j J;split;[exact (V j J)|discriminate].
       + intros r j [Away Scratch];apply X;lia.
     - destruct(first o s k i ltac:(lia)) as [a [b [R [_ [M [V X]]]]]];exists a,b;split;[exact R|split;[exact M|split]].
       + intros j J;destruct(V j J);split;auto.
       + intros r j [Away Scratch];apply X;lia. }
   destruct One as [a [ak [A [M [V X]]]]];destruct(IH (S i) o a ak ltac:(lia)) as [t [b [B [TM [TV TX]]]]].
   exists t,b;cbn [seq flat_map];rewrite (app_eval _ _ _ _ _ _ _ A);split;[exact B|split;[congruence|split]].
   + intros l j Range J;destruct (Nat.eq_dec l i) as [->|Later].
     * destruct(V j J) as [L S];split;[rewrite TX;[exact L|unfold kept;destruct phase;lia]|].
       intros ->;rewrite TX;[apply S;reflexivity|unfold kept;lia].
     * destruct(TV l j ltac:(lia) J) as [L S];rewrite L;split.
       -- unfold differences,twice_minus_z,minus_plus,cell;rewrite M;unfold bias_reg;
          destruct phase,(Nat.eqb l 0);repeat rewrite X by (unfold kept;lia);reflexivity.
       -- intros ->;rewrite S by reflexivity;unfold cell;rewrite M,X by (unfold kept;lia);reflexivity.
   + intros r j R;rewrite TX;[apply X|];unfold kept in *;destruct phase;intuition lia.
Qed.

Record result phase bias e p q:Prop:=Result {
 pc:ip q=bias+FilterLoad.site+Z.of_nat(offset phase+size phase);
 state:unchanged e (writable e) p q;
 limbs:forall i j,(i<5)%nat -> (j<8)%nat ->
   vectors(machine q) j i=differences phase (machine p) j i /\
   (phase=false -> vectors(machine q) j (15+i)%nat=cell (machine p) j 0 i);
 prior:forall r j,kept phase 0 5 r -> vectors(machine q) j r=vectors(machine p) j r
}.
Definition execute phase bias:=MaskedResult.execute (bias+FilterLoad.site) (block phase).
Theorem checked phase bias e p ks : loaded Dalek bias (mem e) (writable e) ->
 ip p=bias+FilterLoad.site+Z.of_nat(offset phase) -> accounted e (writable e) p -> well_formed(machine p) ->
 exists q bank,execute phase bias p ks=Some(q,bank) /\ result phase bias e p q.
Proof.
 intros I PC Acc W;set (o:=bias+FilterLoad.site) in *.
 destruct(columns phase 5 0 o (machine p) ks ltac:(lia)) as [v [b [Run [_ [Data Other]]]]].
 destruct(mapped_now _ _ _ I _ _ _ Acc StrictFilterCall.in_filter) as [Map _].
 destruct(proj1(symbols _ _ _ _ I _ _ StrictFilterCall.in_filter)) as [L H].
 destruct(mapped_slice o FilterLoad.text e (writable e) p ks (offset phase) (size phase) (block phase) v b L H Map PC Acc W
  ltac:(change (List.length FilterLoad.text) with 551%nat;destruct phase;cbn [offset size];lia) (image phase) Run) as [q [Exec [End [CPU Same]]]].
 exists q,b;split;[exact Exec|constructor];[exact End|exact Same|intros i j N J;rewrite CPU;apply Data;lia|now rewrite CPU].
Qed.
