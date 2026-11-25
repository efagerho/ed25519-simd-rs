From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.WordBounds execution.LinkedCalls execution.LinkedRun execution.ScalarBytes execution.ScalarWords
 execution.InstructionRoute execution.MappedFetch memory.ByteMemory memory.WriteTrace.
From Machine Require execution.PermutationBlock execution.PackedStores execution.VectorOutputs.
From Ed25519Simd.KeyTable Require Pack.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableMultiple TableFrame TableEntry TableIdentity.
Import ListNotations. Local Open Scope Z_scope.

Definition lower op:=match op with
 | Pack.Unpack hi d a b=>PackedStores.Rearrange(PermutationBlock.Unpack hi d a b)
 | Pack.Shuffle d a b imm=>PackedStores.Rearrange(PermutationBlock.Shuffle d a b imm)
 | Pack.Copy d a=>PackedStores.Move d a
 | Pack.Permute d i b=>PackedStores.Select d i b
 | Pack.MaskSub d a b=>PackedStores.MaskSub d 1 a b
 | Pack.Store pos off r=>PackedStores.Write(VectorOutputs.Out r (if pos then 13 else 14) (8*Z.of_nat off) VectorOutputs.Full)
 | Pack.Extract pos off r half=>PackedStores.Write(VectorOutputs.Out r (if pos then 13 else 14) (8*Z.of_nat off) (VectorOutputs.Half (Nat.odd half))) end.
Definition code first:=map lower (if first:bool then Pack.first else Pack.rest).
Definition start first:=(if first:bool then 1207 else 1323)%nat.
Definition finish first:=(if first:bool then 1314 else 1947)%nat.
Definition select:list line:=[(1314,3%nat,Compare32 3 1);(1317,6%nat,Branch Equal (1947-1323))].

Definition in_row v:=match v with
 | PackedStores.Write w=>let disp:=VectorOutputs.displacement w in
   ((VectorOutputs.base w=?13)%nat || (VectorOutputs.base w=?14)%nat) &&
   (0<=?disp) && (disp/2720<?8) && (disp mod 2720+Z.of_nat(VectorOutputs.size w)<=?160)
 | _=>true end.

Lemma image first:PackedStores.image TableFrame.text (start first) (code first) /\
 PackedStores.stop (start first) (code first)=finish first /\ forallb in_row (code first)=true.
Proof. destruct first;vm_compute;repeat split;reflexivity. Qed.
Lemma branch:linked TableFrame.text select.
Proof. repeat constructor;vm_compute;discriminate || reflexivity. Qed.
Lemma count first:PackedStores.count_stores (code first)=(if first:bool then 6 else 42)%nat.
Proof. destruct first;reflexivity. Qed.
Local Opaque code.

Definition row e digit pos key:= (if pos:bool then TableMultiple.pos e digit else TableMultiple.neg e digit)+2720*key.
Definition area e digit x:=exists pos key,0<=key<8 /\ row e digit pos key<=x<row e digit pos key+160.
Lemma in_table e digit x : 1<=digit<=8 -> area e digit x -> Return.span (TableEntry.tables e) 21760 x.
Proof. intros N [pos [key [K X]]];unfold area,row,TableMultiple.pos,TableMultiple.neg,TableIdentity.first,Return.span in *;destruct pos;lia. Qed.
Lemma ranges e digit pos key : placement e -> 1<=digit<=8 -> 0<=key<8 ->
 scratch e<=row e digit pos key /\ row e digit pos key+160<=scratch e+25344.
Proof. intros P N K;unfold row,TableMultiple.pos,TableMultiple.neg,TableIdentity.first,TableEntry.tables;destruct pos;lia. Qed.
Lemma safe pol e digit s v : placement e -> 1<=digit<=8 -> TableMultiple.pointers pol e digit s ->
 in_row v=true -> PackedStores.safe (area e digit) s v.
Proof.
 intros P N Ptr;destruct v as [| | | |w];try solve [intros;exact Logic.I].
 cbn [in_row PackedStores.safe];rewrite !Bool.andb_true_iff,Bool.orb_true_iff;intros [[[Reg L] H] Size] x.
 apply Z.leb_le in L,Size;apply Z.ltb_lt in H.
 set (d:=VectorOutputs.displacement w) in *;assert (K:0<=d/2720<8) by (split;[apply Z.div_pos;lia|exact H]).
 assert (D:=Z.div_mod d 2720 ltac:(lia));assert (R:=Z.mod_pos_bound d 2720 ltac:(lia)).
 destruct (scratch_ok _ P) as [[Low High] _].
 destruct Reg as [G|G];apply Nat.eqb_eq in G;unfold VectorOutputs.address;rewrite G.
 - rewrite (TableMultiple.positive _ _ _ _ Ptr);pose proof(ranges e digit true (d/2720) P N K) as B.
   unfold row in B;cbn beta iota in B;fold d;rewrite word_fits by (unfold word64;destruct w as [? ? ? [|]];cbn [VectorOutputs.size VectorOutputs.piece] in Size;lia).
   intro X;exists true,(d/2720);unfold row;split;[exact K|lia].
 - rewrite (TableMultiple.negative _ _ _ _ Ptr);pose proof(ranges e digit false (d/2720) P N K) as B.
   unfold row in B;cbn beta iota in B;fold d;rewrite word_fits by (unfold word64;destruct w as [? ? ? [|]];cbn [VectorOutputs.size VectorOutputs.piece] in Size;lia).
   intro X;exists false,(d/2720);unfold row;split;[exact K|lia].
Qed.
Definition run bias first:=PackedStores.execute (TableFrame.base bias) TableFrame.text (code first).
Record block first pol bias e digit p q ks:Prop:=Block {
 address:ip q=TableFrame.base bias+Z.of_nat(finish first);
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 registers:regs(machine q)=regs(machine p);
 arguments:TableMultiple.pointers pol e digit (machine q);
 footprint:exists ws,log q=log p++ws /\ confined (area e digit) ws /\
   length ws=(if first then 6 else 42)%nat /\ mem(machine q)=replay (mem(machine p)) ws;
 exact_bytes:let '(s,ws):=PackedStores.simulate (TableFrame.base bias) (start first) (code first) (machine p) ks in
  machine q=s /\ log q=log p++ws
}.
Lemma checked first pol bias e digit p ks : placement e -> loaded pol bias (mem e) (writable e) -> 1<=digit<=8 ->
 ip p=TableFrame.base bias+Z.of_nat(start first) -> accounted e (writable e) p -> well_formed(machine p) ->
 TableMultiple.pointers pol e digit (machine p) ->
 exists q,run bias first p ks=Some(q,ks) /\ block first pol bias e digit p q ks.
Proof.
 intros P I N PC Acc W Ptr;destruct (image first) as [Code [End Bounds]];set (o:=TableFrame.base bias) in *.
 destruct(symbols _ _ _ _ I _ _ (TableEntry.image pol)) as [Fit Map].
 destruct(mapped_now _ _ _ I _ _ _ Acc (TableEntry.image pol)) as [_ Sep].
 assert (B:(PackedStores.stop (start first) (code first)<length TableFrame.text)%nat)
   by (rewrite End;destruct first;vm_compute;lia).
 assert (Area:Forall (PackedStores.safe (area e digit) (machine p)) (code first)).
 { apply Forall_forall;intros v V;apply (safe pol);[exact P|exact N|exact Ptr|now apply forallb_forall with (x:=v) in Bounds]. }
 assert (Stores:Forall (PackedStores.safe (writable e) (machine p)) (code first)).
 { eapply Forall_impl;[|exact Area];intros v A;destruct v;try exact Logic.I.
   intros x X;destruct(A x X) as [pos [key [K Range]]];pose proof(ranges e digit pos key P N K).
   right;left;unfold Return.span;lia. }
 destruct(PackedStores.checked o _ _ _ p ks _ _ Code B Fit PC Acc Map Sep W Stores) as [q [Run [At [Paid [Q [G Data]]]]]].
 exists q;split;[exact Run|constructor;try assumption].
 - now rewrite <-End.
 - destruct Ptr;constructor;rewrite G;assumption.
 - destruct(PackedStores.simulate o (start first) (code first) (machine p) ks) as [s ws] eqn:Eval.
   destruct Data as [S Log];destruct(PackedStores.trace_effects _ _ _ _ _ _ _ _ Area Eval) as [F [Len M]].
   exists ws;rewrite S,<-count;auto.
Qed.
