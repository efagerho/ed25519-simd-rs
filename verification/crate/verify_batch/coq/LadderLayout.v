From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun memory.ByteMemory.
From Ed25519Simd.FullLadder Require Import Operands.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require LadderTables.
Import ListNotations. Local Open Scope Z_scope.
Module F := Ed25519Simd.FullLadder.Audit.

(* Only these seven registers and memory occur in the two placement records.
   Volatile temporaries on entry are the ones produced by the caller. *)
Definition same_args s t:=mem s=mem t /\ forall r,In r [1;2;4;6;7;8;9]%nat -> regs s r=regs t r.
Local Ltac substitute_args H := repeat rewrite H by (cbv [In];intuition congruence).
Lemma stage_args s t pad n : same_args s t -> same_args (entry_for pad s n) (entry_for pad t n).
Proof.
 intros [M G];split;[exact M|];intros r R;unfold entry_for,set,set_regs;cbn [regs mem with_words];
 unfold Instructions.put;repeat match goal with |-context[if ?b then _ else _]=>destruct b end;
 try reflexivity;try apply G,R;substitute_args G;reflexivity.
Qed.
Lemma stage_layout pc len s t : same_args s t -> SA.placement pc len s -> SA.placement pc len t.
Proof.
 intros [M G] [O A C Ret SP Ptr Key Base Dg Pair Digits];constructor.
 all: unfold SA.source,SA.key_table,SA.digit,SA.digit_addr in *.
 all: try intros j J;try match goal with J:(_=_ \/ _=_) |- _ =>destruct J as [->| ->] end.
 all: try match goal with |-forall _ _,_ -> _ -> _ -> _=>intros j p [->| ->] J K end.
 all: rewrite <-?M;repeat rewrite <-G by (cbv [In];intuition congruence);auto.
 intros p [->| ->] K B;repeat rewrite <-G by (cbv [In];intuition congruence);apply Digits;auto.
Qed.
Lemma ladder_layout bias s t : same_args s t -> F.placement bias s -> F.placement bias t.
Proof.
 intros [M G] [A SF PF Arena Sources Code].
 assert (Ranges:F.external_ranges s=F.external_ranges t).
 { unfold F.external_ranges,SA.key_table;rewrite M;substitute_args G;reflexivity. }
 constructor;unfold F.base_of,F.pad_of in *;repeat rewrite <-G by (cbv [In];intuition congruence);
 try assumption;intros a n N;apply Sources;now rewrite Ranges.
Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Definition view pol bias e t:=Candidate.ladder_with (HashLayout.chunk pol e bias) (mem(machine t)).
Lemma same_view pol bias e p t : LadderEntry.entry pol bias e p t -> same_args (view pol bias e t) (machine t).
Proof.
 intro E;destruct(LadderEntry.arguments _ _ _ _ _ E) as [SP [DI [SI [DX [CX [R8 R9]]]]]];split;[reflexivity|].
 intros r [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];symmetry;try assumption;try exact SP;try exact DI;try exact SI;
 try exact DX;try exact CX;try exact R8;destruct pol;exact R9.
Qed.
Lemma signature_digits pol bias e p t j : LadderEntry.entry pol bias e p t -> (j<8)%nat ->
 let ds:=digit_list (machine t) 1 j in let s:=little_endian(s_bytes(HashLayout.row e j)) in
 Forall (fun d=> -8<=d<8) ds /\ (s<Curve25519.Scalar.L -> Radix.number 16 ds=s).
Proof.
 intros E J ds s;destruct(LadderEntry.arguments _ _ _ _ _ E) as [_ [_ [_ [_ [CX _]]]]].
 pose proof (PreparedInputs.scalar_digits _ _ (ScoreBuffers.operands _ _ (LadderEntry.operands _ _ _ _ _ E)) j J) as S.
 assert (D:ds=SignatureScalar.Audit.digits (machine t) (scratch e+512) j).
 { unfold ds,digit_list,digits,SignatureScalar.Audit.digits;now rewrite CX. }
 cbv zeta in S;change (ScalarInputs.original_scalar e (BatchWindow.row e j)) with s in S;rewrite <-D in S.
 destruct(Z.ltb_spec s Curve25519.Scalar.L);[tauto|rewrite S;split;[apply Forall_forall;intros v V;apply repeat_spec in V;lia|lia]].
Qed.

Theorem checked pol bias e p t : ProductRun.geometry (HashLayout.chunk pol e bias) ->
 LadderEntry.entry pol bias e p t ->
 F.placement bias (machine t) /\ valid_inputs (bias+FullLadder.LinkedBytes.stage_pc) (F.pad_of (machine t)) (machine t).
Proof.
 intros Geometry E;set (v:=view pol bias e t);pose proof(same_view _ _ _ _ _ E) as H;fold v in H.
 destruct H as [M G];pose proof(LadderEntry.words _ _ _ _ _ E) as W.
 assert (Digits:ProductRun.bounded_digits v).
 { intros r j k Which J K;assert (Range:Forall (fun x=> -8<=x<8) (digit_list (machine t) r j)).
   { destruct Which as [->| ->];[apply (proj1(signature_digits _ _ _ _ _ _ E J))|exact (proj1(LadderEntry.challenge _ _ _ _ _ E j J))]. }
   unfold digits;rewrite M,G by (destruct Which as [->| ->];cbv [In];tauto).
   apply (proj1(Forall_forall _ _) Range);apply in_map_iff;exists k;split;[reflexivity|apply in_seq;lia]. }
 assert (Keys:forall j,(j<8)%nat -> Candidate.possible (HashLayout.chunk pol e bias) (SA.key_table v j)).
 { intros j J;unfold SA.key_table;rewrite M,G by (cbv [In];auto 8).
   destruct(LadderEntry.arguments _ _ _ _ _ E) as [_ [_ [SI _]]];rewrite SI.
   destruct(ScoreBuffers.selected _ _ (LadderEntry.operands _ _ _ _ _ E) j J) as [Local Original].
   destruct(LadderTables.choice (BatchDecode.original_encoding false e j)) as [A|[Bad _]].
   - rewrite (Local (proj2(RootDecision.signed_encoding false e j) (ex_intro _ _ A)));right;exists j;split;[exact J|].
     change (scratch e+PrepareChunk.Caller.table_offset j=scratch e+3584+2720*Z.of_nat j).
     unfold PrepareChunk.Caller.table_offset,PrepareChunk.Caller.tables_offset,PrepareChunk.Caller.table_stride;ring.
   - rewrite (Original ltac:(intro D;destruct(proj1(RootDecision.signed_encoding false e j) D) as [P D'];exact (Bad _ D')));left;reflexivity. }
 destruct(ProductRun.ladder_layout _ Geometry (mem(machine t)) (proj2(proj2 W)) Keys Digits) as [Place [_ Stage]];fold v in Place,Stage.
 split;[eapply ladder_layout;[split;eassumption|exact Place]|split;[exact W|]].
 intros n N;assert (Pad:F.pad_of (machine t)=F.pad_of v) by (unfold F.pad_of;rewrite G by (cbv [In];tauto);reflexivity).
 rewrite Pad;eapply stage_layout;[apply stage_args;split;eassumption|exact (Stage n N)].
Qed.
End Iteration.
