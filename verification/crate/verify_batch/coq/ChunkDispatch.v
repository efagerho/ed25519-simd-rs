From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.ScalarWords.
From Ed25519Simd.VerifyBatch Require Import Policy Image Return Audit Iteration.
From Ed25519Simd.VerifyBatch Require BatchWindow ChunkStaging ChunkScalar.
Local Open Scope Z_scope.
Section Iteration.
Context `{iteration:BatchWindow.t}.

Definition invalid pol e:=forall j,(j<8)%nat -> (j<BatchWindow.remaining e)%nat ->
 ~signature_accepts pol (read_input (mem e) (regs e 7%nat) (BatchWindow.first+j)).
Definition post pol bias pc e b:=match b with
 | FirstDispatch.Completed q=>RejectExecution.post_with (ScoredChunk.outputs pol e) (bias+pc) e (RejectExecution.BatchReturned q)
 | FirstDispatch.MoreChunks q=>RejectExecution.post_with (ScoredChunk.outputs pol e) (bias+pc) e (RejectExecution.NextChunk q)
 | FirstDispatch.HashReturned q r=>HashLayout.active pol e /\ NativeHash.returned pol bias (bias+pc) e q r /\
   ScoreInputs.inputs pol e (machine q) /\ well_formed(machine q) end.

Lemma zeros pol e m:invalid pol e -> RejectExecution.zero_results e m -> ScoredChunk.outputs pol e m.
Proof. intros Bad Z j J;exists false;split;[apply Z,J|split;[discriminate|intro Sig;exfalso;exact (Bad j ltac:(lia) ltac:(lia) Sig)]]. Qed.
Lemma rejected pol bias pc e r:invalid pol e -> RejectExecution.post (bias+pc) e r ->
 post pol bias pc e (FirstDispatch.after_reject r).
Proof. intros Bad Done;destruct r;unfold post;cbn [FirstDispatch.after_reject];eapply RejectExecution.post_map;[intros m;exact (zeros pol e m Bad)|exact Done|intros m;exact (zeros pol e m Bad)|exact Done]. Qed.

Theorem checked pol bias pc text e p masks:admissible pol bias pc text e -> StrictDispatch.bound pc text ->
 (0<BatchWindow.remaining e)%nat ->
 ChunkStaging.entry (bias+pc) (BatchScalar.first_symbol pol-pc) e BatchWindow.first (BatchWindow.remaining e) p ->
 exists b,dispatch pol bias pc text e p masks=Some b /\ post pol bias pc e b.
Proof.
 intros A Code N Stage;pose proof (BatchWindow.total e N) as Total.
 assert (Full:(0<Scatter.count e)%nat) by lia.
 destruct(batch_inputs _ _ _ _ _ A Full) as [P [[_ Slices] [[Range Sep] [Maps [Idx Entries]]]]].
 pose proof(callee_image _ _ _ _ _ A Full) as I;pose proof(decoder_aligned _ _ _ _ _ A Full) as Al.
 destruct(ChunkScalar.checked pol bias pc e p masks P I Stage) as [s [bank [Scalar Result]]].
 destruct Result as [PC [SP [Paid [Links [Outputs Data]]]]] eqn:Res.
 destruct(Data N ltac:(intros j J;exact (proj1(proj2(Slices j J))))) as [Digits [Copy [Meta Saved]]].
 pose proof (proj2(proj2(proj2(proj2(proj2(proj2 Copy)))))) as Layout.
 pose proof (ChunkScalar.valid_words _ _ _ _ _ _ (ChunkStaging.valid _ _ _ _ _ _ Stage) Scalar (proj1 Copy)) as W.
 assert (Exit:forall decoded v, EligibilityFrame.context pol bias (bias+pc) e v ->
   accounted e (writable e) v -> well_formed(machine v) -> regs(machine v) 4%nat=BatchScalar.common_top pol e-104 ->
   ip v=bias+PrepareNative.common+PrepareUnwind.unwind_offset decoded ->
   PrepareUnwind.return_value decoded (machine v) mod 2^32=0 ->
   exists r,RejectedPath.execute decoded pol bias pc text v=Some r /\ RejectExecution.post (bias+pc) e r).
 { intros dec v;apply (@RejectedPath.checked iteration);[exact(proj1(proj2 Code))|exact(proj1(proj2(proj2 Code)))|exact P|exact I|exact Range|
     exact(proj2(proj2(proj2 Code)))|exact(entry_text _ _ _ _ _ A)|exact Sep|exact N|exact Idx]. }
 unfold dispatch;rewrite Scalar;cbn [bind];unfold after_scalar;destruct(Z.eqb_spec (regs(machine s) 0%nat mod 2^32) 0) as [Z|Live].
 - destruct(Exit false s (EligibilityFrame.Context _ _ _ _ _ Links Outputs Meta Saved Layout) Paid W SP PC Z) as [r [End Done]].
   exists(FirstDispatch.after_reject r);split;[now rewrite End|apply rejected;[exact (ScalarInputs.zero_rejects _ _ _ Digits Z)|exact Done]].
 - assert (Inputs:BatchDecode.readable e).
   { intros j sig J;destruct(Slices _ (BatchWindow.live_row e j N)) as [Key [Sig _]].
     unfold ScalarInputs.encoding_ptr;destruct sig;[|exact Key]. destruct Sig as [[L H] Away];split;[unfold MemoryGeometry.fits64;lia|intros x X;apply Away;lia]. }
   destruct(BatchDecode.from_return pol bias pc e s P I Inputs Result Copy Live) as [d [To [Entry Handoff]]].
   rewrite To;cbn [bind];unfold after_decode.
   destruct(EligibleLanes.from_decoder _ _ _ s d bank P I Al Entry (segment_wf _ _ _ _ _ W To) Digits (BatchDecode.caller_args _ _ _ _ Handoff))
     as [t [Run Check]];rewrite Run;cbn [bind].
   pose proof (EligibilityFrame.restore _ _ _ _ _ _ _ P Result Handoff Meta Saved Layout Check) as Frame.
   destruct (Z.eqb_spec (regs(machine(EligibleLanes.stopped t)) 14%nat) 0) as [Zero|Yes].
   + destruct(Exit true (EligibleLanes.stopped t) Frame (EligibleLanes.writes _ _ _ _ _ (proj2 Check))
       (EligibleLanes.words _ _ _ _ _ (proj2 Check)) (EligibleLanes.stack _ _ _ _ _ (proj2 Check))
       ltac:(rewrite (EligibleLanes.destination _ _ _ _ _ (proj2 Check));unfold EligibleLanes.next;now rewrite Zero) eq_refl)
       as [r [End Done]].
     exists(FirstDispatch.after_reject r);split;[now rewrite End|apply rejected;[exact(EligibleLanes.zero_rejects _ _ _ _ _ (proj2 Check) Zero)|exact Done]].
   + assert (Enc:PreparedInputs.operands e (machine(EligibleLanes.stopped t))).
     { eapply PreparedInputs.from_decoder;[exact P|exact Digits|exact Handoff| |exact Check].
       destruct Entry as [_ [_ [_ [_ [_ [_ [_ Data0]]]]]]];exact Data0. }
     destruct(PreparedReturn.from_eligible _ _ _ _ _ _ (TableMask.masks t) P I Al (proj2 Check) Frame (PreparedTables.input _ _ _ _ _ P Check) Enc Yes)
        as [q [k [Prep Done]]].
     destruct(ReadyDispatch.checked pol bias pc text e q k (proj1 Code) P I Range (entry_text _ _ _ _ _ A) Sep Done)
        as [v [kv [Go [_ Child]]]];unfold ReadyDispatch.observe;rewrite Prep;cbn [bind];rewrite Go;cbn [bind fst snd].
     pose proof(proj1(EligibleLanes.live_branch _ _ _ _ _ (proj2 Check)) Yes) as Active.
     assert (Borrow:NativeHash.messages_immutable e).
     { intros j k0 J K;destruct(Slices _ (BatchWindow.live_row e j N)) as [_ [_ [_ B]]];apply B;unfold NativeHash.field in K|-*;lia. }
     specialize(Entries BatchWindow.first (BatchWindow.remaining e) Loop.zero_loc N Total Loop.zero_words).
     destruct pol.
     * destruct Active as [j [J On]];assert (LiveZip:HashLayout.active Zip215 e) by (exists j;split;[exact J|now apply HashLayout.candidate]).
       destruct(@NativeHash.checked iteration Zip215 _ _ _ _ _ P I N Entries Borrow LiveZip (HashLayout.zip_flags _ _ _ _ Done)
         (PreparedReturn.encodings _ _ _ _ _ Done) Child) as [r [H Ret]].
       eexists;split;[unfold FirstDispatch.continue,FirstDispatch.hash_return;now rewrite H|exact(conj LiveZip (conj Ret (conj (ScoreInputs.at_hash _ _ _ _ _ _ P (ScoreInputs.zip _ _ _ _ Done) Child) (HashEntry.words _ _ _ _ _ Child))))].
     * destruct(StrictReturn.from_entry _ _ _ _ _ kv P I Maps Done Child) as [out [k0 [Filter F]]].
       destruct(@StrictDispatch.checked iteration bias pc text e v out k0 Code P I Range (entry_text _ _ _ _ _ A) Sep N Idx F)
         as [exit [Path [_ Branch]]];cbn [FirstDispatch.continue];rewrite Filter;cbn [bind];rewrite Path.
       assert (Eq:StrictReturn.live e (machine v) <-> HashLayout.active Dalek e).
       { split;intros [j [J H]];exists j;split;[exact J|apply (proj1(StrictReturn.strong_lane _ _ _ _ F j J)),H|
             exact J|apply (proj2(StrictReturn.strong_lane _ _ _ _ F j J)),H]. }
       destruct exit as [r|h];cbn [FirstDispatch.after_filter bind] in *;destruct Branch as [Survives Ready].
       -- exists (FirstDispatch.after_reject r);split;[reflexivity|apply rejected;[|exact Ready]].
          intros j J Row Sig;apply Survives,Eq;exists j;split;[exact J|apply Lane.accepted_eligible;unfold HashLayout.row;now rewrite BatchWindow.own_row by exact Row].
       -- pose proof(proj1 Eq Survives) as ActiveD.
          destruct(@NativeHash.checked iteration Dalek _ _ _ _ _ P I N Entries Borrow ActiveD (HashLayout.strict_flags _ _ _ _ F)
            (StrictReturn.encodings _ _ _ _ F) Ready) as [r [H Ret]].
          eexists;split;[unfold FirstDispatch.hash_return;now rewrite H|exact(conj ActiveD (conj Ret (conj (ScoreInputs.at_hash _ _ _ _ _ _ P (ScoreInputs.dalek _ _ _ _ F) Ready) (HashEntry.words _ _ _ _ _ Ready))))].
Qed.
End Iteration.
