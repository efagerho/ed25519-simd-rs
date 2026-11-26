From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun abi.SysV.
From Machine Require abi.CallReturn execution.Composition.
From Ed25519Simd.Sha512Challenge Require Execution.
From Ed25519Simd.VerifyBatch Require NativeHash ScoreSetup ScoreStart Iteration Audit.
Local Open Scope Z_scope.

(* Expand the shared call rule at the production boundary. The scorer may see
   every well-formed assignment of the volatile GPRs, vectors and flags. The
   instruction pointer, RSP, saved GPRs, memory and full store trace are fixed. *)
Definition explicit_handoff pol bias pc text h r started : Prop :=
  exists s cf child,
    mem s = Execution.after r /\ regs s 4%nat = Execution.return_sp r /\
    (forall g, In g sysv_saved -> Execution.saved_register r g = Some (regs s g)) /\
    well_formed s /\
    ScoreSetup.execute (bias+pc) text
      (Cursor (Execution.return_ip r) s cf (log h ++ CallWrites.hash_events_at bias (machine h))) = Some child /\
    ScoreStart.from_call pol bias child = Some started.
Lemma same_scorer_runs pol bias pc text h r started :
  ScoreStart.from_hash pol bias pc text h r started <-> explicit_handoff pol bias pc text h r started.
Proof.
  split.
  - intros [[ip s cf trace] [[PC SP Saved Mem Log Words] [child [Setup Start]]]].
    cbn [LinkedRun.ip log] in PC,Log. subst ip trace.
    exists s,cf,child. exact (conj Mem (conj SP (conj Saved (conj Words (conj Setup Start))))).
  - intros [s [cf [child [Mem [SP [Saved [Words [Setup Start]]]]]]]].
    exists (Cursor (Execution.return_ip r) s cf (log h ++ CallWrites.hash_events_at bias (machine h))).
    split; [constructor; assumption || reflexivity|now exists child].
Qed.

(* Both callers must observe that same handoff before executing the scorer. *)
Example iteration_paths pol bias pc text h r last :
  Iteration.score pol bias pc text h r last <->
  exists started screen, explicit_handoff pol bias pc text h r started /\
    ScoreProgress.observed pol bias started screen /\ Iteration.publish pol bias pc text screen last.
Proof.
  split.
  - intros [started [Call [screen [Run End]]]]. exists started,screen.
    split; [apply same_scorer_runs,Call|auto].
  - intros [started [screen [Call [Run End]]]]. exists started.
    split; [apply same_scorer_runs,Call|now exists screen].
Qed.

Example public_scorer_paths pol bias pc text e cf masks stop :
  Audit.scoring pol bias pc text e cf masks stop <->
  exists h r started, FirstDispatch.run pol bias pc text e cf masks=Some (FirstDispatch.HashReturned h r) /\
    explicit_handoff pol bias pc text h r started /\ ScoreProgress.observed pol bias started stop.
Proof.
  split; intros [h [r [started [Run [Call Screen]]]]]; exists h,r,started.
  all: split; [exact Run|split; [now apply same_scorer_runs|exact Screen]].
Qed.
