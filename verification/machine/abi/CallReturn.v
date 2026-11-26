From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds
  execution.Composition memory.FlatMemory memory.ByteMemory memory.WriteTrace.
Local Open Scope Z_scope.

(* A callee can report only the machine components its ABI specifies.
   The register list excludes RSP, which has its own return condition. *)
Record observation := Observe {
  return_ip : Z; return_sp : Z; register : nat -> option Z; after : bytes
}.

(* The cursor at callee entry already contains the CALL push. Each admissible
   continuation carries the observed PC and memory and the exact new stores.
   Its volatile registers, vector lanes and flags can take any valid values. *)
Record resumes kept prior own r (next : cursor) : Prop := Resumes {
  pc_seen : ip next = return_ip r;
  stack_seen : regs (machine next) 4%nat = return_sp r;
  saved_seen : forall g, In g kept -> register r g = Some (regs (machine next) g);
  memory_seen : mem (machine next) = after r;
  trace_seen : log next = log prior ++ own;
  valid_cpu : well_formed (machine next)
}.

(* The callee certificate supplies replay from its own entry memory. The
   caller supplies the preceding trace and the continuation it expects. *)
Record certificate kept entry allowed prior own r back top : Prop := Certificate {
  target : return_ip r = back;
  stack : return_sp r = top;
  saved : forall g, In g kept -> register r g = Some (regs (machine prior) g);
  stack_fits : word64 top;
  bytes_valid : byte_memory (after r);
  prefix_paid : accounted entry allowed prior;
  writes_confined : confined allowed own;
  writes_replay : forall x, after r x = replay (mem (machine prior)) own x
}.

Record ready kept entry allowed prior own r back top next : Prop := Ready {
  at_return : ip next = back;
  caller_stack : regs (machine next) 4%nat = top;
  caller_registers : forall g, In g kept -> regs (machine next) g = regs (machine prior) g;
  memory_returned : mem (machine next) = after r;
  extended_trace : log next = log prior ++ own;
  words : well_formed (machine next);
  paid : accounted entry allowed next
}.

Theorem checked kept entry allowed prior own r back top :
  ~ In 4%nat kept -> well_formed (machine prior) ->
  certificate kept entry allowed prior own r back top ->
  ensures (resumes kept prior own r) (ready kept entry allowed prior own r back top).
Proof.
  intros Apart [Gprs [Vectors _]] [Back SP Saved Fit Bytes Prefix Safe Replay]. split.
  - (* One witness suffices for progress. Soundness below covers all completions. *)
    set (s := CPU (fun g => if Nat.eqb g 4 then top else regs (machine prior) g)
                  (vectors (machine prior)) (flag (machine prior)) (after r)).
    exists (Cursor (return_ip r) s (carry prior) (log prior ++ own)). constructor; try reflexivity.
    + exact (eq_sym SP).
    + intros g InG. cbn [machine s regs].
      destruct (Nat.eqb_spec g 4); [subst; contradiction|exact (Saved g InG)].
    + split; [intro g; cbn [machine s regs]; destruct (Nat.eqb g 4); auto|exact (conj Vectors Bytes)].
  - intros [pc s c trace] [Seen Stack Reg Mem Log W]. constructor.
    + exact (eq_trans Seen Back).
    + exact (eq_trans Stack SP).
    + intros g InG. specialize (Reg g InG). rewrite (Saved g InG) in Reg. now injection Reg.
    + exact Mem.
    + exact Log.
    + exact W.
    + cbn [log] in Log. subst trace. apply append_accounted with (p:=prior); auto.
      intro x. cbn [machine] in Mem. now rewrite Mem.
Qed.

Arguments checked {kept entry allowed prior own r back top} _ _ _.
