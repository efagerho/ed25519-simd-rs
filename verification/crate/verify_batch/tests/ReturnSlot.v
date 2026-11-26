(* Run this against the extracted ZIP entry whose first table-pointer spill
   was redirected to the caller's return slot. *)
From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.WordSemantics execution.LinkedCalls execution.ScalarBytes memory.WriteTrace memory.FlatMemory.
From Machine Require execution.MappedFetch.
From Ed25519Simd.VerifyBatch Require Import StageEntry ZipBytes Return EntryWrites Prologue.
Import ListNotations. Local Open Scope Z_scope.

Definition origin := 4096.
Definition slot := 32768.
Definition loaded a := if (origin<=?a)&&(a<?origin+Z.of_nat(length symbol_bytes)) then
 nth (Z.to_nat (a-origin)) symbol_bytes 0 else 0.
Definition entry := CPU (fun r=>match r with 4%nat=>slot | 6%nat=>1 | _=>0 end)
 (fun _ _=>0) None loaded.
Definition start := State (Running 0) entry None.
Definition next := MappedFetch.fetch origin (length symbol_bytes).
Definition hit w := (WriteTrace.pc w=?origin+40) && (WriteTrace.address w=?slot) && (WriteTrace.size w=?8)%nat.

(* The store writes eight zero bytes on top of eight zero bytes. Both the
   before/after comparison and the actual out-of-bounds instruction matter. *)
Example counterexample :
 match MappedFetch.run 14 next start with
 | Some(t,ws)=>existsb hit ws && forallb (fun k=>
    mem (cpu_state t) (slot+Z.of_nat k)=?mem entry (slot+Z.of_nat k)) (seq 0 8)
 | None=>false end=true.
Proof. vm_compute;reflexivity. Qed.

(* The bad store also occurs for every nonempty caller satisfying the real
   stack/scratch/output placement, independent of the return word or R8. *)
Theorem rejects_placed_call ip delta e :
 placement e -> (0<Scatter.count e)%nat -> MappedFetch.mapped (mem e) ip symbol_bytes ->
 (forall x,ip<=x<ip+Z.of_nat(length symbol_bytes) -> ~writable e x) ->
 ~StageEntry.physical ip symbol_bytes delta e.
Proof.
 intros P Live Map Apart Physical.
 destruct (Prologue.before_spills ip symbol_bytes e None ltac:(repeat constructor) P Live)
   as [[l s c] [head [Run [Safe [L [R _]]]]]].
 cbn [loc cpu_state] in L,R;subst l.
 apply Prologue.stack_writable in Safe.
 pose proof (MappedFetch.run_lift _ _ _ _ _ _ _ Run Safe Map Apart) as First.
 pose proof (steps_memory _ _ _ _ _ (MappedFetch.run_steps _ _ _ _ _ _ Run)) as Memory.
 change (mem s=WriteTrace.replay (mem e) head) in Memory.
 assert (Mapped:MappedFetch.mapped (mem s) ip symbol_bytes).
 { rewrite Memory;exact (MappedFetch.keep_image _ _ _ _ _ Map Apart Safe). }
 set (addr:=Address 4 None 1000).
 assert (AddressOf:effective s addr=sp e).
 { unfold addr;cbn [effective];rewrite R;unfold Rows.frame;fold (sp e).
   replace (sp e-1000+0+1000) with (sp e) by ring;apply word_fits,(initial_cpu _ P). }
 set (w:=qword (word (ip+40)) (effective s addr) (regs s 8%nat)).
 assert (Store:MappedFetch.run 1 (MappedFetch.fetch ip (length symbol_bytes))
    (State (Running 40) s c)=Some(State (Running 48) (with_words s (regs s) (commit (mem s) w)) c,[w])).
 { cbn [MappedFetch.run];unfold MappedFetch.fetch;cbn [cpu_state].
   rewrite (MappedFetch.snapshot_mapped _ _ _ Mapped).
   rewrite (fetch_at ip symbol_bytes 40 _ _ 8 (Store64 8 addr) ltac:(lia) ltac:(reflexivity));reflexivity. }
 pose proof (MappedFetch.run_append _ 13 _ _ _ First 1 _ _ Store) as Bad.
 destruct (Physical None) as [t [ws [_ [_ [_ [_ Prefix]]]]]].
 pose proof (Prefix _ _ _ Bad) as Bounds.
 apply Forall_app in Bounds as [_ Bounds];inversion Bounds as [|? ? Allowed];subst.
 assert (T:touches w (sp e)) by (change (effective s addr<=sp e<effective s addr+8);rewrite AddressOf;lia).
 specialize (Allowed _ T);destruct Allowed as [Stack|[Scratch|Out]].
 - unfold span in Stack;lia.
 - destruct (scratch_stack _ P);unfold span in Scratch;lia.
 - destruct (out_stack _ P);unfold span in Out;lia.
Qed.

(* This contradicts the memory field of the public theorem independently of
   the wrapper byte-equality field. *)
From Ed25519Simd.VerifyBatch Require Import Policy Audit.
Corollary rejects_master_on_live_call bias e :
 admissible Equations.Zip215 bias ZipBytes.address symbol_bytes e ->
 (0<Scatter.count e)%nat -> ~batch_contract Equations.Zip215 ZipBytes.address symbol_bytes.
Proof.
 intros Input Live Master;destruct (batch_inputs _ _ _ _ _ Input Live) as [P [_ [[_ Apart] _]]].
 apply (rejects_placed_call _ (destination Equations.Zip215 Image.Prepare-ZipBytes.address) _ P Live (entry_text _ _ _ _ _ Input) Apart).
 exact (machine_prepare_entry _ _ _ Master _ _ Input Live).
Qed.
