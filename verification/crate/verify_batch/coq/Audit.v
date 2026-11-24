From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.FlatMemory memory.ByteMemory memory.MemoryGeometry abi.SysV.
From Machine Require execution.MappedFetch execution.ScalarBytes execution.LinkedRun memory.WriteTrace.
From Ed25519Simd.PrepareChunk Require Audit CommonBytes StrictBytes.
From Ed25519Simd.Sha512Challenge Require Audit ObjectBytes LiteralBytes.
From Ed25519Simd.Zip215 Require Audit DecodedBytes ScatterBytes.
From Ed25519Simd.DalekPostHash Require Audit DecodedBytes ScatterBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Arguments Image Control Tables Scatter Loop Return LoadedImage EntryWrites CallWrites NestedRegions StageEntry RejectCall BatchScalar PrepareUnwind RejectDispatch RejectFinish RejectExecution.
From Ed25519Simd.VerifyBatch Require BatchDecode KeySquare.
Local Open Scope Z_scope.

Definition destination pol t := match t with
 | Prepare => match pol with Zip215=>PrepareChunk.CommonBytes.address | Dalek=>PrepareChunk.StrictBytes.address end
 | Hash => Sha512Challenge.ObjectBytes.address
 | Score => match pol with Zip215=>Zip215.DecodedBytes.address | Dalek=>DalekPostHash.DecodedBytes.address end
 | Scatter => Zip215.ScatterBytes.address end.

Definition callees pol := PrepareChunk.Audit.prepare_chunk_contract /\
 Sha512Challenge.Audit.sha512_contract Sha512Challenge.ObjectBytes.address Sha512Challenge.ObjectBytes.symbol_bytes
   Sha512Challenge.LiteralBytes.address Sha512Challenge.LiteralBytes.symbol_bytes /\
 match pol with
 | Zip215=>Zip215.Audit.zip215_contract
 | Dalek=>DalekPostHash.Audit.dalek_post_hash_contract /\
   DalekPostHash.ScatterBytes.address=Zip215.ScatterBytes.address /\
   DalekPostHash.ScatterBytes.symbol_bytes=Zip215.ScatterBytes.symbol_bytes end.

(* The arguments are the actual SysV entry registers. For nonempty batches
   the caller supplies immutable input slices and tables, writable output and
   scratch, and the per-call spatial/literal preconditions of the callees. *)
Definition separate_input e a n := fits64 a n /\ forall x, a<=x<a+n -> ~writable e x.
Definition borrowed e :=
 let row:=descriptor (mem e) (regs e 7%nat) in
 separate_input e (regs e 7%nat) (40*Z.of_nat(count e)) /\
 forall i,(i<count e)%nat -> separate_input e (row i 0) 32 /\
   separate_input e (row i 8) 64 /\ separate_input e (row i 16) (row i 24).
Record admissible pol bias pc (text:list Z) e := {
 entry_range : fits64 (bias+pc) (Z.of_nat (length text));
 entry_text : forall i,(i<length text)%nat -> mem e (bias+pc+Z.of_nat i)=nth i text 0;
 cpu_words : well_formed e;
 caller_sp : word64 (sp e+8);
 batch_inputs : (0<count e)%nat -> Return.placement e /\ borrowed e /\
     separate_input e (bias+pc) (Z.of_nat(length text)) /\ Tables.mapped e bias /\
     indices e /\ entries e pol bias;
 callee_image : (0<count e)%nat -> LoadedImage.loaded pol bias (mem e) (Return.writable e)
}.

(* SHA's aligned read-only segment fixes the load bias modulo 64 for every
   linked symbol. Reuse that loader fact at aligned RIP-relative operands. *)
Lemma decoder_aligned pol bias pc text e : admissible pol bias pc text e -> (0<count e)%nat ->
 (bias+DecoderFrame.origin) mod 64=0.
Proof.
 intros A N;destruct(batch_inputs _ _ _ _ _ A N) as [_ [_ [_ [_ [_ Entries]]]]].
 destruct (Entries 0%nat (count e) zero_loc N eq_refl zero_words) as [_ [_ [[Hash _] _]]].
 destruct(Sha512Challenge.Frame.image_fits _ _ _ _ Hash) as [_ [_ Al]].
 change ((bias+Sha512Challenge.LiteralBytes.address) mod 64=0) in Al.
 rewrite Z.add_mod in Al by lia;change (Sha512Challenge.LiteralBytes.address mod 64) with 0 in Al.
 rewrite Z.add_0_r,Z.mod_mod in Al by lia;rewrite Z.add_mod,Al by lia;reflexivity.
Qed.

(* Grouped execution. Each nonempty trace supplies the actual callee results
   for its live buffers. Other private bytes may take any byte value. *)
Inductive execution pol bias pc text : Z -> cpu -> Z -> cpu -> Prop :=
 | empty_path e ip final :
   matches pc (destination pol) text ->
   initial (count e)=Some Empty ->
   empty_return e=(ip,final) ->
   execution pol bias pc text (bias+pc) e ip final
 | batch_path e ip final out stack_bytes scratch_bytes noise :
   matches pc (destination pol) text ->
   initial (count e)=Some Prologue -> branch Prologue false false=Some Choose ->
   batches e pol bias 0 (count e) (fun i=>mem e (output e+Z.of_nat i)) out ->
   byte_memory stack_bytes -> byte_memory scratch_bytes -> well_formed noise ->
   Return.resume e (fill e stack_bytes scratch_bytes out) noise=(ip,final) ->
   execution pol bias pc text (bias+pc) e ip final.

Definition returned pol e ip final :=
 ip=read_word (mem e) (sp e) /\ regs final 0%nat=1 /\ regs final 4%nat=sp e+8 /\
 (forall r,In r sysv_saved -> regs final r=regs e r) /\
 preserved (fun x=>~writable e x) (mem e) (mem final) /\ byte_memory (mem final) /\
 (forall j,(j<count e)%nat -> let b:=mem final (output e+Z.of_nat j) in b=0 \/ b=1) /\
 forall i,(i<count e)%nat -> exists v:bool,
   mem final (output e+Z.of_nat (position e i))=Z.b2z v /\
   (v=true <-> signature_accepts pol (read_input (mem e) (regs e 7%nat) i)).

Definition first_chunk pol bias pc text e carry masks :=
 exists stop, BatchScalar.observe pol bias (bias+pc) text e carry masks=Some stop /\
                BatchScalar.post pol bias (bias+pc) e stop /\
                ScalarInputs.recoded e (LinkedRun.machine stop) /\
                (regs (LinkedRun.machine stop) 0%nat mod 2^32<>0 ->
                 exists decoder, BatchDecode.observe pol bias pc text e carry masks=Some decoder /\
                                 BatchDecode.entry pol bias e decoder /\
                                 forall incoming,exists q updated,KeySquare.from_key bias decoder incoming=Some(q,updated) /\
                                   KeySquare.squared pol bias e q) /\
                (regs (LinkedRun.machine stop) 0%nat mod 2^32=0 ->
                 (forall j,(j<8)%nat -> (j<count e)%nat -> ~signature_accepts pol (read_input (mem e) (regs e 7%nat) j)) /\
                 exists r, RejectExecution.scalar_rejection pol bias pc text e carry masks=Some r /\
                           RejectExecution.post (bias+pc) e r).

(* A single rejected chunk reaches the outer RET on the same store log. *)
Inductive observation pol bias pc text e carry masks : list WriteTrace.store -> Z -> cpu -> Prop :=
 | observe_empty ws ip final : count e=0%nat ->
   MappedFetch.steps (bias+pc) (length text) (ScalarBytes.State (ScalarBytes.Running 0) e carry) ws
     (ScalarBytes.State (ScalarBytes.Returned ip) final (Some false)) ->
   observation pol bias pc text e carry masks ws ip final
 | observe_rejected stop q : (0<count e<=8)%nat ->
   BatchScalar.observe pol bias (bias+pc) text e carry masks=Some stop ->
   regs(LinkedRun.machine stop) 0%nat mod 2^32=0 ->
   RejectExecution.scalar_rejection pol bias pc text e carry masks=Some(RejectExecution.BatchReturned q) ->
   observation pol bias pc text e carry masks (LinkedRun.log q) (LinkedRun.ip q) (LinkedRun.machine q)
 | observe_batch stop ip final : (0<count e)%nat ->
   ((8<count e)%nat \/ regs(LinkedRun.machine stop) 0%nat mod 2^32<>0) ->
   BatchScalar.observe pol bias (bias+pc) text e carry masks=Some stop ->
   execution pol bias pc text (bias+pc) e ip final ->
   observation pol bias pc text e carry masks (LinkedRun.log stop) ip final.

Definition immutable_after pol bias pc text e ip final :=
 (0<count e)%nat -> execution pol bias pc text (bias+pc) e ip final ->
 forall x, LoadedImage.readonly pol bias x -> mem final x=mem e x.

(* Scatter after an earlier confined prefix. Fetch sees the memory produced
   by that prefix, including the case where stack, scratch or output changed. *)
Definition physical_scatter pol bias e := forall prior s carry ws last,
 WriteTrace.confined (Return.writable e) prior -> mem s=WriteTrace.replay (mem e) prior ->
 regs s 6%nat=output e -> regs s 2%nat=Z.of_nat (count e) ->
 MappedFetch.steps (bias+Zip215.ScatterBytes.address) (length Zip215.ScatterBytes.symbol_bytes)
   (ScalarBytes.State (ScalarBytes.Running 0) s carry) ws last ->
 WriteTrace.confined (nested_writable e) ws /\
   LoadedImage.loaded pol bias (mem (ScalarBytes.cpu_state last)) (Return.writable e).

Record batch_contract pol pc text : Prop := {
 linked : matches pc (destination pol) text;
 call_setup : Arguments.call_arguments;
 static_tables : Tables.verified;
 linked_callees : callees pol;
 nested_regions : CallWrites.footprint /\ NestedRegions.footprint /\
   forall e,Return.placement e -> forall x,sp e-40<=x<sp e+8 -> ~nested_writable e x;
 verify : forall bias e carry masks, admissible pol bias pc text e ->
   (exists ws ip final, observation pol bias pc text e carry masks ws ip final) /\
   (forall ws ip final, observation pol bias pc text e carry masks ws ip final ->
      returned pol e ip final /\ WriteTrace.confined (writable e) ws);
 image_preserved : forall bias e, admissible pol bias pc text e ->
   (forall ip final,immutable_after pol bias pc text e ip final) /\
   ((0<count e)%nat -> physical_scatter pol bias e /\ RejectCall.contract bias pc text e);
 machine_prepare_entry : forall bias e, admissible pol bias pc text e -> (0<count e)%nat ->
   StageEntry.physical (bias+pc) text (destination pol Prepare-pc) e;
 machine_scalar_return : forall bias e carry masks, admissible pol bias pc text e -> (0<count e)%nat ->
   first_chunk pol bias pc text e carry masks;
 machine_empty : forall bias e, admissible pol bias pc text e -> count e=0%nat ->
   let '(ip,final):=empty_return e in
   returned pol e ip final /\ empty_mapped (bias+pc) text e
}.

Theorem single_rejected_return pol pc text : batch_contract pol pc text ->
 forall bias e c masks,admissible pol bias pc text e -> (0<count e<=8)%nat -> ScalarInputs.noncanonical_chunk e ->
 exists q,RejectExecution.scalar_rejection pol bias pc text e c masks=Some(RejectExecution.BatchReturned q) /\
 returned pol e (LinkedRun.ip q) (LinkedRun.machine q) /\ LinkedRun.accounted e (writable e) q /\
 forall i,(i<count e)%nat -> mem(LinkedRun.machine q)(output e+Z.of_nat(position e i))=0 /\
 ~signature_accepts pol (read_input (mem e) (regs e 7%nat) i).
Proof.
 intros Checked bias e c masks A [Live Size] Bad.
 destruct(machine_scalar_return _ _ _ Checked _ _ c masks A Live) as [s [Run [_ [Digits [_ Reject]]]]].
 pose proof(proj2 (ScalarInputs.zero_iff _ _ Live Digits) Bad) as Zero.
 destruct(Reject Zero) as [Invalid [[q|q] [End [Paid [[Status Outputs] [Bytes Exit]]]]]].
 2:{ destruct Exit as [More _];lia. }
 exists q;split;[exact End|split].
 - exact (proj1 (proj2 (verify _ _ _ Checked _ _ c masks A) _ _ _
     (observe_rejected _ _ _ _ _ _ _ _ _ (conj Live Size) Run Zero End))).
 - split;[exact Paid|intros i I;split;[apply Outputs;lia|apply Invalid;lia]].
Qed.
