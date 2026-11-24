From Coq Require Import List ZArith.
From Machine Require Import execution.LinkedCalls execution.WordBounds memory.FlatMemory memory.ByteMemory memory.MemoryGeometry abi.SysV.
From Ed25519Simd.PrepareChunk Require Audit CommonBytes StrictBytes.
From Ed25519Simd.Sha512Challenge Require Audit ObjectBytes LiteralBytes.
From Ed25519Simd.Zip215 Require Audit DecodedBytes ScatterBytes.
From Ed25519Simd.DalekPostHash Require Audit DecodedBytes ScatterBytes.
From Ed25519Simd.VerifyBatch Require Import Policy Arguments Image Control Tables Scatter Loop Return.
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
     indices e /\ entries e pol bias
}.

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

Record batch_contract pol pc text : Prop := {
 linked : matches pc (destination pol) text;
 call_setup : Arguments.call_arguments;
 static_tables : Tables.verified;
 linked_callees : callees pol;
 verify : forall bias e, admissible pol bias pc text e ->
   (exists ip final,execution pol bias pc text (bias+pc) e ip final) /\
   (forall ip final,execution pol bias pc text (bias+pc) e ip final -> returned pol e ip final)
}.
