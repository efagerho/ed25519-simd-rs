From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.WordBounds
 execution.MappedFetch execution.InstructionRoute memory.ByteMemory memory.FlatMemory memory.MemoryGeometry abi.SysV.
From Machine Require execution.StoreHistory.
From Ed25519Simd.KeyTable Require Import CallLayout.
From Ed25519Simd.KeyTable Require NativeEntry NativeReturn NativeTable TableContents.
From Ed25519Simd.Decode Require DecoderBytes.
Import ListNotations. Local Open Scope Z_scope.

Definition buffers p:=let s:=machine p in
 let sp:=regs s 4%nat in let pt:=regs s 7%nat in let dst:=regs s 6%nat in
 Layout sp pt dst (footprint sp pt dst).

Definition execute bias p ks:=let e:=buffers p in
 let base:=CallLayout.base bias in
 bind (NativeEntry.execute base text (StoreHistory.fresh p)) (fun init=>
 bind (TableRounds.observe bias e init ks) (fun '(last,k)=>
 option_map (fun q=>(StoreHistory.rejoin p q,k)) (NativeReturn.execute base text last))).

Record result p q : Prop:=Result {
 return_pc:ip q=read_word (mem(machine p)) (sp (buffers p));
 words:well_formed(machine q);
 return_sp:regs(machine q) 4%nat=word(sp (buffers p)+8);
 saved_registers:forall r,In r sysv_saved -> regs(machine q) r=regs(machine p) r;
 stores:StoreHistory.extends (private (buffers p)) p q;
 parent:let e:=buffers p in preserved (Frame.keep (sp e) (point_ptr e) (table_ptr e))
    (Frame.saved (sp e) p) (mem(machine q));
 table:let e:=buffers p in NativeTable.contents (table_ptr e)
    (buffer_words (mem(machine p)) (point_ptr e)) (mem(machine q))
}.

Definition contract pc raw decoder ds helper hs cached cs:=forall bias p ks,
 let e:=buffers p in
 ip p=bias+pc -> regs(machine p) 2%nat=8 -> well_formed(machine p) ->
 Frame.placement [] 8 (sp e) (point_ptr e) (table_ptr e) ->
 (bias+decoder) mod 64=0 ->
 loaded_images [(pc,raw);(decoder,ds);(helper,hs);(cached,cs)] (machine p) bias e ->
 exists q bank,execute bias p ks=Some(q,bank) /\ result p q.

Lemma local_placement p : let e:=buffers p in
 Frame.placement [] 8 (sp e) (point_ptr e) (table_ptr e) -> placement e.
Proof.
 intros e [SA [PA [_ [Stack [Point [Table [PT [SP [ST _]]]]]]]]].
 constructor;try assumption;try exact (fun x X=>X).
 - unfold disjoint in *;tauto.
 - unfold disjoint in *;tauto.
Qed.

Theorem checked : NativeEntry.image CallLayout.text -> linked CallLayout.text NativeReturn.path ->
 contract KeyTable.ObjectBytes.address KeyTable.ObjectBytes.symbol_bytes DecoderBytes.address DecoderBytes.symbol_bytes
 HelperBytes.address HelperBytes.symbol_bytes KeyTable.CachedBytes.address KeyTable.CachedBytes.symbol_bytes.
Proof.
 intros Entry Return bias p ks e At Eight W Place Align Image.
 pose proof(local_placement p Place) as P;fold e in P.
 set (a:=StoreHistory.fresh p);set (o:=CallLayout.base bias).
 pose proof(proj2(symbols _ _ _ Image _ _ builder_in)) as Map.
 assert (Valid:CursorSegment.valid_cursor (machine p) (writable e) a) by (split;[apply initial_accounted|exact W]).
 destruct (NativeEntry.checked (machine p) (writable e) o text (sp e) (point_ptr e) (table_ptr e) a
   Entry Map Valid At ltac:(destruct(stack_fit _ P);lia)
   ltac:(destruct(table_fit _ P);unfold word64;lia)
   ltac:(intros x X;apply (permits _ P);left;unfold NativeEntry.save_area,span in *;lia)
   eq_refl eq_refl eq_refl Eight) as [init [Start Init]].
 destruct(TableContents.checked (machine p) bias e a init ks P Image Align Init)
   as [last [k [Rounds [[PC Paid F Ptr] [Kept Rows]]]]].
 destruct (NativeReturn.checked (machine p) (writable e) o text (sp e) (point_ptr e) (table_ptr e) a last
    Return Map (conj Paid F) PC (TableMultiple.multiple _ _ _ Ptr) (TableMultiple.frame_pointer _ _ _ Ptr)
    ltac:(destruct(stack_fit _ P);lia) ltac:(destruct(stack_fit _ P);lia) W
    ltac:(intros x X;pose proof(CallLayout.depth e P);pose proof(CallLayout.point_stack _ P);pose proof(table_stack _ P);
      unfold Frame.keep,CallLayout.stage,disjoint in *;intuition lia) Kept)
   as [t [Finish [Ret [[History WF] [SP [Regs Mem]]]]]].
 exists (StoreHistory.rejoin p t),k;split.
 - unfold execute;fold e o a;rewrite Start;cbn [bind];rewrite Rounds;cbn [bind];now rewrite Finish.
 - constructor;[exact Ret|exact WF|exact SP|exact Regs|apply StoreHistory.rejoin_history;exact History| |].
   all: cbn [StoreHistory.rejoin machine];rewrite Mem;assumption.
Qed.
