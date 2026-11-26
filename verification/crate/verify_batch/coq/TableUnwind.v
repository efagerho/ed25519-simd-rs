From Coq Require Import List ZArith Znumtheory Lia.
From Machine Require Import execution.WordSemantics execution.WordBounds execution.LinkedCalls execution.LinkedRun
 memory.ByteMemory memory.FlatMemory memory.MemoryGeometry abi.SysV.
From Machine Require execution.StoreHistory.
From Ed25519Simd.KeyTable Require NativeBuilder NativeTable CallLayout Audit Object.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar.
From Ed25519Simd.VerifyBatch Require TableEntry TableParentFrame.
Import ListNotations. Local Open Scope Z_scope.

Definition back bias:=bias+TableEntry.site+185.
Record returned pol bias e caller q:Prop:=ReturnedTable {
 pc:ip q=back bias;
 writes:accounted e (writable e) q;
 words:well_formed(machine q);
 stack:regs(machine q) 4%nat=TableEntry.frame pol e+8;
 registers:forall r,In r sysv_saved -> regs(machine q) r=regs(machine caller) r;
 parent:TableParentFrame.retained pol bias e (machine caller) (machine q);
 contents:NativeTable.contents (TableEntry.tables e) (TableEntry.point_words e (machine caller)) (mem(machine q))
}.

Definition observe bias p ks:=bind (TableEntry.enter bias p) (fun a=>NativeBuilder.execute bias a ks).

Lemma images pol : forall sym,In sym CallLayout.children -> In sym (children pol).
Proof.
 intros sym [<-|[<-|[<-|[<-|[]]]]];[apply TableEntry.image|apply BatchDecode.decode_in|apply BatchDecode.helper_in|].
 apply in_or_app;left;do 15 right;left;reflexivity.
Qed.

Lemma loan pol e : placement e -> forall x,CallLayout.footprint (TableEntry.frame pol e)
 (TableEntry.point e) (TableEntry.tables e) x -> writable e x.
Proof.
 intros P x [Stack|[Point|Table]];unfold CallLayout.span,TableEntry.frame,common_top,Rows.frame,sp,TableEntry.point,TableEntry.tables in *;
 destruct pol;unfold writable,span,sp;intuition lia.
Qed.

Lemma buffers pol e : placement e -> let t:=TableEntry.frame pol e in
 KeyTable.Frame.placement [] 8 t (TableEntry.point e) (TableEntry.tables e) /\ word64(t+8).
Proof.
 intros P t;destruct(stack_ok _ P) as [[L H] S];destruct(scratch_ok _ P) as [[B E] A];pose proof(scratch_stack _ P) as Sep.
 assert (SP:t mod 16=8).
 { unfold t,TableEntry.frame,common_top,Rows.frame;fold (sp e);destruct pol.
   - replace (sp e-1000-8-0-112) with (sp e+(-70)*16) by ring;now rewrite Z.mod_add by lia.
   - replace (sp e-1000-8-16-112) with (sp e+(-71)*16) by ring;now rewrite Z.mod_add by lia. }
 assert (Pt:(TableEntry.point e) mod 64=0).
 { unfold TableEntry.point;replace (scratch e+1024) with (scratch e+16*64) by ring;now rewrite Z.mod_add by lia. }
 assert (Dst:(TableEntry.tables e) mod 8=0).
 { assert (R:scratch e mod 8=0) by (rewrite (Zmod_div_mod 8 64) by (try lia;exists 8;reflexivity);now rewrite A).
   unfold TableEntry.tables;replace (scratch e+3584) with (scratch e+448*8) by ring;now rewrite Z.mod_add by lia. }
 split;[split;[exact SP|split;[exact Pt|split;[exact Dst|]]]|].
 all: unfold t,TableEntry.frame,common_top,Rows.frame,sp,TableEntry.point,TableEntry.tables,KeyTable.Frame.stack_depth,
       disjoint,fits64,word64 in *;change (Z.of_nat 8) with 8;destruct pol;repeat split;try lia;intros r c _ [].
Qed.

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Theorem from_eligible pol bias e before p ks:placement e -> loaded pol bias (mem e) (writable e) ->
 (bias+DecoderFrame.origin) mod 64=0 -> EligibleLanes.post pol bias e before p -> regs(machine p) 14%nat<>0 ->
 exists q bank,observe bias p ks=Some(q,bank) /\ returned pol bias e p q.
Proof.
 intros P I Al E Live;destruct(TableEntry.checked _ _ _ _ _ P I E Live) as [a [Enter A]].
 destruct(TableEntry.arguments _ _ _ _ _ A) as [SP [DI [SI DX]]].
 set (l:=NativeBuilder.buffers a).
 assert (View:l=CallLayout.Layout (TableEntry.frame pol e) (TableEntry.point e) (TableEntry.tables e)
   (CallLayout.footprint (TableEntry.frame pol e) (TableEntry.point e) (TableEntry.tables e))).
 { unfold l,NativeBuilder.buffers;now rewrite SP,DI,SI. }
 destruct(buffers pol e P) as [Place Top].
 assert (Image:CallLayout.loaded (machine a) bias l).
 { rewrite View;constructor;intros addr bs C;pose proof(images pol _ C) as Child.
   destruct(mapped_now _ _ _ I _ _ _ (TableEntry.writes _ _ _ _ _ A) Child) as [Map Sep].
   split;[exact (proj1(symbols _ _ _ _ I _ _ Child))|split;[exact Map|]].
   intros x Code X;apply (Sep x Code),(loan pol e P x),X. }
 destruct(KeyTable.Audit.native_eight _ _ _ _ _ _ _ _ KeyTable.Object.assembled_key_table_correct bias a ks
   (TableEntry.address _ _ _ _ _ A) DX (TableEntry.words _ _ _ _ _ A)
   ltac:(fold l;rewrite View;exact Place) Al Image)
   as [q [bank [Run Q]]].
 destruct Q as [PC W Stack Regs Trace Parent Data];fold l in PC,Stack,Trace,Parent,Data;rewrite View in PC,Stack,Trace,Parent,Data;
   cbn [CallLayout.sp CallLayout.point_ptr CallLayout.table_ptr CallLayout.private CallLayout.writable] in *.
 exists q,bank;split;[unfold observe;now rewrite Enter|constructor].
 - now rewrite PC,(TableEntry.link _ _ _ _ _ A).
 - apply (StoreHistory.account _ _ _ _ (TableEntry.writes _ _ _ _ _ A));
   exact (StoreHistory.lend _ _ _ _ (loan pol e P) Trace).
 - exact W.
 - now rewrite Stack,word_fits by exact Top.
 - intros r R;rewrite Regs by exact R;apply (TableEntry.caller_regs _ _ _ _ _ A);
   destruct R as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];discriminate.
 - unfold TableParentFrame.retained;rewrite <-(TableParentFrame.on_entry _ _ _ _ _ A);exact Parent.
 - eapply NativeTable.input_ext;[|exact Data].
   intros n N;unfold TableEntry.point_words,buffer_words;rewrite (TableEntry.memory_after _ _ _ _ _ A).
   apply preserved_read with (outside:=span (TableEntry.point e) 1280).
   + intros x X;unfold store_word;apply write_outside;pose proof(scratch_stack _ P) as Apart;
     unfold span,disjoint,TableEntry.point,TableEntry.frame,common_top,Rows.frame,sp in *;destruct pol;lia.
   + intros b B;change (0<=b<8) in B;unfold span;lia.
Qed.
End Iteration.
