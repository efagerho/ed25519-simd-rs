From Coq Require Import List ZArith Lia.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.WordSemantics execution.WordBounds memory.ByteMemory memory.MemoryGeometry abi.SysV.
From SHA512 Require Import Spec.
From Ed25519Simd.Sha512Challenge Require Import Image Control Frame Lanes Execution Refinement Writes Audit Rows Output ObjectBytes LiteralBytes.
Local Open Scope Z_scope.

Local Definition rom a := nth (Z.to_nat a) LiteralBytes.symbol_bytes 0.
Local Lemma table_read s ro : mapped s ro LiteralBytes.symbol_bytes ->
  forall off n, 0<=off -> off+8*Z.of_nat n<=832 ->
  literal_words (mem s) (ro+off) n=literal_words rom off n.
Proof.
 intros M off n L U. unfold literal_words. apply map_ext_in. intros j J. apply in_seq in J.
 f_equal. replace (ro+off+8*Z.of_nat j) with (ro+(off+8*Z.of_nat j)) by ring.
 assert (R: forall k pos, 0<=pos -> pos+Z.of_nat k<=832 ->
   read_le k (mem s) (ro+pos)=read_le k rom pos).
 { induction k; intros pos A B;[reflexivity|].
   cbn [read_le]. replace (ro+pos+1) with (ro+(pos+1)) by ring.
   rewrite IHk by lia. unfold rom. rewrite <- M by (change (length LiteralBytes.symbol_bytes) with 832%nat;lia).
   now rewrite Z2Nat.id by lia. }
 apply R;lia.
Qed.

Local Lemma load_constants s slide ro : mapped s (slide+ro) LiteralBytes.symbol_bytes ->
 initial_at (mem s) (slide+ro)=initial /\
 group_constants (mem s) slide (keys (expected ObjectBytes.address ro))=constants.
Proof.
 intro M. unfold initial_at, group_constants, expected.
 cbn [keys flat_map seq map]. repeat rewrite <- Z.add_assoc.
 repeat rewrite (Z.add_assoc slide ro).
 rewrite !(table_read s (slide+ro) M) by lia.
 vm_compute; split; reflexivity.
Qed.

Theorem assembled_sha512_challenge_correct :
 sha512_contract ObjectBytes.address ObjectBytes.symbol_bytes LiteralBytes.address LiteralBytes.symbol_bytes.
Proof.
 constructor.
 - vm_compute; reflexivity.
 - vm_compute; reflexivity.
 - vm_compute; reflexivity.
 - exact masked_reads.
 - exact cursor_fits.
 - apply run_writes;vm_compute;reflexivity.
 - intros slide s P W M. set (pc:=slide+ObjectBytes.address) in *.
   set (ro:=slide+LiteralBytes.address) in *.
   assert (Extent:0<=pc /\ pc+7328<=2^64) by (apply (proj1 (image_fits _ _ _ _ P))).
   assert (U:word64 (pc+Z.of_nat (offset AfterUpper listing))).
   { change (word64 (pc+514)). unfold word64;lia. }
   assert (L:word64 (pc+Z.of_nat (offset AfterLower listing))).
   { change (word64 (pc+6626)). unfold word64;lia. }
   destruct (returning_digest _ _ _ _ P W _ _ U L) as [m [Run [K H]]].
   exists (restored s m). split.
   + unfold run. assert (Plan : decode ObjectBytes.address ObjectBytes.symbol_bytes =
       Some (expected ObjectBytes.address LiteralBytes.address)) by (vm_compute;reflexivity).
     assert (Loads : loads_match ObjectBytes.address LiteralBytes.address ObjectBytes.symbol_bytes=true)
       by (vm_compute;reflexivity).
     rewrite Loads,Plan. destruct (load_constants s slide LiteralBytes.address M) as [IV Table].
     rewrite IV, Table. cbn [expected upper lower depth row_step]. rewrite (enter_frame _ _ _ _ P). unfold pos. rewrite !Z.add_assoc. exact (f_equal (option_map (restored s)) Run).
   + pose proof (stack_fits _ _ _ _ P) as [Fits Ret].
     assert (BP : word64 (sp s-8)).
     { unfold frame in Fits. pose proof (Z.mod_pos_bound (sp s-8) 64 ltac:(lia)).
       unfold word64;lia. }
     assert (SP : word64 (sp s)) by apply W.
     assert (End : word64 (sp s+8)) by (unfold word64 in *;lia).
     unfold restored. cbn [stack_step stack_top advance_rsp put result_regs result_mem
                           target_ip return_ip return_sp saved_register after Nat.eqb].
     unfold stack_top,advance_rsp,put; cbn [Nat.eqb]. fold (sp s). rewrite (word_fits _ BP). replace (sp s-8+8) with (sp s) by ring.
     rewrite !(word_fits _ SP), (word_fits _ End), (caller_pc _ _ _ _ P _ K).
     rewrite (word_fits _ (read_word_bound _ _ (proj2 (proj2 W)))).
     split;[reflexivity|]. split;[reflexivity|]. split.
     * intros r R. destruct (in_dec Nat.eq_dec r sysv_saved);[|contradiction].
       destruct R as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];try reflexivity.
       change (Some (read_word m (sp s-8))=Some (regs s 5%nat)).
       now rewrite (saved_bp _ _ _ _ P W _ K).
     * split;[exact (proj1 K)|]. split;[|exact H]. intros x X.
       exact (outside s m x K X).
Qed.
