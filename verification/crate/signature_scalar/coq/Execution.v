From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Packed memory.PackedMemory execution.LinkedCalls
 execution.MaskTrace execution.CircuitFacts execution.MaskedWords execution.WordSemantics
 execution.WordBounds memory.ByteMemory memory.FlatMemory memory.MemoryGeometry abi.SysV.
From ProofArithmetic Require Import Radix.
From Curve25519 Require Import Scalar SignedRadix16.
From Ed25519Simd Require Import Radix16Output.
From Ed25519Simd.SignatureScalar Require Import Program Audit Inputs Arithmetic Words.
Import ListNotations. Local Open Scope Z_scope.

Definition literal_word bs off := read_word (fun i=>nth (Z.to_nat i) bs 0) off.
Local Lemma mapped_read s a bs n off : mapped s a bs -> 0<=off ->
 off+Z.of_nat n<=Z.of_nat(length bs) ->
 read_le n (mem s) (a+off)=read_le n (fun i=>nth (Z.to_nat i) bs 0) off.
Proof.
 intros M;revert off;induction n;intros off L U;[reflexivity|].
 cbn [read_le];replace (a+off+1) with (a+(off+1)) by ring.
 rewrite IHn by lia;rewrite <- (M (Z.to_nat off)) by lia;now rewrite Z2Nat.id by lia.
Qed.

Local Lemma mask16_low f : (forall j,(8<=j)%nat -> f j=false) ->
 mask16 f=mask_word 8 (fun j=>Z.b2z (f j)).
Proof.
 intro H;unfold mask16.
 change (mask_word (8+8) (fun j=>Z.b2z (f j))=mask_word 8 (fun j=>Z.b2z (f j))).
 generalize 8%nat at 1 as n;intro n;induction n;[reflexivity|].
 change (mask_word (n+8) (fun j=>Z.b2z (f j)) + Z.b2z (f (n+8)%nat)*2^Z.of_nat (n+8)=mask_word 8 (fun j=>Z.b2z (f j))).
 rewrite IHn,H by lia;cbn [Z.b2z];ring.
Qed.
Local Lemma lt_bit x y : Z.b2z (x <? y)=1 <-> x<y.
Proof. destruct (Z.ltb_spec x y);cbn [Z.b2z];lia. Qed.

Section Execution.
Variables (pc n ro slide:Z) (bs:list Z) (s:cpu) (ks:nat->nat->bool).
Hypothesis constants : length bs=32%nat /\ literal_word bs 0=l0 /\
 literal_word bs 8=l1 /\ literal_word bs 24=l3.
Hypothesis P:placement s (slide+pc) n (slide+ro).
Hypothesis W:LinkedCalls.well_formed s.
Hypothesis M:mapped s (slide+ro) bs.
Let rd t:=read_word (mem s) (word (slide+t)).
Local Lemma ro_word off : 0<=off<=24 -> rd (ro+off)=literal_word bs off.
Proof.
 intro O;destruct (literals_fit _ _ _ _ P) as [[A U] _].
 unfold rd;rewrite word_fits by (unfold word64;lia).
 rewrite Z.add_assoc;apply mapped_read;[exact M|lia|rewrite (proj1 constants);lia].
Qed.
Local Lemma literal_values : rd ro=l0 /\ rd (ro+8)=l1 /\ rd (ro+24)=l3.
Proof.
 replace (rd ro) with (rd (ro+0)) by now rewrite Z.add_0_r.
 rewrite !ro_word by lia;tauto || exact (proj2 constants).
Qed.

Let state j := lanes ro slide s ks j.
Let pred j := mask (state j) result_mask.
Let prep := prepared ro slide s ks.
Let rows := Packed.execute 8 write_digits prep.
Let last := body ro slide s ks.
Let out := returning last.
Let dst := LinkedCalls.regs s 7%nat.
Local Lemma words_ok j : (j<8)%nat -> pred j=accepted s j /\
 forall i,(i<4)%nat -> vectors prep j i=chunk (selected s j+bias 64) i.
Proof. apply (lane_result P W ks literal_values). Qed.
Local Lemma mask_small : mask16 pred=mask_word 8 (fun j=>Z.b2z (pred j)).
Proof.
 apply mask16_low. intros j J;exact (@high_result s ro slide ks j J).
Qed.
Local Lemma mask_ok : 0<=mask16 pred<256 /\ forall j,(j<8)%nat ->
 (Z.testbit (mask16 pred) (Z.of_nat j)=true <-> scalar s j<L).
Proof.
 rewrite mask_small;destruct (mask_word_bits 8 (fun j=>Z.b2z (pred j))
   ltac:(intros j J;cbv beta;destruct (pred j);[right|left];reflexivity)) as [R Bits].
 split;[exact R|];intros j J;rewrite Bits by assumption;rewrite (proj1 (words_ok j J)).
 apply lt_bit.
Qed.
Local Lemma row_result j k : (j<8)%nat -> (k<64)%nat ->
 mem rows (dst+64*Z.of_nat j+Z.of_nat k) = digit (selected s j) k mod 256.
Proof.
 intros J K;destruct(output_routed j k J K) as [v [Store Byte]].
 change dst with (LinkedCalls.regs prep 7%nat).
 unfold rows,Packed.execute;rewrite row_byte by assumption;fold output_state;rewrite Store,Byte.
 apply routed_digit;[exact K|apply (proj2 (words_ok j J))].
Qed.
Local Lemma final_mem a : mem out a=mem rows a.
Proof. change (mem last a=mem rows a);unfold last,body;rewrite upper_memory;reflexivity. Qed.
Lemma recorded_digits :
 let ws:=digit_writes pc n ro slide s ks in
 WriteTrace.confined (output s) ws /\ forall x, mem out x=WriteTrace.replay (mem s) ws x.
Proof.
 unfold digit_writes;cbv zeta.
 pose proof (PackedWrites.execution false 8 (digit_start pc n slide) write_digits prep eq_refl) as H.
 split;[exact (proj1 H)|intro x;rewrite final_mem;exact (proj2 H x)].
Qed.

Local Lemma frame : preserved (fun a=>~output s a) (mem s) (mem out).
Proof. intros a A;rewrite final_mem;change (mem s a) with (mem prep a);apply outside_rows,A. Qed.
Local Lemma final_bytes : byte_memory (mem out).
Proof.
 intro a;destruct (Z_le_dec dst a), (Z_lt_dec a (dst+512));
 try (rewrite frame by (unfold output;fold dst;lia);apply W).
 set (d:=a-dst);assert (D:0<=d<512) by (unfold d;lia).
 set (j:=Z.to_nat (d/64));set (k:=Z.to_nat (d mod 64)).
 pose proof (Z.mod_pos_bound d 64 ltac:(lia)).
 assert (J:0<=d/64<8) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
 assert (E:a=dst+64*Z.of_nat j+Z.of_nat k) by
  (unfold j,k;rewrite !Z2Nat.id by lia;pose proof(Z.div_mod d 64 ltac:(lia));unfold d in *;lia).
 rewrite E,final_mem,row_result by (unfold j,k;lia);apply Z.mod_pos_bound;lia.
Qed.
Local Lemma row_digits j : (j<8)%nat ->
 digits out dst j=map (digit (selected s j)) (seq 0 64).
Proof.
 intros J;apply map_ext_in;intros k K;apply in_seq in K.
 rewrite final_mem,row_result by lia;apply signed_encoding,digit_range.
Qed.
Local Lemma keeps_stack : LinkedCalls.regs last 4%nat=LinkedCalls.regs s 4%nat.
Proof. unfold last,body;rewrite upper_registers;reflexivity. Qed.
Local Lemma mask_register : LinkedCalls.regs out 0%nat=mask16 pred.
Proof. change (LinkedCalls.regs last 0%nat=mask16 pred);unfold last,body;rewrite upper_registers;reflexivity. Qed.
Local Lemma return_pc : word (stack_top (LinkedCalls.regs last) (mem last))=
 read_word (mem s) (LinkedCalls.regs s 4%nat).
Proof.
 unfold stack_top;rewrite keeps_stack,(word_fits (LinkedCalls.regs s 4%nat)) by apply W.
 assert (F:preserved (fun a=>~output s a) (mem s) (mem last)).
 { intros a A;unfold last,body;rewrite upper_memory.
   change (mem rows a=mem prep a);apply outside_rows,A. }
 unfold read_word;rewrite (preserved_read _ _ _ _ _ F) by
   (intros;destruct (ret_fits _ _ _ _ P) as [_ D];unfold disjoint,output in *;lia).
 apply word_fits,read_word_bound,W.
Qed.
Theorem verified_call : reads_inputs s /\
 let '(ip,final):=run pc n ro slide s ks in
 ip=read_word (mem s) (LinkedCalls.regs s 4%nat) /\
 LinkedCalls.regs final 4%nat=LinkedCalls.regs s 4%nat+8 /\
 (forall r,In r sysv_saved -> LinkedCalls.regs final r=LinkedCalls.regs s r) /\
 preserved (fun a=>~output s a) (mem s) (mem final) /\ byte_memory (mem final) /\
 0<=LinkedCalls.regs final 0%nat<256 /\
 forall j,(j<8)%nat ->
 let x:=scalar s j in let ds:=digits final dst j in
 (Z.testbit (LinkedCalls.regs final 0%nat) (Z.of_nat j)=true <-> x<L) /\
 if x<?L then Forall (fun d=> -8<=d<8) ds /\ number 16 ds=x else ds=repeat 0 64.
Proof.
 split;[exact (inputs_safe P)|];split;[exact return_pc|].
 split.
 - change (word (LinkedCalls.regs last 4%nat+8)=LinkedCalls.regs s 4%nat+8).
   rewrite keeps_stack;apply word_fits;destruct (ret_fits _ _ _ _ P) as [[A U] _].
   pose proof (next_sp_fits _ _ _ _ P);unfold word64;lia.
 - split.
   + intros r I;destruct I as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];reflexivity.
   + split;[exact frame|];split;[exact final_bytes|].
     split;[change (0<=LinkedCalls.regs out 0%nat<256);rewrite mask_register;apply mask_ok|].
     intros j J;change ((Z.testbit (LinkedCalls.regs out 0%nat) (Z.of_nat j)=true <-> scalar s j<L) /\
       if scalar s j<?L then Forall (fun d=> -8<=d<8) (digits out dst j) /\ number 16 (digits out dst j)=scalar s j
       else digits out dst j=repeat 0 64).
     rewrite mask_register,row_digits by exact J.
     split;[apply mask_ok,J|].
     unfold selected,accepted;destruct (Z.ltb_spec (scalar s j) L).
     * split;[apply Forall_forall;intros d I;apply in_map_iff in I as [i [<- _]];apply digit_range|].
       apply reconstruct;split;[apply (read_le_bound 32 _ _ (proj2 (proj2 W)))|assumption].
     * apply trans_eq with (map (fun _ : nat=>0) (seq 0 64));[apply map_ext_in;intros k K;apply zero_digit;apply in_seq in K;lia|reflexivity].
Qed.
End Execution.
