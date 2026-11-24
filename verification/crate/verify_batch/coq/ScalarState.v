From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.LinkedCalls execution.WordBounds execution.WordSemantics execution.IndexedLoads
 execution.ProjectionWords execution.MaskedWords execution.CircuitFacts memory.ByteMemory memory.PackedMemory.
From Machine Require execution.Packed.
From Ed25519Simd Require Radix16Output.
From Ed25519Simd.SignatureScalar Require Import Program.
Import ListNotations. Local Open Scope Z_scope.

Local Lemma below n check : forallb check (seq 0 n)=true -> forall i,(i<n)%nat -> check i=true.
Proof. intros C i I;apply forallb_forall with (x:=i) in C;[exact C|apply in_seq;lia]. Qed.

Lemma input_words s : well_formed s -> well_formed (loaded s).
Proof.
 intro W;split;[|split;[|exact (proj2(proj2 W))]].
 - intro r;apply indexed_ok;[exact W|]. destruct(Nat.lt_ge_cases r 16) as [L|H].
   + exact (below 16 (fun i=>indexed (gp (summary inputs) i)) ltac:(vm_compute;reflexivity) r L).
   + do 16 (destruct r as [|r];[lia|]);reflexivity.
 - intros j r J;apply indexed_ok;[exact W|]. destruct(Nat.lt_ge_cases r 32) as [L|H].
   + pose proof(below 8 (fun lane=>forallb (fun i=>indexed (vec (summary inputs) i lane)) (seq 0 32))
       ltac:(vm_compute;reflexivity) j J) as Row;apply (below 32 _ Row),L.
   + do 32 (destruct r as [|r];[lia|]);change ((j<?8)%nat=true);apply Nat.ltb_lt,J.
Qed.

Lemma before_pack ro slide s ks : well_formed s -> well_formed (prepared ro slide s ks).
Proof.
 intros W;pose proof(input_words _ W) as [G [V B]].
 assert (Rows:forall j,(j<8)%nat -> lane_words (lanes ro slide s ks j)).
 { intros j J;unfold lanes,MaskedWords.execute;apply masked_code;[split;[apply G|intros;apply V,J]|vm_compute;reflexivity]. }
 split;[intro r|split;[intros j r J|exact B]].
 - unfold prepared;cbn [regs];unfold Packed.update;destruct (r=?0)%nat;[apply (proj1(Rows 0%nat ltac:(lia)))|apply G].
 - exact (proj2(Rows j J) r).
Qed.

Lemma digit_vectors s : well_formed s -> forall j r,(j<8)%nat ->
 word64(vectors (Packed.execute 8 Radix16Output.write_digits s) j r).
Proof.
 intros W j r J;apply packed_ok;[exact W|];destruct(Nat.lt_ge_cases r 32) as [L|H].
 - pose proof (below 8 (fun lane=>forallb (fun i=>packed (Packed.qword (Packed.zmm Radix16Output.output_state i) lane)) (seq 0 32))
    ltac:(vm_compute;reflexivity) j J) as Row;apply (below 32 _ Row),L.
 - do 32 (destruct r as [|r];[lia|]);change ((j<?8)%nat=true);apply Nat.ltb_lt,J.
Qed.

Theorem returned_words pc n ro slide s ks ip out :
 well_formed s -> Program.run pc n ro slide s ks=(ip,out) -> byte_memory (mem out) -> well_formed out.
Proof.
 intros W Run B;pose proof(f_equal snd Run) as E;change (returning (body ro slide s ks)=out) in E;subst out;clear Run.
 set (a:=prepared ro slide s ks).
 set (rows:=Packed.execute 8 Radix16Output.write_digits a).
 set (m:=mask16 (fun j=>MaskedWords.mask (lanes ro slide s ks j) result_mask)).
 assert (MW:word64 m).
 { pose proof(mask_word_bits 16 (fun j=>Z.b2z(MaskedWords.mask (lanes ro slide s ks j) result_mask))
       ltac:(intros j J;cbv beta;destruct (MaskedWords.mask (lanes ro slide s ks j) result_mask);[right|left];reflexivity)) as [Range _].
   unfold m,mask16,word64;lia. }
 assert (A:well_formed a) by (apply before_pack,W).
 split;[intro r|split;[intros j r J|exact B]].
 - change (word64 (Instructions.put (regs (Packed.execute 8 [Packed.Upper] (set rows 0 m))) 4
     (word(regs (Packed.execute 8 [Packed.Upper] (set rows 0 m)) 4%nat+8)) r)).
   unfold Instructions.put;destruct (4=?r)%nat;[apply mod64_word|]. rewrite upper_registers.
   change (word64 (Instructions.put (regs rows) 0 m r));unfold Instructions.put;destruct (0=?r)%nat eqn:R;[exact MW|].
   change (word64 (Packed.update (regs a) 0 (Packed.value a (Packed.acc Radix16Output.output_state)) r)).
   unfold Packed.update;rewrite Nat.eqb_sym,R;apply A.
 - change (word64 (vectors (Packed.execute 8 [Packed.Upper] (set rows 0 m)) j r)).
   cbn [Packed.execute Packed.finish fold_left Packed.step Packed.initial Packed.zmm Packed.qword Packed.value vectors].
   destruct (r<?16)%nat;cbn [Packed.qword Packed.value];try destruct (j<?2)%nat;cbn [Packed.value set set_regs vectors];try exact (digit_vectors a A j r J);try (unfold word64;lia).
Qed.
