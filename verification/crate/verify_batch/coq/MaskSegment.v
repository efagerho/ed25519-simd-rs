From Coq Require Import ZArith List Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics execution.MappedFetch memory.ByteMemory.
From Machine Require execution.MaskedResult execution.MaskTransfer.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderProduct DecoderKernel.
Local Open Scope Z_scope.

(* One certificate checks a store-free predicate block against the current
   decoder text. Its CPU, opmasks and write history all pass to the caller. *)
Definition bytes pc n:=firstn n (skipn (Z.to_nat pc) text).
Theorem checked pol bias e pc n ops p ks v k : loaded pol bias (mem e) (writable e) ->
 0<=pc -> pc+Z.of_nat n<Z.of_nat(length text) -> length(bytes pc n)=n ->
 MaskedResult.assemble pc ops=Some(bytes pc n) -> ip p=base bias+pc -> accounted e (writable e) p ->
 well_formed(machine p) -> MaskedResult.evaluate (base bias) (machine p) ks ops=Some(v,k) ->
 exists q,MaskedResult.execute (base bias) ops p ks=Some(q,k) /\ machine q=v /\
 ip q=base bias+(pc+Z.of_nat n) /\ accounted e (writable e) q /\ well_formed(machine q) /\
 regs(machine q)=regs(machine p) /\ mem(machine q)=mem(machine p) /\ log q=log p.
Proof.
 intros I Pos Range Len Enc PC Acc W Eval.
 destruct(mapped_now _ _ _ I _ _ _ Acc (decode_in pol)) as [Map _].
 assert (Mapped:mapped (mem(machine p)) (ip p) (bytes pc n)).
 { rewrite PC;replace pc with (Z.of_nat(Z.to_nat pc)) at 1 by (rewrite Z2Nat.id;lia).
   apply MaskTransfer.subimage with (text:=text);[exact Map|rewrite Len;lia|rewrite Len;reflexivity]. }
 destruct(MaskedResult.stable _ _ _ _ _ _ Eval) as [G [M [_ WF]]].
 pose proof(MaskedResult.mapped_block _ _ _ _ _ _ _ _ PC Enc Mapped Eval) as Run.
 eexists;split;[exact Run|split;[reflexivity|split]].
 - change (word(ip p+Z.of_nat(length(bytes pc n)))=base bias+(pc+Z.of_nat n)).
   rewrite PC,Len,Z.add_assoc;apply word_fits;rewrite <-Z.add_assoc;apply (DecoderProduct.address_fits _ _ _ I DecoderKernel.Carry);change (0<=pc+Z.of_nat n<Z.of_nat(length text));lia.
 - split;[unfold accounted;cbn [log machine];rewrite M;exact Acc|]. exact (conj (WF W) (conj G (conj M eq_refl))).
Qed.
