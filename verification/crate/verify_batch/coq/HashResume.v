From Coq Require Import List ZArith Lia.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordBounds abi.SysV memory.ByteMemory.
From Ed25519Simd.VerifyBatch Require Import Policy Return.
From Ed25519Simd.VerifyBatch Require NativeHash.
From Ed25519Simd.Sha512Challenge Require Execution.
Import ListNotations. Local Open Scope Z_scope.

(* SHA exposes all memory, RSP, the return address and the SysV saved GPRs.
   Each completion supplies the remaining registers and flags independently. *)
Definition compatible (r:Sha512Challenge.Execution.observation) s:=
 mem s=Sha512Challenge.Execution.after r /\ regs s 4%nat=Sha512Challenge.Execution.return_sp r /\
 forall g,In g sysv_saved -> Sha512Challenge.Execution.saved_register r g=Some(regs s g).
Definition complete r noise:=
 let gprs:=fun g=>if Nat.eqb g 4 then Sha512Challenge.Execution.return_sp r
    else if in_dec Nat.eq_dec g sysv_saved then
        match Sha512Challenge.Execution.saved_register r g with Some v=>v | None=>regs noise g end
    else regs noise g in
 CPU gprs (vectors noise) (flag noise) (Sha512Challenge.Execution.after r).
Definition resume bias q r s c:=Cursor (Sha512Challenge.Execution.return_ip r) s c (NativeHash.history bias q).

From Ed25519Simd.VerifyBatch Require BatchWindow.
Section Iteration.
Context `{iteration:BatchWindow.t}.
Lemma complete_ok pol bias o e q r noise : placement e -> well_formed(machine q) -> well_formed noise ->
 NativeHash.returned pol bias o e q r -> compatible r (complete r noise) /\ well_formed(complete r noise).
Proof.
 intros P W N R.
 assert (SP:word64 (Sha512Challenge.Execution.return_sp r)).
 { rewrite (NativeHash.stack _ _ _ _ _ _ R);destruct (stack_ok _ P) as [[L H] _];unfold Rows.frame,sp,word64 in *;lia. }
 assert (K:forall g,In g sysv_saved -> regs(complete r noise) g=regs(machine q) g).
 { intros g I;cbn [complete regs];destruct (Nat.eqb_spec g 4) as [->|Other];[simpl in I;intuition discriminate|].
   destruct(in_dec Nat.eq_dec g sysv_saved);[now rewrite (NativeHash.saved _ _ _ _ _ _ R g I)|contradiction]. }
 split.
 - split;[reflexivity|split;[reflexivity|intros g I;rewrite K by assumption;apply (NativeHash.saved _ _ _ _ _ _ R),I]].
 - split;[intro g;destruct(in_dec Nat.eq_dec g sysv_saved) as [I|I];[rewrite K by exact I;apply W|]|].
   + cbn [complete regs];destruct(Nat.eqb g 4);[exact SP|destruct(in_dec Nat.eq_dec g sysv_saved);[contradiction|apply N]].
   + split;[apply N|exact (NativeHash.bytes _ _ _ _ _ _ R)].
Qed.

Lemma accounted pol bias o e q r s c : NativeHash.returned pol bias o e q r -> compatible r s ->
 LinkedRun.accounted e (writable e) (resume bias q r s c).
Proof.
 intros R [M _];split;[exact (NativeHash.writes _ _ _ _ _ _ R)|intro x;cbn [resume machine];rewrite M;exact (NativeHash.replayed _ _ _ _ _ _ R x)].
Qed.
Lemma saved pol bias o e q r s : NativeHash.returned pol bias o e q r -> compatible r s ->
 forall g,In g sysv_saved -> regs s g=regs(machine q) g.
Proof. intros R [_ [_ Keep]] g I;specialize(Keep g I);rewrite (NativeHash.saved _ _ _ _ _ _ R g I) in Keep;congruence. Qed.
End Iteration.
