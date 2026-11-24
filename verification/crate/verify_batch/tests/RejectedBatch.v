(* Exercise the complete single-row return, including the repeated tail row.
   The caller supplies a noncanonical S and an output byte initially set to 1. *)
From Coq Require Import List ZArith Bool Lia FSets.FMapPositive.
From Machine Require Import execution.LinkedCalls execution.LinkedRun execution.WordSemantics
  memory.ByteMemory memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.PrepareChunk Require CommonBytes StrictBytes.
From Ed25519Simd.SignatureScalar Require ObjectBytes OrderBytes.
From Ed25519Simd.Zip215 Require ScatterBytes.
From Ed25519Simd.VerifyBatch Require Import Policy ZipBytes DalekBytes RejectExecution.
Import ListNotations. Local Open Scope Z_scope.

Definition symbols := [(ZipBytes.address,ZipBytes.symbol_bytes);(DalekBytes.address,DalekBytes.symbol_bytes);
 (CommonBytes.address,CommonBytes.symbol_bytes);(StrictBytes.address,StrictBytes.symbol_bytes);
 (SignatureScalar.ObjectBytes.address,SignatureScalar.ObjectBytes.symbol_bytes);
 (OrderBytes.address,OrderBytes.symbol_bytes);(Zip215.ScatterBytes.address,Zip215.ScatterBytes.symbol_bytes)].
Definition image_end := fold_left Z.max
  (map (fun '(a,bs)=>a+Z.of_nat(length bs)) symbols) 0.
Definition rows := 64*(image_end/64+2).
Definition signature := rows+128.
Definition scratch := rows+1024.
Definition output := rows+28000.
Definition stack := rows+60008.
Definition ret := 12345.
Definition inputs x :=
 if (rows<=?x)&&(x<?rows+40) then word_byte
   (nth (Z.to_nat ((x-rows)/8)) [rows+64;signature;rows+200;0;0] 0) ((x-rows) mod 8)
 else if (signature+32<=?x)&&(x<?signature+64) then 255
 else if (stack<=?x)&&(x<?stack+8) then word_byte ret (x-stack)
 else if x=?output then 1 else 0.
Fixpoint install (p:positive) bs (m:PositiveMap.t Z) := match bs with
 | []=>m | b::rest=>install (Pos.succ p) rest (PositiveMap.add p b m) end.
Definition linked := fold_left (fun m '(a,bs)=>install (Z.to_pos a) bs m) symbols (PositiveMap.empty Z).
Definition image x := if rows<=?x then inputs x else
 match PositiveMap.find (Z.to_pos x) linked with Some b=>b | None=>inputs x end.
Definition initial := CPU (fun r=>match r with
 | 7%nat=>rows | 6%nat=>1 | 2%nat=>output | 1%nat=>scratch | 4%nat=>stack
 | _=>100+Z.of_nat r end) (fun _ _=>0) None image.

Definition in_range a n x := (a<=?x)&&(x<?a+n).
Definition allowed x := in_range (stack-16384) 16384 x || in_range scratch 25344 x || (x=?output).
Definition covers (w:store) := forallb (fun i=>allowed (WriteTrace.address w+Z.of_nat i)) (seq 0 (size w)).
Definition check pol entry text := match scalar_rejection pol 0 entry text initial None (fun _ _=>true) with
 | None | Some (NextChunk _)=>false
 | Some (BatchReturned p)=> let s:=machine p in
   (ip p=?ret) && (regs s 4%nat=?stack+8) && (regs s 0%nat=?1) &&
   forallb (fun r=>regs s r=?regs initial r) [3;5;12;13;14;15]%nat &&
   (mem s output=?0) && (WriteTrace.replay image (log p) output=?0) &&
   forallb covers (log p)
 end.
Example zip_returns : check Zip215 ZipBytes.address ZipBytes.symbol_bytes=true.
Proof. lazy;reflexivity. Qed.
Example dalek_returns : check Dalek DalekBytes.address DalekBytes.symbol_bytes=true.
Proof. lazy;reflexivity. Qed.

Lemma fixture_rejects pol : ~signature_accepts pol (read_input image rows 0).
Proof.
 intros [Bound _].
 change (2^256-1 < Curve25519.Scalar.L) in Bound.
 vm_compute in Bound;discriminate.
Qed.

Theorem same_return pol pc text : check pol pc text=true ->
 exists q,scalar_rejection pol 0 pc text initial None (fun _ _=>true)=Some(BatchReturned q) /\
   ip q=ret /\ regs(machine q) 4%nat=stack+8 /\ regs(machine q) 0%nat=1 /\
   mem(machine q) output=0 /\
   (mem(machine q) output=1 <-> signature_accepts pol (read_input image rows 0)) /\
   replays initial q /\ confined (fun x=>allowed x=true) (log q).
Proof.
 unfold check;destruct (scalar_rejection _ _ _ _ _ _ _) as [[q|q]|] eqn:Run;try discriminate.
 intros H;repeat rewrite Bool.andb_true_iff in H;repeat rewrite Z.eqb_eq in H.
 exists q;split;[reflexivity|]. repeat apply conj;try tauto.
 - intros Impossible;exfalso;intuition lia.
 - intro Impossible;exfalso;exact (fixture_rejects pol Impossible).
 - exact (final_bytes _ _ _ _ _ _ _ _ Run).
 - apply Forall_forall;intros w InLog x Touch.
   assert (C:forallb covers (log q)=true) by tauto.
   apply (proj1 (forallb_forall _ _) C) in InLog;unfold covers in InLog.
   unfold touches in Touch;pose proof (proj1 (forallb_forall _ _) InLog
     (Z.to_nat (x-WriteTrace.address w)) ltac:(apply in_seq;lia)) as A.
   cbv beta in A;rewrite Z2Nat.id in A by lia;replace (WriteTrace.address w+(x-WriteTrace.address w)) with x in A by ring;exact A.
Qed.
