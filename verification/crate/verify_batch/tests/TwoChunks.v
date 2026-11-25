(* The first eight descriptors publish to indices 1..8. The ninth publishes
   to index 0 from a padded tail. Every S equals 2^256-1. *)
From Coq Require Import List ZArith Bool.
From Machine Require Import isa.Instructions execution.LinkedCalls execution.LinkedRun execution.WordSemantics
  memory.FlatMemory memory.WriteTrace.
From Ed25519Simd.VerifyBatch Require Import Policy ZipBytes DalekBytes.
From Ed25519Simd.VerifyBatch Require RejectedBatch Iteration FirstDispatch ChunkStaging.
Import ListNotations. Local Open Scope Z_scope.

Local Notation rows:=RejectedBatch.rows.
Local Notation out:=RejectedBatch.output.
Definition image x:=
 if x<?rows then RejectedBatch.image x
 else if x<?rows+360 then
   word_byte (nth (Z.to_nat (((x-rows) mod 40)/8))
      [rows+640;rows+512;rows+768;0;((x-rows)/40+1) mod 9] 0) ((x-rows) mod 8)
 else if (rows+544<=?x)&&(x<?rows+576) then 255
 else if (out<=?x)&&(x<?out+9) then 254
 else RejectedBatch.inputs x.
Definition initial:=CPU (put (regs RejectedBatch.initial) 6 9) (vectors RejectedBatch.initial) None image.
Definition windows pol pc text:=let masks:=fun _ _:nat=>true in
 bind (Iteration.begin pc text initial None) (fun staged=>
 bind (Iteration.dispatch pol 0 pc text initial staged masks) (fun first=>
 match first with
 | FirstDispatch.MoreChunks back=>bind (ChunkStaging.execute pc text 1 back) (fun next=>
   bind (Iteration.dispatch pol 0 pc text initial next masks) (fun last=>
   match last with FirstDispatch.Completed q=>Some(back,q) | _=>None end))
 | _=>None end)).
Definition check pol pc text:=match windows pol pc text with
 | Some(back,q)=>
   (mem(machine back) out=?254) &&
   forallb (fun j=>mem(machine back)(out+1+Z.of_nat j)=?0) (seq 0 8) &&
   (ip q=?RejectedBatch.ret) && (regs(machine q) 4%nat=?RejectedBatch.stack+8) &&
   (regs(machine q) 0%nat=?1) &&
   forallb (fun j=>mem(machine q)(out+Z.of_nat j)=?0) (seq 0 9) &&
   forallb (fun w=>forallb (fun k=> let x:=WriteTrace.address w+Z.of_nat k in
       (x<?out)||(out+9<=?x)||(x=?out)) (seq 0 (size w))) (skipn (length (log back)) (log q))
 | None=>false end.
Example zip_padded_back_edge:check Zip215 ZipBytes.address ZipBytes.symbol_bytes=true.
Proof. lazy;reflexivity. Qed.
Example dalek_padded_back_edge:check Dalek DalekBytes.address DalekBytes.symbol_bytes=true.
Proof. lazy;reflexivity. Qed.
