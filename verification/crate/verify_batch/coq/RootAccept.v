From Coq Require Import ZArith List Bool Lia.
From Machine Require Import isa.Instructions execution.WordBounds execution.WordSemantics execution.LinkedCalls execution.LinkedRun
 execution.ScalarBytes execution.ScalarWords execution.MappedFetch execution.InstructionRoute execution.AlignedRows memory.ByteMemory memory.WriteTrace memory.MemoryGeometry.
From Machine Require execution.MaskTransfer.
From Curve25519 Require Import Radix51.
From Ed25519Simd.Decode Require Import Limbs.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage BatchScalar BatchDecode KeySquare NativeScale.
From Ed25519Simd.VerifyBatch Require DecoderFrame DecoderKernel DecoderProduct RootMasks.
Import ListNotations. Local Open Scope Z_scope.

Definition load bias:=segment (base bias) text 5.
Definition move:=MaskTransfer.ToGpr 10 2.
Definition execute bias p bank:=bind (RootMasks.execute true bias p bank) (fun '(s,k)=>
 bind (load bias s) (fun u=>bind (RootMasks.execute false bias u k) (fun '(t,m)=> MaskTransfer.tick move t m))).
Definition bits sig e s j:=let q:=vectors s j in let u:=row s (point e sig) j in
 (high_test q 1 || high_test u 0 || high_test q (-1))%bool.

Theorem checked sig pol bias e p bank : placement e -> loaded pol bias (mem e) (writable e) ->
 ip p=base bias+952 -> accounted e (writable e) p -> regs(machine p) 7%nat=point e sig ->
 (forall j,vectors(machine p) j 29%nat=radix-1) ->
 exists q out,execute bias p bank=Some(q,out) /\ ip q=base bias+1076 /\ accounted e (writable e) q /\
 log q=log p /\ mem(machine q)=mem(machine p) /\
 (forall r,r<>10%nat -> regs(machine q) r=regs(machine p) r) /\
 (forall j i,(i<5)%nat -> vectors(machine q) j i=row (machine p) (point e sig) j i) /\
 (forall j i,(28<=i)%nat -> vectors(machine q) j i=vectors(machine p) j i) /\
 0<=regs(machine q) 10%nat<256 /\ forall j,(j<8)%nat ->
 Z.testbit (regs(machine q) 10%nat) (Z.of_nat j)=bits sig e (machine p) j /\
 out 4%nat j=high_test (vectors(machine p) j) (-1).
Proof.
 intros P Image PC Acc DI Mask;set (o:=base bias) in *;set (a:=point e sig) in *.
 destruct(RootMasks.checked true pol bias e p bank Image PC Acc Mask)
   as [s [ks [A [At [Log [M [G [High Q]]]]]]]].
 assert (Paid:accounted e (writable e) s) by (unfold accounted;rewrite Log,M;exact Acc).
 assert (Bound:linked text (AlignedRows.route false 996 0 7 0 5)) by (repeat constructor;vm_compute;discriminate || reflexivity).
 destruct(scratch_ok _ P) as [[L H] Al].
 destruct(AlignedRows.loads o _ 5 996 0 7 0 a (machine s) (LinkedRun.carry s) Bound
   ltac:(rewrite G,DI;ring) ltac:(apply point_aligned,Al) ltac:(unfold fits64,a,point,point_offset;destruct sig;change (Z.of_nat 5) with 5;lia))
   as [v [R [GV [MV [_ [Rows Other]]]]]].
 destruct(mapped_now _ _ _ Image _ _ _ Paid (decode_in pol)) as [Map Sep].
 destruct(at_segment _ _ _ o text 5 996 _ _ Paid At Map Sep R (Forall_nil _)) as [U More].
 set (mid:=LinkedRun.finish o s (State (Running 1030) v (LinkedRun.carry s),[])) in *.
 assert (VMask:forall j,vectors v j 29%nat=radix-1) by
   (intro j;rewrite Other by lia;rewrite High by discriminate;apply Mask).
 destruct(RootMasks.checked false pol bias e mid ks Image eq_refl More VMask)
   as [t [ms [B [End [LastLog [MT [GT [HT Valid]]]]]]]].
 assert (Flat:mem(machine t)=mem(machine p)).
 { rewrite MT;change (mem v=mem(machine p));now rewrite MV,M. }
 assert (Logs:log t=log p).
 { rewrite LastLog;change (log s++[]=log p);now rewrite app_nil_r,Log. }
 assert (Account:accounted e (writable e) t) by (unfold accounted;rewrite Flat,Logs;exact Acc).
 destruct(mapped_now _ _ _ Image _ _ _ Account (decode_in pol)) as [MapT _].
 assert (Fetched:mapped (mem(machine t)) (ip t) (MaskTransfer.encoding move)).
 { rewrite End;apply MaskTransfer.subimage with (text:=text) (off:=1072%nat);[exact MapT|change (1076<=2984)%nat;lia|vm_compute;reflexivity]. }
 pose proof(MaskTransfer.fetched move t ms ltac:(reflexivity) Fetched) as Transfer.
 set (value:=MaskTransfer.mask16(ms 2%nat));set (q:=Cursor (word(ip t+4)) (set (machine t) 10 value) (LinkedRun.carry t) (log t)) in *.
 assert (IP:ip q=o+1076).
 { change (word(ip t+4)=o+1076);rewrite End;change (word(o+1072+4)=o+1076);
   replace (o+1072+4) with (o+1076) by ring;apply word_fits;exact (DecoderProduct.address_fits pol bias e Image DecoderKernel.Carry 1076 ltac:(change (0<=1076<2984);lia)). }
 assert (Digit:forall i j,(i<5)%nat -> vectors v j i=row (machine p) a j i).
 { intros i j N;unfold row;rewrite <-M;apply Rows,N. }
 assert (Utest:forall j,high_test (vectors v j) 0=high_test (row (machine p) a j) 0).
 { intro j;unfold high_test;repeat rewrite Digit by lia;reflexivity. }
 assert (Bit:forall j,ms 2%nat j=((j<?8)%nat && bits sig e (machine p) j)%bool).
 { intro j;destruct(Valid j) as [Val _];destruct(Q j) as [Plus Neg];rewrite Val,Plus,Neg;
   unfold RootMasks.passed,bits;change (vectors(machine mid) j) with (vectors v j);rewrite Utest;fold a.
   destruct(Nat.ltb_spec j 8);[rewrite (proj2(Nat.ltb_lt j 16) ltac:(lia));reflexivity|now rewrite !orb_false_r,andb_false_r]. }
 exists q,ms;split;[unfold execute,load;fold o;rewrite A;cbn [bind];rewrite U;cbn [bind];change (bind (RootMasks.execute false bias mid ks) (fun '(t,m)=>MaskTransfer.tick move t m)=Some(q,ms));rewrite B;exact Transfer|].
 split;[exact IP|split;[exact Account|split;[exact Logs|split;[exact Flat|split]]]].
 - intros r N;change (put (regs(machine t)) 10 value r=regs(machine p) r);unfold put;rewrite (proj2(Nat.eqb_neq 10 r) ltac:(lia)),GT;
   change (regs v r=regs(machine p) r);now rewrite GV,G.
 - split;[intros j i N;change (vectors(machine t) j i=row (machine p) a j i);rewrite HT by lia;apply Digit,N|split].
   + intros j i N;change (vectors(machine t) j i=vectors(machine p) j i);rewrite HT by lia;change (vectors v j i=vectors(machine p) j i);
     rewrite Other by lia;apply High;lia.
   + split;[apply MaskTransfer.low_mask_byte;intros j J;rewrite Bit,(proj2(Nat.ltb_ge j 8) J);reflexivity|].
     intros j J;split;[change (Z.testbit value (Z.of_nat j)=bits sig e (machine p) j);unfold value;rewrite (proj2(MaskTransfer.kmov_value _) j ltac:(lia)),Bit,(proj2(Nat.ltb_lt j 8) J);reflexivity|].
     rewrite (proj2(Valid j)),(proj2(Q j));unfold RootMasks.passed;now rewrite (proj2(Nat.ltb_lt j 8) J).
Qed.

From Ed25519Simd.VerifyBatch Require NativeWords.
Lemma words bias p bank q out : well_formed(machine p) ->
 execute bias p bank=Some(q,out) -> well_formed(machine q).
Proof.
 intro W;unfold execute,load.
 destruct(RootMasks.execute true bias p bank) as [[s ks]|] eqn:A;[|discriminate];cbn [bind].
 destruct(segment _ _ _ s) as [u|] eqn:B;[|discriminate];cbn [bind].
 destruct(RootMasks.execute false bias u ks) as [[t ms]|] eqn:C;[|discriminate];cbn [bind].
 intro D;eapply NativeWords.mask_op;[|exact D];eapply RootMasks.words;[|exact C].
 eapply segment_wf;[|exact B];eapply RootMasks.words;eassumption.
Qed.
