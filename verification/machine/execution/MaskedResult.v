From Coq Require Import List ZArith Bool Lia.
From Machine Require Import isa.X86 isa.Instructions isa.ProgramLayout isa.VectorMoves execution.WordBounds
 execution.WordSemantics execution.LinkedCalls execution.LinkedRun execution.MappedFetch memory.ByteMemory memory.FlatMemory.
From Machine Require execution.ScalarBytes execution.ScalarWords execution.MaskTransfer execution.MaskedWords.
Import ListNotations. Local Open Scope Z_scope.

(* Straight-line, store-free instructions on the architectural predicate bank.
   A masked vector destination merges inactive lanes with its old value. *)
Inductive op :=
 | Invert (d a:nat) | Exclusive (d a b:nat) | FromGpr (d r:nat)
 | TestBroadcast (d a:nat) (target:Z)
 | LoadRow (d k base:nat) (offset:Z) | Subtract (d k a b:nat)
 | BroadcastGpr (d r:nat) | WidenWords (d:nat) (target:Z)
 | AddQ (d k a b:nat) | MaskBytes (d k:nat) | AbsBytes (d a:nat).

(* VPMOVZXWQ reads sixteen contiguous bytes at RIP+disp32. *)
Definition widen_encoding d disp :=
 let r:=Z.of_nat d in
 match prefix 2 1 r 0 5 with
 | a::b::c::rest=>a::b::(c-128)::rest++[0x34;modrm 0 r 5]++le32 disp
 | _=>[] end.

Definition mask_qword (bits:nat->bool) (lane:nat) :=
 read_word (fun i=>if bits (8*lane+Z.to_nat i)%nat then 255 else 0) 0.
Definition abs_byte x:=if x<?128 then x else 256-x.
Definition abs_qword x:=read_word (fun i=>abs_byte (word_byte x i)) 0.
Lemma abs_byte_range x : 0<=x<256 -> 0<=abs_byte x<256.
Proof. unfold abs_byte;destruct (Z.ltb_spec x 128);lia. Qed.
Lemma mask_memory (bits:nat->bool) lane : byte_memory (fun i=>if bits (8*lane+Z.to_nat i)%nat then 255 else 0).
Proof. intros i;destruct (bits _);lia. Qed.
Lemma abs_memory x : byte_memory (fun i=>abs_byte (word_byte x i)).
Proof. intro i;apply abs_byte_range,word_byte_bound. Qed.
Lemma abs_mask_byte bits lane j : (j<8)%nat ->
 word_byte (abs_qword (mask_qword bits lane)) (Z.of_nat j)=Z.b2z(bits (8*lane+j)%nat).
Proof.
 intro J;unfold abs_qword,mask_qword;rewrite read_word_byte by (apply abs_memory || lia).
 rewrite Z.add_0_l,read_word_byte by (apply mask_memory || lia).
 rewrite Z.add_0_l,Nat2Z.id;destruct (bits _);reflexivity.
Qed.

Definition encode pc op:=match op with
 | Invert d a=>[0xc5;0xf8;0x44;modrm 3 (Z.of_nat d) (Z.of_nat a)]
 | Exclusive d a b=>[0xc5;0x84+8*(15-Z.of_nat a);0x47;modrm 3 (Z.of_nat d) (Z.of_nat b)]
 | FromGpr d r=>(if (r<?8)%nat then [0xc5;0xf8] else [0xc4;0xc1;0x78])++
      [0x92;modrm 3 (Z.of_nat d) (Z.of_nat r)]
 | TestBroadcast d a t=>let emit:=rip_bcst 2 1 0x27 d a in emit (MaskedWords.relative pc t emit)
 | LoadRow d k b off=>MaskedWords.writemask k (row_encoding (Row false d b off))
 | Subtract d k a b=>MaskedWords.writemask k (Arithmetic.encode_vpsubq d a b)
 | BroadcastGpr d r=>rr 2 1 0x7c d 0 r
 | WidenWords d t=>widen_encoding d (MaskedWords.relative pc t (widen_encoding d))
 | AddQ d k a b=>MaskedWords.encode pc (MaskedWords.Add d k a b)
 | MaskBytes d k=>Packed.rr_w0 2 2 0x28 d 0 k
 | AbsBytes d a=>Packed.rr_w0 2 1 0x1c d 0 a
 end.
Definition valid pc op:=let kr k:=(k<?8)%nat in let vr r:=(r<?32)%nat in match op with
 | Invert d a=>kr d && kr a | Exclusive d a b=>kr d && kr a && kr b
 | FromGpr d r=>kr d && (r<?16)%nat
 | TestBroadcast d a t=>kr d && vr a && signed 32 (MaskedWords.relative pc t (rip_bcst 2 1 0x27 d a))
 | LoadRow d k b off=>vr d && kr k && (b<?16)%nat && signed 32 off
 | Subtract d k a b | AddQ d k a b=>vr d && kr k && vr a && vr b
 | BroadcastGpr d r=>vr d && (r<?16)%nat
 | WidenWords d t=>vr d && signed 32 (MaskedWords.relative pc t (widen_encoding d))
 | MaskBytes d k=>vr d && kr k | AbsBytes d a=>vr d && vr a end.

Lemma widen_target pc d t : valid pc (WidenWords d t)=true ->
 let bs:=encode pc (WidenWords d t) in pc+Z.of_nat(length bs)+displacement32(firstn 4 (skipn 6 bs))=t.
Proof. intros V;apply andb_true_iff in V as [_ Range];cbv zeta.
 change (pc+10+displacement32(le32 (MaskedWords.relative pc t (widen_encoding d)))=t).
 rewrite displacement32_le32 by exact Range;change (pc+10+(t-(pc+10))=t);ring. Qed.
Definition set_mask (ks:MaskTransfer.bank) d n f:=put ks d (fun j=>(j<?n)%nat && f j).
Definition merge s (ks:MaskTransfer.bank) d k f:=ScalarBytes.vector_dest s d (fun j=>
 if ((k=?0)%nat || ks k j)%bool then f j else vectors s j d).
Definition step origin s (ks:MaskTransfer.bank) op : option (cpu*MaskTransfer.bank) :=match op with
 | Invert d a=>Some(s,set_mask ks d 16 (fun j=>negb(ks a j)))
 | Exclusive d a b=>Some(s,set_mask ks d 16 (fun j=>xorb (ks a j) (ks b j)))
 | FromGpr d r=>Some(s,set_mask ks d 16 (fun j=>Z.testbit (regs s r) (Z.of_nat j)))
 | TestBroadcast d a t=>let rhs:=read_word (mem s) (word(origin+t)) in
    Some(s,set_mask ks d 8 (fun j=>negb (Z.land (vectors s j a) rhs=?0)))
 | LoadRow d k b off=>if (word(regs s b+off) mod 64=?0) then
    Some(merge s ks d k (fun j=>ScalarBytes.vector_load s j b off),ks) else None
 | Subtract d k a b=>Some(merge s ks d k (fun j=>Arithmetic.vpsubq (vectors s j a) (vectors s j b)),ks)
 | BroadcastGpr d r=>Some(ScalarBytes.vector_dest s d (fun _=>regs s r),ks)
 | WidenWords d t=>Some(ScalarBytes.vector_dest s d (fun j=>read_le 2 (mem s) (word(origin+t)+2*Z.of_nat j)),ks)
 | AddQ d k a b=>Some(merge s ks d k (fun j=>Arithmetic.vpaddq (vectors s j a) (vectors s j b)),ks)
 | MaskBytes d k=>Some(ScalarBytes.vector_dest s d (mask_qword (ks k)),ks)
 | AbsBytes d a=>Some(ScalarBytes.vector_dest s d (fun j=>abs_qword (vectors s j a)),ks)
 end.
Fixpoint assemble pc ops:=match ops with []=>Some [] | op::rest=>
 if valid pc op then let bytes:=encode pc op in option_map (app bytes) (assemble (pc+Z.of_nat(length bytes)) rest) else None end.
Fixpoint evaluate origin s ks ops:=match ops with []=>Some(s,ks) | op::rest=>
 bind (step origin s ks op) (fun '(t,k)=>evaluate origin t k rest) end.
Definition execute origin ops p ks:=bind (assemble (ip p-origin) ops) (fun bytes=>
 if list_eq_dec Z.eq_dec (snapshot (mem(machine p)) (ip p) (length bytes)) bytes then
 option_map (fun '(v,k)=>(Cursor (word(ip p+Z.of_nat(length bytes))) v (carry p) (log p),k))
  (evaluate origin (machine p) ks ops) else None).

Lemma mapped_block origin off ops p ks bytes v k : ip p=origin+off ->
 assemble off ops=Some bytes -> mapped (mem(machine p)) (ip p) bytes ->
 evaluate origin (machine p) ks ops=Some(v,k) ->
 execute origin ops p ks=Some(Cursor (word(ip p+Z.of_nat(length bytes))) v (carry p) (log p),k).
Proof. intros PC Enc Map Eval;unfold execute;replace (ip p-origin) with off by lia;rewrite Enc;cbn [bind];
 rewrite (snapshot_mapped _ _ _ Map);destruct(list_eq_dec _ _ _);[now rewrite Eval|contradiction]. Qed.

Lemma stable origin ops : forall s ks v k, evaluate origin s ks ops=Some(v,k) ->
 regs v=regs s /\ mem v=mem s /\ flag v=flag s /\ (well_formed s -> well_formed v).
Proof.
 induction ops as [|op tail IH];intros s ks v k Exec;[injection Exec as <- <-;auto|].
 cbn [evaluate] in Exec;destruct(step origin s ks op) as [[u bank]|] eqn:S;[|discriminate].
 cbn [bind] in Exec;destruct(IH _ _ _ _ Exec) as [G [M [F W]]];rewrite G,M,F.
 destruct op as [d a|d a b|d r|d a target|d mask base off|d mask a b|d r|d target|d mask a b|d mask|d a];cbn [step] in S;try (destruct (_=?0) eqn:A;[|discriminate]);
 injection S as <- <-.
 all: split;[reflexivity|split;[reflexivity|split;[reflexivity|]]];auto.
 - intro H;apply W;destruct H as [R [Vec Bytes]];split;[exact R|split;[|exact Bytes]].
   intros j n J;unfold merge;cbn [ScalarBytes.vector_dest vectors];unfold put;destruct (d=?n)%nat;[|apply Vec,J].
   destruct ((mask=?0)%nat || ks mask j);[apply read_word_bound,Bytes|apply Vec,J].
 - intro H;apply W;destruct H as [R [Vec Bytes]];split;[exact R|split;[|exact Bytes]].
   intros j n J;unfold merge;cbn [ScalarBytes.vector_dest vectors];unfold put;destruct (d=?n)%nat;[|apply Vec,J].
   destruct ((mask=?0)%nat || ks mask j);[apply low64_word|apply Vec,J].
 - intro H;apply W,ScalarWords.set_vector_words;[exact H|intros;apply H].
 - intro H;apply W,ScalarWords.set_vector_words;[exact H|intros j J].
   pose proof(read_le_bound 2 _ (word(origin+target)+2*Z.of_nat j) (proj2(proj2 H))) as B;change (256^Z.of_nat 2) with 65536 in B;cbv beta;unfold word64;split;[exact (proj1 B)|eapply Z.lt_trans;[exact (proj2 B)|lia]].
 - intro H;apply W,ScalarWords.set_vector_words;[exact H|intros j J];destruct ((mask=?0)%nat || ks mask j);[apply low64_word|apply H,J].
 - intro H;apply W,ScalarWords.set_vector_words;[exact H|intros;apply read_word_bound,mask_memory].
 - intro H;apply W,ScalarWords.set_vector_words;[exact H|intros;apply read_word_bound,abs_memory].
Qed.

Fixpoint rows d k base off n:=match n with
 | O=>[] | S tail=>LoadRow d k base off::rows (S d) k base (off+64) tail end.

(* No masked-off lane is read. All enabled qwords come from the byte
   memory at the start of the block, even when different lanes disagree. *)
Lemma load_rows origin n : forall d k b off a s ks,
 regs s b+off=a -> a mod 64=0 -> 0<=a -> a+64*Z.of_nat n<=2^64 ->
 exists t,evaluate origin s ks (rows d k b off n)=Some(t,ks) /\
 regs t=regs s /\ mem t=mem s /\
 (forall i j,(i<n)%nat -> vectors t j (d+i)%nat=
  if ((k=?0)%nat || ks k j)%bool then read_word (mem s) (a+64*Z.of_nat i+8*Z.of_nat j) else vectors s j (d+i)%nat) /\
 forall r j,(r<d \/ d+n<=r)%nat -> vectors t j r=vectors s j r.
Proof.
 induction n as [|n IH];intros d k b off a s ks Base Al L H.
 - exists s;repeat split;intros;reflexivity || lia.
 - set (u:=merge s ks d k (fun j=>ScalarBytes.vector_load s j b off)).
   assert (Addr:word(regs s b+off)=a) by (rewrite Base;apply word_fits;unfold word64;lia).
   assert (Op:step origin s ks (LoadRow d k b off)=Some(u,ks)) by (cbn [step];now rewrite Addr,Al).
   destruct(IH (S d) k b (off+64) (a+64) u ks
     ltac:(change (regs s b+(off+64)=a+64);lia)
     ltac:(replace (a+64) with (a+1*64) by ring;rewrite Z.mod_add by lia;exact Al)
     ltac:(lia) ltac:(lia)) as [t [Run [G [M [Data Other]]]]].
   exists t;split;[cbn [rows evaluate];rewrite Op;exact Run|split;[exact G|split;[exact M|split]]].
   + intros [|i] j N.
     * rewrite Nat.add_0_r,Other by lia;unfold u,merge;cbn [ScalarBytes.vector_dest vectors];unfold put;rewrite Nat.eqb_refl.
       destruct ((k=?0)%nat || ks k j);[unfold ScalarBytes.vector_load;rewrite Addr;f_equal;ring|reflexivity].
     * replace (d+S i)%nat with (S d+i)%nat by lia;rewrite Data by lia.
       replace (a+64+64*Z.of_nat i+8*Z.of_nat j) with (a+64*Z.of_nat(S i)+8*Z.of_nat j) by lia.
       destruct ((k=?0)%nat || ks k j);[reflexivity|unfold u,merge;cbn [ScalarBytes.vector_dest vectors];unfold put;now rewrite (proj2(Nat.eqb_neq d (S d+i)) ltac:(lia))].
   + intros r j R;rewrite Other by lia;unfold u,merge;cbn [ScalarBytes.vector_dest vectors];unfold put;now rewrite (proj2(Nat.eqb_neq d r) ltac:(lia)).
Qed.
