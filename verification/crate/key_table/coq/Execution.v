From Coq Require Import ZArith List Bool Lia FSets.FMapPositive.
From Machine Require Import isa.Instructions.
From Curve25519.group Require Import Affine SignedMultiple Representation.
From Ed25519Simd Require Import Wide51.
From Ed25519Simd.KeyTable Require Import Pack Image Rows Advance.
Import ListNotations. Local Open Scope Z_scope.

(* Qword offsets are relative to RSI. A word records the number of completed
   cached additions and the source limb at that iteration. *)
Definition write := (Z * list (nat * word))%type.
Definition place epoch pos neg (e:event) : write :=
 let '(positive,off,ws):=e in ((if positive then pos else neg)+Z.of_nat off,
                              map (fun w=>(epoch,w)) ws).
Definition identity_writes base : list write :=
 [(base,repeat (0%nat,Literal 0) 8);(base+8,repeat (0%nat,Literal 0) 8);
  (base+16,repeat (0%nat,Literal 0) 4)] ++
 map (fun kv=>(base+fst kv,[(0%nat,Literal(snd kv))])) identity_values.
Definition load_indices (r:nat->nat->word) :=
 put (put (put r 28 (constant index0)) 29 (constant index8)) 30 (constant biases).
Definition branch t count left digit := match t with
 | MoreKeys=>negb (Nat.eqb left 0) | AlreadyStaged=>negb (Nat.eqb digit 1)
 | SingleKey=>Nat.eqb count 1 | LastMultiple=>Nat.eqb digit 8 end.

Fixpoint trace fuel count l left digit idptr pos neg epoch saved regs (writes:list write) :=
 match fuel with O=>None | S n=>
 let next left digit idptr pos neg epoch saved regs writes := match exit l with
 | Return=>Some writes
 | Fall dst | Jump _ dst=>trace n count dst left digit idptr pos neg epoch saved regs writes
 | Branch t yes no=>trace n count (if branch t count left digit then yes else no)
                         left digit idptr pos neg epoch saved regs writes end in
 match l with
 | Frame=>next count 0%nat (8*entry_size/8) (8*entry_size/8) (8*entry_size/8) 0%nat None initial []
 | Identity=>next (Nat.pred left) digit (idptr+table_size/8) pos neg epoch saved regs
   (writes++identity_writes idptr)
 | Start=>next left 1%nat idptr pos neg epoch saved regs writes
 | Multiple=>next left digit idptr (pos+entry_size/8) (neg-entry_size/8) epoch saved initial writes
 | Stage=>next left digit idptr pos neg epoch (Some epoch) regs writes
 | Bulk | Single=>let single:=match l with Single=>true|_=>false end in
   next left digit idptr pos neg epoch saved (fst(fold_left step (transpose single) (regs,[]))) writes
 | First | Remaining=>let '(r,events):=match l with First=>fold_left step first (load_indices regs,[])
   | _=>fold_left step rest (regs,[]) end in
   next left digit idptr pos neg epoch saved r (writes++map (place epoch pos neg) events)
 | Advance=>match saved with Some O=>
   next left (S digit) idptr pos neg (S epoch) saved regs writes | _=>None end
 | _=>next left digit idptr pos neg epoch saved regs writes end end.
Definition returning count := trace 128 count Frame 0%nat 0%nat 0 0 0 0%nat None initial [].
Fixpoint points incoming k w n := match n with O=>w | S t=>advance (incoming t) (points incoming k w t) (staged k w) end.
Definition resolve incoming k w nw := let '(n,t):=nw in eval (column k (points incoming k w n)) t.
Definition address (j:nat) d (i:nat) := 340*Z.of_nat j+20*(8+d)+Z.of_nat i.

Module Memory := PositiveMap.
Fixpoint write_words {A:Type} off (words:list A) (m:Memory.t A) :=
 match words with []=>m | v::tail=>write_words (off+1) tail (Memory.add (Z.to_pos(off+1)) v m) end.
Definition store_all (writes:list write) :=
 fold_left (fun m w=>write_words (fst w) (snd w) m) writes (Memory.empty _).
Definition lookup {A:Type} (m:Memory.t A) off :=
 if off <? 0 then None else Memory.find (Z.to_pos(off+1)) m.
Definition within count (ws:list write) := forallb (fun block=>
 (0<=?fst block) && (fst block+Z.of_nat(length(snd block)) <=? 340*Z.of_nat count)) ws.

Lemma words_after {A} (ws:list A) base x m : 0<=base -> base+Z.of_nat(length ws)<=x ->
 Memory.find (Z.to_pos(x+1)) (write_words base ws m)=Memory.find (Z.to_pos(x+1)) m.
Proof.
 revert base m;induction ws as [|v ws IH];intros base m B X;[reflexivity|].
 cbn [write_words];cbn [length] in X;rewrite Nat2Z.inj_succ in X.
 rewrite IH by lia;apply Memory.gso;intro E;apply Z2Pos.inj in E;lia.
Qed.
Lemma outside count writes x : within count writes=true -> (x<0 \/ 340*Z.of_nat count<=x) ->
 lookup (store_all writes) x=None.
Proof.
 intros Good [L|U];unfold lookup;destruct (Z.ltb_spec x 0);try reflexivity;try lia.
 unfold store_all;rewrite <- (Memory.gempty (nat*word)%type (Z.to_pos(x+1))).
 generalize (Memory.empty (nat*word)%type);induction writes as [|[base ws] rest IH];intro m.
 - reflexivity.
 - cbn [within forallb] in Good;apply andb_true_iff in Good as [B R].
   cbn [fold_left];rewrite IH by exact R. apply words_after.
   all:apply andb_true_iff in B as [Low High];apply Z.leb_le in Low,High;cbn [fst snd] in *;lia.
Qed.

Definition expected j d i := if d=?0 then (0%nat,Literal(identity_word (Z.of_nat i)))
 else (Nat.pred (Z.to_nat(Z.abs d)),signed_word (0<?d) i j).
Definition word_dec : forall x y:word, {x=y}+{x<>y}.
Proof. decide equality;auto using Nat.eq_dec,Z.eq_dec. Defined.
Definition matches m j d i := match lookup m (address j d i) with
 | Some (n,w)=>let '(e,t):=expected j d i in Nat.eqb n e &&
 (if word_dec w t then true else false) | None=>false end.
Definition complete count writes :=
 let m:=store_all writes in forallb (fun j=>forallb (fun slot=>forallb
 (matches m j (Z.of_nat slot-8)) (seq 0 20)) (seq 0 17)) (seq 0 count).
Definition replay count := match returning count with
 | Some ws=>within count ws && complete count ws | None=>false end.
Lemma replay_checked count : count=1%nat \/ count=8%nat -> replay count=true.
Proof. intros [->| ->];vm_compute;reflexivity. Qed.

Local Opaque returning store_all lookup expected.
Lemma returns count : count=1%nat \/ count=8%nat -> exists ws,
 returning count=Some ws /\ within count ws=true /\
 forall j d i,(j<count)%nat -> -8<=d<=8 -> (i<20)%nat ->
 lookup (store_all ws) (address j d i)=Some(expected j d i).
Proof.
 intro Count;pose proof(replay_checked _ Count) as H;unfold replay in H.
 destruct(returning count) as [ws|] eqn:R;[|discriminate].
 apply andb_true_iff in H as [B C];exists ws;split;[reflexivity|split;auto].
 intros j d i J D I. unfold complete in C.
 apply forallb_forall with (x:=j) in C;[|apply in_seq;lia].
 apply forallb_forall with (x:=Z.to_nat(d+8)) in C;[|apply in_seq;lia].
 apply forallb_forall with (x:=i) in C;[|apply in_seq;lia].
 replace (Z.of_nat (Z.to_nat(d+8))-8) with d in C by lia.
 unfold matches in C;destruct (lookup _ _) as [[n v]|];[|discriminate].
 destruct (expected j d i) as [e t];apply andb_true_iff in C as [N T].
 apply Nat.eqb_eq in N. destruct (word_dec v t);congruence.
Qed.
