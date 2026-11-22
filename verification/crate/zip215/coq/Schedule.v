From Coq Require Import List Bool ZArith Lia.
From Ed25519Simd.Zip215 Require Import Caller.
Import ListNotations. Local Open Scope nat_scope.

(* (chunks submitted to scoring, occupancy after return). *)
Definition flush_counts n := match successor Flush Count (n=?0) false with
 | Some Empty=>Some (0,n)
 | Some Setup=>let st:=Staging.step (Staging.step (Staging.initial n 0 true) (Staging.Mov 3 7)) (Staging.ClearCount 3) in
   match Staging.occupancy st with Staging.Number z=>Some(n,Z.to_nat z) | _=>None end
 | _=>None end.
Definition push_counts n pad :=
 let st:=fold_left Staging.step Staging.push_ops (Staging.initial n pad true) in
 match Staging.occupancy st,exit_of Enqueue with
 | Staging.Number z, Jump Eq _ (Entry Flush)=>let occupied:=Z.to_nat z in
   if Staging.zf st then flush_counts occupied else Some (0,occupied)
 | _,_=>None end.
Definition queue_lifecycle := (forall n,n<=8 -> flush_counts n=Some(n,0)) /\
 forall n pad,n<8 -> pad<4 -> push_counts n pad=Some(if S n=?8 then (8,0) else (0,S n)).
Lemma queue_lifecycle_ok : queue_lifecycle.
Proof.
 split;[intros [|n] _;reflexivity|]. intros n pad N P.
 do 8 (destruct n as [|n];[do 4 (destruct pad as [|pad];[vm_compute;reflexivity|]);lia|]);lia.
Qed.

(* The probe has no authority to set an acceptance bit. Its read-only
   field operation can return any mask, including a false positive. *)
Fixpoint probe fuel l n i hits (matches:nat->bool) : option bool :=
 match fuel with O=>None | S gas=>
 let go e b i h:=match successor Flush l e b with
 | Some dst=>probe gas dst n i h matches | None=>None end in
 match l with
 | Count=>go (n=?0) false i hits | Empty=>Some false
 | Setup=>go (n=?2) (n<?2) i hits | StartProbe=>go false false 0 2
 | Probe=>if i<?n then go (matches i) false i hits else None
 | ProbeHit=>go (hits=?1) false i (pred hits)
 | AdvanceProbe=>go (S i=?n) false (S i) hits
 | Recompress=>Some true | NoExact | Resolve=>Some false | _=>None end end.

(* A source carries the chunk that supplied a mask byte, including the
   starting chunk of a paired decode. Unwritten stack bytes are explicit. *)
Inductive source := ExactByte (i:nat) | CheckedByte (start:nat)(pair high:bool).
Definition stores := list (nat*source).
Definition update stack i (v:source) j := if j=?i then Some v else stack j.
Fixpoint resolve fuel l n (full:nat->bool) i pair (stack:nat->option source) (writes:stores)
 : option stores := match fuel with O=>None | S gas=>
 let go e b i pair stack writes:=match successor Flush l e b with
 | Some dst=>resolve gas dst n full i pair stack writes | None=>None end in
 match l with
 | Resolve=>go false false 0 false (fun j=>Some(ExactByte j)) []
 | Chunk=>if i<?n then go (full i) false i pair stack writes else None
 | ChooseOne=>go (S i=?n) (S i<?n) i false stack writes
 | Adjacent=>if S i<?n then go (full (S i)) false i pair stack writes else None
 | ChoosePair=>go false false i true stack writes
 | Check=>if i+(if pair then 2 else 1)<=?n then go pair false i pair stack writes else None
 | SaveOne=>go false false i pair (update stack i (CheckedByte i pair false)) writes
 | SavePair=>go false false (S i) pair
    (update (update stack i (CheckedByte i pair false)) (S i) (CheckedByte i pair true)) writes
 | Next=>go (S i=?n) (S i<?n) (S i) pair stack writes
 | StartScore=>go false false 0 pair stack writes
 | Score=>match stack i with Some v=>go false false i pair stack ((i,v)::writes) | None=>None end
 | NextScore=>go (S i=?n) (S i<?n) (S i) pair stack writes
 | Restore=>Some(rev writes) | _=>None end end.

Definition run (pattern:list bool) := match pattern with []=>Some [] | _=>
 resolve 128 Resolve (length pattern) (fun i=>nth i pattern false) 0 false (fun _=>None) [] end.
Definition origin n (full:nat->bool) i s := match s with
 | ExactByte j=>(i=?j) && full j
 | CheckedByte j paired high=>(i=?j+(if high then 1 else 0)) &&
   (negb high||paired) && (j+(if paired then 2 else 1)<=?n) end.
Definition checked pattern := match run pattern with None=>false | Some writes=>
 (if list_eq_dec Nat.eq_dec (map fst writes) (seq 0 (length pattern)) then true else false) &&
 forallb (fun w=>origin (length pattern) (fun i=>nth i pattern false) (fst w)(snd w)) writes end.

Fixpoint patterns n : list(list bool) := match n with O=>[[]] | S k=>
 let smaller:=patterns k in map (cons false) smaller ++ map (cons true) smaller end.
Lemma enumerated xs : In xs (patterns(length xs)).
Proof.
 induction xs as [|b xs IH];[simpl;auto|]. cbn [length patterns].
 apply in_or_app;destruct b;[right|left];apply in_map;exact IH.
Qed.
Lemma all_checked xs : length xs<=8 -> checked xs=true.
Proof.
 intro N. assert (C:forallb (fun n=>forallb checked (patterns n)) (seq 0 9)=true)
 by (vm_compute;reflexivity).
 apply forallb_forall with (x:=length xs) in C;[|apply in_seq;lia].
 apply forallb_forall with (x:=xs) in C;auto using enumerated.
Qed.
Lemma probe_total xs : length xs<=8 ->
 exists use_exact, probe 52 Count (length xs) 0 0 (fun i=>nth i xs false)=Some use_exact.
Proof.
 intro N. set (runs:=fun ys:list bool=>match probe 52 Count (length ys) 0 0 (fun i=>nth i ys false)
   with Some _=>true | None=>false end).
 assert (C:forallb (fun n=>forallb runs (patterns n)) (seq 0 9)=true) by (vm_compute;reflexivity).
 apply forallb_forall with (x:=length xs) in C;[|apply in_seq;lia].
 apply forallb_forall with (x:=xs) in C;[|apply enumerated].
 unfold runs in C. destruct (probe _ _ _ _ _ _) as [b|];[eauto|discriminate].
Qed.

(* Scatter invalid metadata returns failure before the offending store. With
   valid metadata, compare the shifted EAX to the original mask at each lane. *)
Record lanes := Lanes { active:nat; index:nat->nat; eligible:nat->bool }.
Definition positions m len := active m<=8 /\ forall j,j<active m -> index m j<len.
Definition write (out:nat->bool) at_ v i := if i=?at_ then v else out i.
Definition takes l e below dest := match successor Scatter l e below with
 | Some dst=>label_beq dst dest | None=>false end.
Fixpoint scatter_loop n j m len (mask:Z) out := match n with O=>Some out | S t=>
 if takes ReadIndex (index m j=?len) (index m j<?len) WriteLane &&
    takes WriteLane (S j=?active m) (S j<?active m) (match t with O=>Success | _=>ReadIndex end)
 then scatter_loop t (S j) m len (Z.shiftr mask 1)
 (write out (index m j) (eligible m j && Z.testbit mask 0)) else None end.
Definition scatter m len mask out := if takes LaneCount (active m=?8) (active m<?8) StartLanes &&
    takes StartLanes (active m=?0) false (match active m with O=>Success | _=>ReadIndex end)
 then scatter_loop (active m) 0 m len mask out else None.
Fixpoint place n j m (verdict:nat->bool) out := match n with O=>out | S t=>
 place t (S j) m verdict (write out (index m j) (eligible m j && verdict j)) end.
Lemma scatter_lanes m len mask out verdict : positions m len ->
 (forall j,j<active m -> Z.testbit mask (Z.of_nat j)=verdict j) ->
 scatter m len mask out=Some(place (active m) 0 m verdict out).
Proof.
 intros [N I] V. unfold scatter.
 assert (Ok:takes LaneCount (active m=?8) (active m<?8) StartLanes &&
   takes StartLanes (active m=?0) false (match active m with O=>Success | _=>ReadIndex end)=true).
 { clear -N. destruct (active m) as [|a];[reflexivity|].
   do 8 (destruct a as [|a];[reflexivity|]);lia. }
 rewrite Ok.
 assert (Loop:forall n j bits out, n+j=active m ->
  (forall k,k<n -> Z.testbit bits (Z.of_nat k)=verdict(j+k)) ->
  scatter_loop n j m len bits out=Some(place n j m verdict out)).
 { induction n;intros j bits o A B;[reflexivity|]. cbn [scatter_loop place].
   assert (Idx:(index m j <? len)=true) by (apply Nat.ltb_lt,I;lia). rewrite Idx.
   assert (To:takes WriteLane (S j=?active m) (S j<?active m) (match n with O=>Success | _=>ReadIndex end)=true).
   { destruct n;[assert (S j=active m) by lia;rewrite H,Nat.eqb_refl,Nat.ltb_irrefl;reflexivity|].
     assert ((S j<?active m)=true) by (apply Nat.ltb_lt;lia);rewrite H;reflexivity. }
   rewrite To. cbn [takes successor exit_of following order label_beq andb negb].
   specialize (B 0 ltac:(lia)) as Low. rewrite Nat.add_0_r in Low.
   change (Z.of_nat 0) with 0%Z in Low. rewrite Low. apply IHn;[lia|].
   intros k K. rewrite Z.shiftr_spec by lia. replace (Z.of_nat k+1)%Z with (Z.of_nat(S k)) by lia.
   replace (S j+k) with (j+S k) by lia. apply B;lia. }
 apply Loop;[lia|]. intros;apply V;auto.
Qed.
