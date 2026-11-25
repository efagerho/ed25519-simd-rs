From Coq Require Import ZArith.
From Machine Require Import execution.LinkedCalls execution.LinkedRun.
From Ed25519Simd.VerifyBatch Require Import Policy Return LoadedImage.
From Ed25519Simd.VerifyBatch Require ZipVerdict.

Definition finish pol bias product stop:=match pol with
 | Dalek=>stop=product
 | Zip215=>exists child ret bank ks,ZipTorsionCall.execute bias product=Some child /\
     ZipTorsion.execute bias child bank=Some(ret,ks) /\ ZipVerdict.execute bias ret=Some stop end.
Definition observed pol bias screen stop:=exists product,ScoreProduct.observed pol bias screen product /\ finish pol bias product stop.
Definition selected pol bias parent e stop:=exists product,ScoreProduct.selected pol bias e product /\
 match pol with Dalek=>stop=product | Zip215=>ZipVerdict.result bias parent e stop end.

Theorem checked pol bias parent e h r caller score screen :
 placement e -> loaded pol bias (mem e) (writable e) -> ProductRun.geometry (HashLayout.chunk pol e bias) ->
 Tables.mapped e bias -> Candidate.constants e -> HashLayout.active pol e ->
 ScoreStart.reached pol bias parent e h r caller score -> ScoreProgress.observed pol bias score screen ->
 ScoreProduct.rejected pol screen=false ->
 (exists stop,observed pol bias screen stop) /\ (forall stop,observed pol bias screen stop ->
   accounted e (writable e) stop /\ selected pol bias parent e stop).
Proof.
 intros P I G M T Active Start Screen On.
 destruct(ScoreProduct.with_origin _ _ _ _ _ _ _ _ _ P I G M T Active Start Screen On) as [[v Run] All].
 destruct pol.
 - assert (Zip:forall p,ScoreProduct.observed Zip215 bias screen p ->
     (exists t,finish Zip215 bias p t) /\ (forall t,finish Zip215 bias p t -> ZipVerdict.result bias parent e t)).
   { intros p R;destruct(All _ R) as [_ [PC [cand [Origin [Entry Data]]]]];change (cand=score) in Origin;subst cand.
     destruct(ZipTorsionCall.checked _ _ _ _ _ P I (ZipResume.checked _ _ _ _ _ _ _ _ P Start PC Entry Data)) as [q [Call Child]].
     split.
     - destruct(ZipTorsion.checked _ _ _ _ _ (fun _ _:nat=>false) P I Child) as [ret [ks [Done [_ Bits]]]].
       destruct(ZipVerdict.checked _ _ _ _ _ P I Bits) as [t [Tail _]];exists t,q,ret,(fun _ _:nat=>false),ks;auto.
     - intros t [child [ret [bank [ks [C [B End]]]]]];rewrite Call in C;injection C as <-.
       destruct(ZipTorsion.checked _ _ _ _ _ bank P I Child) as [u [k [Return [_ Bits]]]].
       rewrite B in Return;injection Return as Eq _;subst u.
       destruct(ZipVerdict.checked _ _ _ _ _ P I Bits) as [z [Return Q]];rewrite End in Return;injection Return as <-;exact Q. }
   split;[destruct(proj1(Zip _ Run)) as [t F];exists t,v;auto|].
   intros t [p [R F]];pose proof(proj2(Zip _ R) _ F) as Result.
   destruct(ZipVerdict.entry _ _ _ _ Result) as [u [m Tail]].
   split;[exact (ScoreTail.writes _ _ _ _ _ _ Tail)|exists p;split;[|exact Result]].
   destruct(All _ R) as [_ [PC [cand [_ C]]]];split;[exact PC|now exists cand].
 - split;[exists v,v;split;[exact Run|reflexivity]|].
   intros t [p [R ->]];destruct(All _ R) as [Paid [PC [cand [_ C]]]];split;[exact Paid|].
   exists p;split;[split;[exact PC|now exists cand]|reflexivity].
Qed.
