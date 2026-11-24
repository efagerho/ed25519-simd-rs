From Coq Require Import List ZArith.
From Machine Require Import execution.Blocks memory.MemoryTrace memory.FlatMemory memory.WriteTrace.
Import ListNotations. Local Open Scope Z_scope.

(* Advance by the emitted instruction length, including register-only fragments
   which can contain several instructions but cannot store to memory. *)
Definition at_pc {A} (ip:Z) (xs:list A) := map (fun x=>(ip,x)) xs.
Fixpoint body_at p l c ip ops : option (control * list (Z * effect)) :=
 match ops with []=>Some (c,[]) | op::tail=>
 match exec_op p l c op with
 | Some (mid,es)=>option_map (fun '(last,rest)=>(last,at_pc ip es++rest))
      (body_at p l mid (ip+Z.of_nat(length(op_bytes p op))) tail)
 | None=>None end end.
Definition dispatch_at slide p l c := match rip c with At pc=>
 match lookup (sections p) pc with Some b=>
 match body_at p l c (slide+pc) (body b) with Some (mid,es)=>
 let ip:=slide+pc+Z.of_nat(length(flat_map (op_bytes p) (body b))) in
 option_map (fun '(next,ts)=>(next,map (fun '(a,e)=>(a,DataOp e)) es++at_pc ip ts))
   (transfer_recorded l mid (after p b) (terminator b))
 | None=>None end | None=>None end | _=>None end.
Definition run slide fuel p l := walk (dispatch_at slide p l) fuel.

Lemma forget_pc {A} ip (xs:list A) : map snd (at_pc ip xs)=xs.
Proof. unfold at_pc;induction xs;cbn;congruence. Qed.
Lemma body_projection p l ops : forall c ip, exec_body p l c ops =
 option_map (fun '(last,es)=>(last,map snd es)) (body_at p l c ip ops).
Proof.
 induction ops as [|op tail IH];intros c ip;[reflexivity|]. cbn [exec_body body_at].
 destruct (exec_op _ _ _ _) as [[mid es]|];[|reflexivity].
 rewrite (IH mid (ip+Z.of_nat(length(op_bytes p op)))).
 destruct (body_at _ _ _ _ _) as [[last rest]|];[|reflexivity].
 cbn;rewrite map_app,forget_pc;reflexivity.
Qed.
Lemma singleton_map {A B} (f:A->B) xs : flat_map (fun x=>[f x]) xs=map f xs.
Proof. induction xs;cbn;congruence. Qed.

Theorem run_projection slide fuel p l c : record_path fuel p l c =
 option_map (fun '(last,es)=>(last,map snd es)) (run slide fuel p l c).
Proof.
 unfold record_path,run.
 rewrite (walk_project (fun x:Z*event=>[snd x]) (dispatch_at slide p l) (dispatch_recorded p l)).
 - destruct (walk _ _ _) as [[last es]|];cbn;[rewrite singleton_map|];reflexivity.
 - intro state;unfold dispatch_recorded,dispatch_at.
   destruct (rip state) as [pc| |];try reflexivity.
   destruct (lookup _ _) as [b|];[|reflexivity].
   rewrite (body_projection p l (body b) state (slide+pc)).
   destruct (body_at _ _ _ _ _) as [[mid es]|];[|reflexivity].
   cbn [option_map]. destruct (transfer_recorded _ _ _ _) as [[last ts]|];[|reflexivity].
   cbn [option_map]. rewrite singleton_map,map_app,forget_pc,!map_map.
   f_equal;f_equal;f_equal;apply map_ext;intros [a e];reflexivity.
Qed.

Fixpoint stores p loc d (es:list (Z*event)) := match es with
 | []=>[] | (ip,e)::rest=>block_store loc ip e d ++ stores p loc (next_data p d e) rest end.
Lemma replay_projection p loc es : forall d m,
 WriteTrace.replay m (stores p loc d es)=FlatMemory.replay p loc (map snd es) d m.
Proof.
 induction es as [|[ip e] t IH];intros;[reflexivity|].
 cbn [stores map snd FlatMemory.replay]. rewrite replay_app,block_store_memory,IH;reflexivity.
Qed.
Lemma writes_projection p loc es : forall d x,
 (exists w, In w (stores p loc d es) /\ touches w x) <-> writes_at loc (map snd es) x.
Proof.
 induction es as [|[ip e] t IH];intros d x.
 - split;[intros [w [[] _]]|intros [v [s [[] _]]]].
 - cbn [stores map snd]. unfold writes_at at 1.
   split.
   + intros [w [I X]]. apply in_app_or in I as [H|H].
     * destruct (proj1 (block_store_footprint loc ip e d x) (ex_intro _ w (conj H X))) as [s [S A]].
       exists e,s;auto using in_eq.
     * destruct (proj1 (IH _ x) (ex_intro _ w (conj H X))) as [v [s [I A]]].
       exists v,s;auto using in_cons.
   + intros [v [s [[<-|I] [S A]]]].
     * destruct (proj2 (block_store_footprint loc ip e d x) (ex_intro _ s (conj S A))) as [w [H X]].
       exists w;split;auto using in_or_app.
     * assert (W:writes_at loc (map snd t) x) by (exists v,s;auto).
       destruct (proj2 (IH (next_data p d e) x) W) as [w [H X]]. exists w;split;auto using in_or_app.
Qed.
