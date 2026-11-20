From Coq Require Import List ZArith Bool Lia.
From Machine Require Import execution.Blocks isa.Instructions execution.WordBounds.
Import ListNotations. Open Scope Z_scope.
(* A lane projection is exact. It introduces no second arithmetic model. *)
Record lane := Lane { registers:nat->Z; cells:pointer->Z }.
Definition view d j := Lane (Blocks.zmm d j) (fun a=>memory d a j).
Definition lane_load s bases b d := match find (fun x=>Nat.eqb(fst x)b) bases with
 | Some(_,a)=>cells s (offset a d) | None=>0 end.
Section Program.
Variable p : program.
Definition lane_effect j s e := match e with
 | Read r a=>Lane (put (registers s) r (cells s a)) (cells s)
 | Write r a=>Lane (registers s) (fun k=>if ptr_eq k a then registers s r else cells s k)
 | Broadcast r n=>Lane (put (registers s) r n) (cells s)
 | ClearUpper=>Lane (fun r=>if Nat.ltb r 16 && Nat.leb 2 j then 0 else registers s r) (cells s)
 | Evaluate id bases=>Lane (run (lane_load s bases) (fragment_code p id) (registers s)) (cells s) end.
Definition lane_effects j es s := fold_left (lane_effect j) es s.
Definition lane_models d j s :=
 (forall r, Blocks.zmm d j r=registers s r) /\ (forall a, memory d a j=cells s a).
Lemma view_effect d j s e : lane_models d j s ->
 lane_models (apply_effect p d e) j (lane_effect j s e).
Proof.
 intros [R M];destruct e;unfold lane_models;
 cbn [apply_effect lane_effect register_write Blocks.zmm memory registers cells];split;intro i;
 try (unfold put;destruct(Nat.eqb _ _));try (destruct(ptr_eq _ _));auto.
 - destruct(Nat.ltb _ _ && Nat.leb _ _);auto.
 - apply run_ext;[|exact R]. intros b d0;unfold effective_load,lane_load.
   destruct(find _ _)as[[base a]|];auto.
Qed.
Lemma view_effects d j s es : lane_models d j s ->
 lane_models (effects p es d) j (lane_effects j es s).
Proof. revert d s;induction es as [|e es IH];intros d s M;[exact M|].
 apply IH,view_effect;exact M. Qed.
Definition lane_words s := (forall r,word64(registers s r)) /\ (forall a,word64(cells s a)).
Lemma lane_effect_words j s e : effect_words e -> lane_words s -> lane_words (lane_effect j s e).
Proof.
 intros E [R M];destruct e;split;intro i;cbn [lane_effect registers cells];
 try (unfold put;destruct (Nat.eqb _ _));try (destruct (ptr_eq _ _));auto.
 - destruct (Nat.ltb _ _ && Nat.leb _ _);[unfold word64;lia|auto].
 - apply run_words;[|exact R]. intros b d;unfold lane_load.
   destruct(find _ _)as[[base a]|];[apply M|unfold word64;lia].
Qed.
Lemma lane_effects_words j es s : Forall effect_words es -> lane_words s -> lane_words (lane_effects j es s).
Proof. intro H;revert s;induction H;intros s S;[exact S|]. apply IHForall,lane_effect_words;assumption. Qed.
End Program.
