From Coq Require Import List ZArith Lia Strings.String Numbers.DecimalString.
From Machine Require Import isa.Instructions isa.ProgramLayout.
From Machine Require tests.CallerForms.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Rows carry an instruction occurrence and its offset in the symbol. Width
   comes directly from the instruction encoder when advancing or printing. *)
Definition row := (Z * instruction)%type.
Fixpoint fragment_rows pc (code : list instruction) : list row :=
 match code with
 | [] => []
 | i :: rest => (pc,i) :: fragment_rows (pc + Z.of_nat (List.length (encode i))) rest
 end.

Definition fragment p op := match op with VectorCode id => fragment_code p id | _ => [] end.
Fixpoint body_rows p pc ops : list row :=
 match ops with
 | [] => []
 | op :: tail => fragment_rows pc (fragment p op) ++
                 body_rows p (pc + Z.of_nat (List.length (op_bytes p op))) tail
 end.
Definition section_rows p s := match s with
 | Code b => body_rows p (start b) (body b)
 | Padding _ => []
 end.

Lemma fragment_rows_instructions pc code : map snd (fragment_rows pc code) = code.
Proof. revert pc; induction code; intros; cbn; congruence. Qed.
Lemma body_rows_instructions p pc ops :
 map snd (body_rows p pc ops) = flat_map (fragment p) ops.
Proof.
 revert pc; induction ops; intro pc; cbn; [reflexivity|].
 now rewrite map_app, fragment_rows_instructions, IHops.
Qed.

(* Equality of lists preserves order and multiplicity, even when two
   occurrences use the same fragment or have identical instructions. *)
Theorem all_vector_occurrences p :
 map snd (flat_map (section_rows p) (sections p)) =
 flat_map (fun s => match s with
 | Code b => flat_map (fragment p) (body b) | Padding _ => [] end) (sections p).
Proof.
 induction (sections p) as [|[b|padding] tail IH]; cbn; auto.
 rewrite map_app, body_rows_instructions. f_equal; exact IH.
Qed.

Local Lemma fragment_rows_app pc a b : fragment_rows pc (a++b) =
 fragment_rows pc a ++ fragment_rows (pc+Z.of_nat (List.length (flat_map encode a))) b.
Proof.
 revert pc; induction a; intro pc; cbn; [now rewrite Z.add_0_r|].
 rewrite IHa, app_length, Nat2Z.inj_add. now rewrite Z.add_assoc.
Qed.
Local Lemma body_rows_app p pc a b : body_rows p pc (a++b) =
 body_rows p pc a ++ body_rows p (pc+Z.of_nat (List.length (flat_map (op_bytes p) a))) b.
Proof.
 revert pc; induction a; intro pc; cbn; [now rewrite Z.add_0_r|].
 rewrite IHa, app_length, Nat2Z.inj_add, Z.add_assoc, app_assoc. reflexivity.
Qed.

Theorem row_at_encoded_offset p b before id after prefix i suffix :
 In (Code b) (sections p) -> body b = before ++ VectorCode id :: after ->
 fragment_code p id = prefix ++ i :: suffix ->
 let pc := start b + Z.of_nat (List.length (flat_map (op_bytes p) before)) +
                      Z.of_nat (List.length (flat_map encode prefix)) in
 In (pc,i) (flat_map (section_rows p) (sections p)).
Proof.
 intros Block Body Code pc. apply in_flat_map. exists (ProgramLayout.Code b); split; [exact Block|].
 unfold section_rows; rewrite Body, body_rows_app. apply in_or_app; right.
 cbn [body_rows fragment]; apply in_or_app; left.
 rewrite Code, fragment_rows_app. apply in_or_app; right. now left.
Qed.

Example mixed_block_offsets :
 let i := (0%nat, Copy 1) in
 let p := Program [[i]] [] in
 map fst (body_rows p 10 [ZeroUpper; VectorCode 0; DecEcx; VectorCode 0]) = [13;21].
Proof. reflexivity. Qed.

Local Open Scope string_scope.
Definition decimal_z n := NilZero.string_of_int (Z.to_int n).
Definition fields (i : instruction) :=
  let '(dst, op) := i in
  let args3 name a b := [name; decimal dst; decimal a; decimal b] in
  match op with
  | Copy a => ["vmovdqa64"; decimal dst; decimal a]
  | Load b d => ["vmovdqu64"; decimal dst; decimal b; decimal_z d]
  | Xor a b => args3 "vpxorq" a b
  | Add a b => args3 "vpaddq" a b
  | Sub a b => args3 "vpsubq" a b
  | Mul a b => args3 "vpmullq" a b
  | And a b => args3 "vpandq" a b
  | Shl a n => args3 "vpsllq" a n
  | Shr a n => args3 "vpsrlq" a n
  | MaddMem hi a base d => [(if hi then "vpmadd52huq_mem" else "vpmadd52luq_mem"); decimal dst; decimal a; decimal base; decimal_z d]
  | Madd hi a b => args3 (if hi then "vpmadd52huq" else "vpmadd52luq") a b
  end.
Definition format_row (r : row) :=
 let '(pc,i) := r in
 String.concat " " (decimal_z pc :: decimal (List.length (encode i)) :: fields i).
Definition exported p :=
 let forms := CallerForms.caller_forms p in
 let counts := String.concat " " ["caller"; decimal (List.length forms);
                  decimal (List.length (nodup CallerForms.form_eq_dec forms))] in
 String.concat "|" (counts :: map format_row (flat_map (section_rows p) (sections p))).
