(* Executable decoding and the signed root used by the assembly decoder. *)
From Coq Require Import ZArith.
From Curve25519 Require Import Field.
From Curve25519.group Require Import PrimeField Affine Decompression PointEncoding.
Local Open Scope Z_scope.

Definition decode_point w : option point :=
 let y := residue (w mod 2^255) in
 let sign := Z.testbit w 255 in
 match decode y sign as v return
   (match v with Some x => on_curve x y /\ has_sign sign x | None => forall x, ~on_curve x y end ->
    option point) with
 | Some x => fun H => Some (Point x y (proj1 H))
 | None => fun _ => None
 end (decode_correct y sign).

Theorem decode_point_iff w P : decode_point w = Some P <-> decodes w P.
Proof.
 unfold decode_point. set (v := residue (w mod 2^255)).
 generalize (decode_correct v (Z.testbit w 255)).
 destruct (decode v (Z.testbit w 255)) as [u|]; intro H.
 - assert (D : decodes w (Point u v (proj1 H))) by (split; [reflexivity|apply H]).
   split; [intros E; now injection E as <- | intro DP; f_equal; exact (decodes_unique _ _ _ D DP)].
 - split; [discriminate | intros [Y _]; exfalso; apply (H (x P)); fold v in Y; rewrite <-Y; apply on_edwards].
Qed.

Definition root_power y:=Decompression.power (numerator y*denominator y)%fp Decompression.exponent.
Definition root_test y:=test_value (numerator y) (denominator y) (root_power y).
Definition encoded_y w:=residue (w mod 2^255).
Definition encoded_sign w:=Z.testbit w 255.
Definition root_candidate w:= (numerator(encoded_y w)*root_power(encoded_y w))%fp.
Definition corrected_root w (minus:bool):=if minus then (root_candidate w*residue sqrt_m1)%fp else root_candidate w.
Lemma decoded_x w minus P : (minus=true <-> root_test(encoded_y w)=(0-1)%fp) -> decodes w P ->
 signed_root (encoded_sign w) (corrected_root w minus)=x P.
Proof.
 intros M [Y Tag];pose proof(on_edwards P) as Curve;rewrite Y in Curve.
 pose proof(decode_correct (encoded_y w) (encoded_sign w)) as Ok.
 destruct(decode (encoded_y w) (encoded_sign w)) as [v|] eqn:Run;[|exfalso;exact (Ok (x P) Curve)].
 destruct Ok as [VC VS];rewrite <-(unique_signed_root _ _ _ _ VC Curve VS Tag).
 unfold decode in Run;fold (root_power (encoded_y w)) in Run;fold (root_test (encoded_y w)) in Run;fold (root_candidate w) in Run.
 unfold corrected_root;destruct(fp_eq_dec (root_test(encoded_y w)) (0-1)%fp) as [Neg|Other].
 - rewrite (proj2 M Neg);now injection Run.
 - destruct minus;[elim Other;apply M;reflexivity|];destruct(fp_eq_dec (root_test(encoded_y w)) 1%fp);
   [now injection Run|destruct(fp_eq_dec (numerator(encoded_y w)) 0%fp);congruence].
Qed.

