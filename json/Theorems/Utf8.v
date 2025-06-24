From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Require Import Json.Parser.
Require Import Json.Theorems.Parser.
Require Import Json.Utf8.

Open Scope string_scope.

Lemma utf8_encode_correct : forall (c: codepoint) l,
    l = utf8_encode_codepoint c  ->
    (exists b1 b2 b3 b4 b5 b6 b7,
        l = [ Byte.of_bits (b7, (b6, (b5, (b4, (b3, (b2, (b1, false))))))) ]
        /\ c = (false, b4_zero, b4_zero, b4_zero, (false, b1, b2, b3), (b4, b5, b6, b7)) )
    \/ (exists b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11,
           l = [ Byte.of_bits (b5,  (b4,  (b3, (b2, (b1, (false,  (true, true)))))));
                 Byte.of_bits (b11, (b10, (b9, (b8, (b7, (b6, (false, true))))))) ]
           /\ c = (false, b4_zero, b4_zero, (false, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11))
           /\ (b1 = true \/ b2 = true \/ b3 = true \/ b4 = true))
    \/ (exists b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16,
           l = [ Byte.of_bits (b4,  (b3,  (b2,  (b1,  (false,   (true, (true, true)))))));
                 Byte.of_bits (b10, (b9,  (b8,  (b7,  (b6,  (b5,  (false, true)))))));
                 Byte.of_bits (b16, (b15, (b14, (b13, (b12, (b11, (false, true)))))))]
           /\ c = (false, b4_zero, (b1, b2, b3, b4), (b5, b6, b7, b8), (b9, b10, b11, b12), (b13, b14, b15, b16))
           /\ (b1 = true \/ b2 = true \/ b3 = true \/ b4 = true \/ b5 = true))
    \/ (exists b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
           l = [ Byte.of_bits (b3,  (b2,  (b1,  (false,   (true,  (true,   (true, true)))))));
                 Byte.of_bits (b9,  (b8,  (b7,  (b6,  (b5,  (b4,  (false, true)))))));
                 Byte.of_bits (b15, (b14, (b13, (b12, (b11, (b10, (false, true)))))));
                 Byte.of_bits (b21, (b20, (b19, (b18, (b17, (b16, (false, true))))))) ]
           /\ c = (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))
           /\ (b1 = true \/ b2 = true \/ b3 = true \/ b4 = true \/ b5 = true)).
Proof.
  intros.
  destruct c as [[[[[b21 [[[b20 b19] b18] b17]]
                      [[[b16 b15] b14] b13]]
                     [[[b12 b11] b10] b9]]
                    [[[b8 b7] b6] b5]]
                   [[[b4 b3] b2] b1]].
  unfold utf8_encode_codepoint in H.
  repeat match goal with
         | [_: l = if ?bit then [ _; _; _; _ ] else ?rest |- _] => destruct bit; [ right; right; right; repeat eexists; [ apply H | auto ] | ]
         | [_: l = if ?bit then [ _; _; _ ] else ?rest |- _] => destruct bit; [ right; right; left; repeat eexists; [ apply H | auto ] |  ]
         | [_: l = if ?bit then [ _; _ ] else ?rest |- _] => destruct bit; [ right; left; repeat eexists; [ apply H | auto ] | ]
         end.
  left. repeat eexists. apply H.
Defined.

Ltac for_all_valid_utf8_encodings c :=
  let encodings := constr:(utf8_encode_correct c (utf8_encode_codepoint c) eq_refl) in
  let rec f H :=
    match type of H with
    | exists bit : bool, _ => let b := fresh "b" in destruct H as [b _rest]; f _rest
    | ?a /\ ?b /\ ?c => destruct H as [eq [c_eq no_overlong]]
    | ?a /\ ?b => destruct H as [eq c_eq]
    | ?a \/ ?b => destruct H as [A | B]; [f A | f B]
    end
  in f encodings.

Theorem encoding_size_correct :
  (forall b1 b2 b3 b4 b5 b6 b7,
      encoding_size_from_header
        (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false)))))))) = Some (OneByte (b7, b6, b5, b4, b3, b2, b1)))
  /\ (forall b1 b2 b3 b4 b5,
         encoding_size_from_header
           (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (true, true)))))))) = Some (TwoBytes (b5, b4, b3, b2, b1)))
  /\ (forall b1 b2 b3 b4,
         encoding_size_from_header
           (Byte.of_bits (b1, (b2, (b3, (b4, (false, (true, (true, true)))))))) = Some (ThreeBytes (b4, b3, b2, b1)))
  /\ (forall b1 b2 b3,
         encoding_size_from_header
        (Byte.of_bits (b1, (b2, (b3, (false, (true, (true, (true, true)))))))) = Some (FourBytes (b3, b2, b1))).
Proof.
  unfold encoding_size_from_header.
  repeat split; intros; rewrite Byte.to_bits_of_bits;
    repeat match goal with
      | [ |- (if ?bit then _ else _) = _ ] => destruct bit
      | [ |- (_ = _)] => reflexivity
    end.
Defined.

Theorem parse_continuation_correct: forall rest b1 b2 b3 b4 b5 b6,
    parse_continuation (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true))))))) :: rest) = Ok ((b6, b5, b4, b3, b2, b1), rest).
Proof.
  intros.
  unfold parse_continuation.
  rewrite parser_map_correct.
  unfold predicate. rewrite Byte.to_bits_of_bits.
  unfold fmap.
  unfold bind.
  assert ((if true && negb false
     then Ok (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true))))))), rest)
     else
      Err
        (Error
           (InvalidContinuationHeader
              (Some
                 (Byte.of_bits
                    (b1, (b2, (b3, (b4, (b5, (b6, (false, true)))))))))))) = Ok (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true))))))), rest)) as G; try reflexivity.
  rewrite G.
  rewrite Byte.to_bits_of_bits.
  reflexivity.
Defined.
  
Theorem parse_codepoint_encode_correct : forall c rest, parse_codepoint ((utf8_encode_codepoint c) ++ rest)%list = Ok (c, rest).
Proof.

  Ltac no_overlongs :=
    match goal with
    | [ H: ?bit = true \/ ?b |- _] => destruct H; no_overlongs
    | [ G: ?bit = true |- context[if ?bit then _ else _] ] => rewrite G; reflexivity
    | |- context[if ?bit then _ else _] => destruct bit; [ reflexivity | no_overlongs ]
    end.
  
  intros.
  destruct encoding_size_correct as [enc_one [enc_two [enc_three enc_four]]].
  for_all_valid_utf8_encodings c;
    auto;
    rewrite eq;
    unfold parse_codepoint, parse_header, bind, app;
    [ rewrite enc_one | rewrite enc_two | rewrite enc_three | rewrite enc_four];
    rewrite c_eq;
    repeat rewrite parse_continuation_correct;
    try reflexivity;
    unfold codepoint_range_to_codepoint, bind;
    no_overlongs.
Defined.

Lemma parse_single_codepoint_correct : forall c, parse_codepoint (utf8_encode_codepoint c) = Ok (c, []).
Proof.
  intros.
  rewrite <- (List.app_nil_r (utf8_encode_codepoint c)).
  apply (parse_codepoint_encode_correct c []).
Defined.

(* Lemma many_aux_strong_progress : forall A I E s p, *)
(*     (forall val rest, p s = Ok (val, rest) -> (length rest) < (length s)) -> *)
(*     (exists val, @many_aux A I E p (S (length s)) s = Ok (val, [])). *)
(* Proof. *)
(*   (* intros. *) *)
(*   (* induction s. *) *)
(*   (* - simpl. destruct (p []) as [[val rest] | errs]. *) *)
(*   (*   + specialize (H val rest eq_refl). inversion H. rewrite length_zero_iff_nil in H1. subst. eauto. *) *)
(*   (*   + eauto. *) *)
(*   (* - simpl in *. destruct (p (a :: s)) as [[val rest] | errs]. *) *)
(*   (*   + specialize (H val rest eq_refl). *) *)
(*   (*     inversion H; subst. *) *)
(* Admitted. *)

Lemma many_aux_length_of_string_is_enough : forall n s,
    (S (List.length s)) <= n ->
    many_aux parse_codepoint (S (List.length s)) s = many_aux parse_codepoint n s.
Proof.
  Admitted.
  (* intros n. *)
  (* induction n; intros. *)
  (* - inversion H. *)
  (* - inversion H; try reflexivity. subst. *)
  (*   generalize dependent n. *)
  (*   induction s; intros; try reflexivity. *)
  (*   specialize (IHn (a::s) H1) as I1. *)
  (*   simpl in H, H1. *)
  (*   rewrite Nat.le_succ_l in H, H1. apply Nat.lt_le_incl in H, H1. *)
  (*   specialize (IHs H H1) as I2. *)
  (*   simpl. *)
  
     
Lemma many_codepoint_distributes : forall (c: codepoint) (cs: list codepoint),
    many parse_codepoint (utf8_encode_codepoint c ++ concat (map utf8_encode_codepoint cs))%list =
      let* (x, rest) := parse_codepoint (utf8_encode_codepoint c) in
      let* (xs, rest) := many parse_codepoint (concat (map utf8_encode_codepoint cs)) in
      Ok (x :: xs, rest).
Proof.
  intros.
  rewrite parse_single_codepoint_correct.
  unfold many. simpl.
  rewrite parse_codepoint_encode_correct.
  unfold bind.
  rewrite <- many_aux_length_of_string_is_enough.
  - reflexivity.
  - rewrite length_app.
    for_all_valid_utf8_encodings c; rewrite eq; simpl; auto.
Defined.

Theorem encode_decode_correct : forall u, utf8_decode (utf8_encode u) = Ok (u, []).
Proof.
  intros.
  unfold utf8_encode, utf8_decode.
  induction u; try reflexivity.
  simpl.
  rewrite many_codepoint_distributes.
  rewrite parse_single_codepoint_correct.
  rewrite IHu.
  reflexivity.
Defined.
