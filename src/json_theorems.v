Require Import json.

From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope string_scope.

Lemma parser_map_correct: forall T R I E (f: T -> R) s (p: @parser T I E),
    (parser_map f p) s = fmap (fun '(v, rest) => (f v, rest)) (p s).
Proof.
  intros.
  unfold parser_map, fmap.
  destruct (p s) as [[val rest] |  err]; reflexivity.
Defined.

Lemma predicate_correct: forall T I E (p: @parser T I E) (pred: I -> bool) (err_handler: option I -> list E) v s rest,
    Ok (v, rest) = predicate pred err_handler s ->
    pred v = true.
Proof.
  intros.
  unfold predicate in H.
  
  destruct s.
  - discriminate H.
  - destruct (pred i) eqn:Eq.
    + inversion H. apply Eq.
    + discriminate H.
Defined.

Lemma utf8_encode_correct : forall l (c: codepoint),
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
  repeat split; intros; rewrite Byte.to_bits_of_bits.
  - destruct b4; destruct b5; destruct b6; destruct b7; reflexivity.
  - destruct b4; destruct b5; reflexivity.
  - destruct b4; reflexivity.
  - reflexivity.
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
        [InvalidContinuationHeader
           (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true))))))))]) = Ok (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true))))))), rest)) as G; try reflexivity.
  rewrite G.
  rewrite Byte.to_bits_of_bits.
  reflexivity.
Defined.
  
Theorem parse_codepoint_encode_correct : forall c rest, parse_codepoint ((utf8_encode_codepoint c) ++ rest)%list = Ok (c, rest).
Proof.

  Ltac no_overlongs :=
    match goal with
    | [ G: ?bit = true |- context[if ?bit then _ else _] ] => rewrite G; reflexivity
    | |- context[if ?bit then _ else _] => destruct bit; [ reflexivity | no_overlongs ]
    end.
  intros.
  destruct encoding_size_correct as [enc_one [enc_two [enc_three enc_four]]].
  destruct (utf8_encode_correct (utf8_encode_codepoint c) c) as [? | [ ? | [ ? | [ ? ?]]]]; auto.
  - destruct H as [b1 [b2 [b3 [b4 [b5 [b6 [b7 [eq c_eq]]]]]]]].
    rewrite eq.
    unfold parse_codepoint, parse_header.
    unfold bind.
    unfold app.
    rewrite enc_one. simpl.
    rewrite c_eq.
    reflexivity.
  - destruct H as [b1 [b2 [b3 [b4 [b5 [b6 [b7 [b8 [b9 [b10 [b11 [eq [c_eq no_overlong]]]]]]]]]]]]].
    rewrite eq.
    unfold parse_codepoint, parse_header.
    unfold app.
    rewrite enc_two.
    rewrite c_eq.
    unfold bind.
    repeat rewrite parse_continuation_correct.
    unfold codepoint_range_to_codepoint.
    destruct no_overlong as [H | [H | [H | H]]]; no_overlongs.
  - destruct H as [b1 [b2 [b3 [b4 [b5 [b6 [b7 [b8 [b9 [b10 [b11 [ b12 [b13 [b14 [b15 [b16 [eq [c_eq no_overlong]]]]]]]]]]]]]]]]]].
    rewrite eq.
    unfold parse_codepoint, parse_header.
    unfold app.
    rewrite enc_three.
    rewrite c_eq.
    unfold bind.
    repeat rewrite parse_continuation_correct.
    unfold codepoint_range_to_codepoint.
    destruct no_overlong as [H | [H | [H | [H | H]]]]; no_overlongs.
  - destruct H as [b2 [b3 [b4 [b5 [b6 [b7 [b8 [b9 [b10 [b11 [ b12 [b13 [b14 [b15 [b16 [b17 [b18 [b19 [b20 [b21 [eq [c_eq no_overlong]]]]]]]]]]]]]]]]]]]]]].
    rewrite eq.
    unfold parse_codepoint, parse_header.
    unfold app.
    rewrite enc_four.
    rewrite c_eq.
    unfold bind.
    repeat rewrite parse_continuation_correct.
    unfold codepoint_range_to_codepoint.
    destruct no_overlong as [H | [H | [H | [H | H]]]]; no_overlongs.
Defined.

Lemma parse_single_codepoint_correct : forall c, parse_codepoint (utf8_encode_codepoint c) = Ok (c, []).
Proof.
  intros.
  rewrite <- (List.app_nil_r (utf8_encode_codepoint c)).
  apply (parse_codepoint_encode_correct c []).
Defined.
  
Lemma many_codepoint_distributes : forall (c: codepoint) (cs: list codepoint),
    many parse_codepoint (utf8_encode_codepoint c ++ concat (map utf8_encode_codepoint cs))%list =
      let* (x, rest) := parse_codepoint (utf8_encode_codepoint c) in
      let* (xs, rest) := many parse_codepoint (concat (map utf8_encode_codepoint cs)) in
      Ok (x :: xs, rest).
Proof.
  induction cs.
  - simpl.
    rewrite app_nil_r.
    rewrite parse_single_codepoint_correct. unfold bind.
    destruct (utf8_encode_correct (utf8_encode_codepoint c) c) as [? | [ ? | [ ? | [ ? ?]]]]; auto;
      [ destruct H as [b1 [b2 [b3 [b4 [b5 [b6 [b7 [eq c_eq]]]]]]]]
      | destruct H as [b1 [b2 [b3 [b4 [b5 [b6 [b7 [b8 [b9 [b10 [b11 [eq [c_eq no_overlong]]]]]]]]]]]]]
      | destruct H as [b1 [b2 [b3 [b4 [b5 [b6 [b7 [b8 [b9 [b10 [b11 [ b12 [b13 [b14 [b15 [b16 [eq [c_eq no_overlong]]]]]]]]]]]]]]]]]]
      | destruct H as [b2 [b3 [b4 [b5 [b6 [b7 [b8 [b9 [b10 [b11 [ b12 [b13 [b14 [b15 [b16 [b17 [b18 [b19 [b20 [b21 [eq [c_eq no_overlong]]]]]]]]]]]]]]]]]]]]]]
      ]; rewrite eq; rewrite c_eq. unfold many, many_aux. unfold bind.
  
  Admitted.

 
Theorem encode_decode_correct : forall u, utf8_decode (utf8_encode u) = Ok (u, []).
Proof.
  intros.
  unfold utf8_encode, utf8_decode.

  induction u; auto. simpl.
  rewrite many_codepoint_distributes.
  rewrite parse_single_codepoint_correct.
  rewrite IHu.
  reflexivity.
Qed.

   
Theorem parse_null_isomorphic : parse_null "null" = Ok((JNull, "")).
  reflexivity.
Qed.
Theorem parse_true_isomorphic : parse_true "true" = Ok((JTrue, "")).
  reflexivity.
Qed.
Theorem parse_false_isomorphic : parse_false "false" = Ok((JFalse, "")).
  reflexivity.
Qed.



Theorem parser_map_correct { A B }: forall (f: A -> B) (p: @parser A) (s: string),
    parser_map f p s = fmap (fun '(x, rest) => (f x, rest)) (p s).
Proof.
  intros.
  unfold parser_map.
  cbv delta. f_equal; simpl.
  destruct (p s); try destruct x; reflexivity.
Qed.

Theorem parse_number_isomorphic :forall n, parse_number (serialize_json (JNumber n)) = Ok((JNumber n, "")).
Proof.
  intros.
  unfold parse_number, serialize_json.
  rewrite parser_map_correct.
  rewrite parse_nat_isomorphic.
  reflexivity.
Defined.

Theorem parse_correct_left (j: json) : parse_json (serialize_json j) = Ok((j, "")).
Proof.
  induction j; try auto.
  - unfold parse_json. unfold one_of. rewrite parse_number_isomorphic. reflexivity.
