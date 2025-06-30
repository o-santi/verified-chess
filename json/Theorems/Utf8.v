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

Lemma parse_codepoint_strong_progress: forall suffix response text,
    (Ok (response, suffix) = parse_codepoint text) ->
    length suffix < length text.
Proof.
  intros.
  generalize dependent response.
  generalize dependent suffix.
  induction text as [| byte1 text_rest1]; intros.
  - inversion H.
  - simpl. (* apply Nat.lt_lt_succ_r. *)
    destruct (Byte.to_bits byte1) as [b1 [b2 [b3 [b4 [b5 [b6 [b7 b8]]]]]]] eqn:byte1_bits.
    unfold parse_codepoint, parse_header, encoding_size_from_header in H.
    rewrite byte1_bits in H.
    repeat match goal with
           | [ H: context[if ?bit then _ else _] |- _ ] => destruct bit
           | [ H: (_ = _) |- _ ] => simpl in H; discriminate H
           end; simpl in H;
      (* encoding size = 1 *)
      try (inversion H; lia);
      (* encoding size = 2 *)
      unfold parse_continuation, predicate in H;
      destruct text_rest1 as [| byte2 text_rest2] eqn:E_text_rest1; try (simpl in H; discriminate H);
      rewrite parser_map_correct in H;
      destruct (Byte.to_bits byte2) as [B1 [B2 [B3 [B4 [B5 [B6 [B7 B8]]]]]]] eqn:byte2_bits;
      destruct B8; destruct B7; try discriminate H; simpl in H; rewrite byte2_bits in H;
      try (simpl; inversion H; subst; lia);
      (* encoding size = 3 *)
      try (destruct text_rest2 as [| byte3 text_rest3] eqn:E_text_rest2; [
            simpl in H; discriminate H |
            rewrite parser_map_correct in H;
            destruct (Byte.to_bits byte3) as [C1 [C2 [C3 [C4 [C5 [C6 [C7 C8]]]]]]] eqn:byte3_bits;
            destruct C8; destruct C7; try discriminate H; simpl in H; rewrite byte3_bits in H
        ]);
      (* encoding size = 4 *)
      try (simpl; inversion H; subst; lia);
      try (destruct text_rest3 as [| byte4 text_rest4] eqn:E_text_rest3; [
        simpl in H; discriminate H |
        rewrite parser_map_correct in H;
        destruct (Byte.to_bits byte4) as [D1 [D2 [D3 [D4 [D5 [D6 [D7 D8]]]]]]] eqn:byte4_bits;
        destruct D8; destruct D7; try discriminate H; simpl in H; rewrite byte4_bits in H
      ]);
      repeat match goal with
        | [ H: context[if ?bit then _ else _] |- _ ] => destruct bit
        | [ H: (_ = _) |- _ ] => simpl in H; try discriminate H; inversion H; simpl; lia
        end.
Defined.
    
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
  rewrite <- many_aux_saturation_aux with (n:= ( S ( S (Datatypes.length (utf8_encode_codepoint c ++ concat (map utf8_encode_codepoint cs))))));
    [ reflexivity | apply parse_codepoint_strong_progress | | ];
    for_all_valid_utf8_encodings c; rewrite eq; simpl; lia.
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

Theorem decode_encode_correct: forall (unicode: unicode_str) (bytes rest: list Byte.byte),
    (utf8_decode bytes = Ok (unicode, rest)) ->
    bytes = List.app (utf8_encode unicode) rest.
Proof.
  Admitted.
  
  (* intros unicode bytes. *)
  (* destruct encoding_size_correct as [enc_one [enc_two [enc_three enc_four]]]. *)
  (* generalize dependent unicode. *)
  (* induction bytes as [ | byte1 bytes_rest]; intros. *)
  (* - inversion H. reflexivity. *)
  (* - unfold utf8_decode, many in H. *)
  (*   unfold many_aux in H. fold (@many_aux codepoint) in H. unfold bind in H. *)
  (*   destruct (parse_codepoint (byte1 :: bytes_rest)) as [[val rest'] | err] eqn:ParseByte1; *)
  (*     [ | inversion H; subst; unfold utf8_encode; reflexivity ]. *)
    
  (*   rewrite <- many_aux_saturation_aux with (n:= (Datatypes.length (byte1 :: bytes_rest))) in H. *)
  (*   2: { apply parse_codepoint_strong_progress. } *)
  (*   fold (@many codepoint Byte.byte unicode_error parse_codepoint rest') in H. fold (utf8_decode rest') in H. *)
  (*   destruct (utf8_decode rest') as [[u r] | err]; try discriminate H. inversion H. subst. clear H. *)
  (*   unfold parse_codepoint, parse_header in ParseByte1. *)
  (*   destruct (encoding_size_from_header byte1) as [ enc_size | ] eqn:E_enc_size_byte1. *)
  (*   + unfold bind in ParseByte1. destruct enc_size eqn:E_enc_size. *)
  (*     * simpl in ParseByte1. *)
  (*       destruct b as [[[[[[b1 b2] b3] b4] b5] b6] b7]. inversion ParseByte1. *)
  (*       erewrite <- enc_one in E_enc_size_byte1. *)
  (*       unfold utf8_encode. *)
        
  (* intros unicode. *)
  (* induction unicode; intros. *)
  (* - unfold utf8_decode in H. simpl. *)
  (*   generalize dependent rest. *)
  (*   induction bytes; intros; unfold many in H; simpl in H. *)
  (*   + inversion H. reflexivity. *)
  (*   + destruct (parse_codepoint (a::bytes)) as [[val1 rest1] | err1]; try discriminate H. *)
  (*     destruct (parse_codepoint rest1) as [[val2 rest2] | err2]; try discriminate H. *)
  (*     destruct (many_aux parse_codepoint (Datatypes.length bytes) rest2) as [[val3 rest3] | err3]; discriminate H. *)
  (*     inversion H. reflexivity. *)
  (* - unfold utf8_decode in H. *)
    
      
    
   

  
