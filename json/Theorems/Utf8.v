From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

Require Import Json.Parser.
Require Import Json.Theorems.Parser.
Require Import Json.Utf8.

Open Scope string_scope.

Ltac destruct_parse_continuation :=
  match goal with
    | [G: context[parse_continuation (?a::?b) = Ok (?resp, ?suffix)] |- _] => idtac
    | [H: context[parse_continuation ?text = Ok (?resp, ?suffix)] |- _] => destruct text; [ discriminate H | ]
  end;
  match goal with
    | [H: context[parse_continuation (?b::?rest) = Ok (?resp, ?suffix)] |- _] =>
        unfold parse_continuation in H;
        rewrite parser_map_correct in H;
        simpl in H;
        let B1 := fresh "b" in
        let B2 := fresh "b" in
        let B3 := fresh "b" in
        let B4 := fresh "b" in
        let B5 := fresh "b" in
        let B6 := fresh "b" in
        let B7 := fresh "b" in
        let B8 := fresh "b" in
        let eqn_name := fresh "byte_bits" in
        destruct (Byte.to_bits b) as [B1 [B2 [B3 [B4 [B5 [B6 [B7 B8]]]]]]] eqn:eqn_name;
        match goal with
        | [G: context[if (?a && negb ?b) then _ else _] |- _ ] =>
            destruct a; destruct b; try discriminate G; simpl in H; rewrite eqn_name in H;
            apply (f_equal Byte.of_bits) in eqn_name;
            rewrite Byte.of_bits_to_bits in eqn_name
        end
    end.

Ltac to_bits byte :=
  let rec break_bit bits :=
    match type of bits with
    | (bool * bool)%type => let b1 := fresh "b" in let b2 := fresh "b" in destruct bits as [b1 b2]
    | (bool * ?rest)%type => let b := fresh "b" in destruct bits as [b _bits]; break_bit _bits
    | (?rest * bool)%type => let b := fresh "b" in destruct bits as [_bits b]; break_bit _bits
    | ?other => idtac other
    end
  in 
  match type of byte with
  | Utf8.b6 =>
      unfold Utf8.b6 in byte; break_bit byte
  | Byte.byte =>
      let B := fresh "B" in
      let eqn_name := fresh "byte_bits" in
      remember (Byte.to_bits byte) as B eqn:eqn_name;
      break_bit B;
      symmetry in eqn_name
  end.

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
  (forall byte b1 b2 b3 b4 b5 b6 b7, byte = (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false)))))))) <->
      encoding_size_from_header byte = Some (OneByte (b7, b6, b5, b4, b3, b2, b1)))
  /\ (forall byte b1 b2 b3 b4 b5, byte = (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (true, true)))))))) <->
         encoding_size_from_header byte = Some (TwoBytes (b5, b4, b3, b2, b1)))
  /\ (forall byte b1 b2 b3 b4, byte = (Byte.of_bits (b1, (b2, (b3, (b4, (false, (true, (true, true)))))))) <->
         encoding_size_from_header byte = Some (ThreeBytes (b4, b3, b2, b1)))
  /\ (forall byte b1 b2 b3, byte = (Byte.of_bits (b1, (b2, (b3, (false, (true, (true, (true, true)))))))) <->
         encoding_size_from_header byte = Some (FourBytes (b3, b2, b1))).
Proof.
  repeat (split; intros; subst);
    try (unfold encoding_size_from_header; repeat rewrite Byte.to_bits_of_bits;
         repeat match goal with
           | [ |- (if ?bit then _ else _) = _ ] => destruct bit
           | [ |- (_ = _)] => reflexivity
           end);
    unfold encoding_size_from_header in H;
    to_bits byte;
    apply (f_equal Byte.of_bits) in byte_bits;
    rewrite Byte.of_bits_to_bits in byte_bits;
    rewrite byte_bits;
    repeat match goal with
      | [ H: (if ?bit then _ else _) = _ |- _ ] => destruct bit
      | [ |- (_ = _)] => try discriminate; inversion H; reflexivity
      end.
Defined.

Lemma enc_one_spec: forall b1 b2 b3 b4 b5 b6 b7, encoding_size_from_header (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false)))))))) = Some (OneByte (b7, b6, b5, b4, b3, b2, b1)).
Proof.
  intros.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  eapply e1. reflexivity.
Defined.

Lemma enc_two_spec: forall b1 b2 b3 b4 b5, encoding_size_from_header (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (true, true)))))))) = Some (TwoBytes (b5, b4, b3, b2, b1)).
Proof.
  intros.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  eapply e2. reflexivity.
Defined.

Lemma enc_three_spec: forall b1 b2 b3 b4, encoding_size_from_header (Byte.of_bits (b1, (b2, (b3, (b4, (false, (true, (true, true)))))))) = Some (ThreeBytes (b4, b3, b2, b1)).
Proof.
  intros.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  eapply e3. reflexivity.
Defined.

Lemma enc_four_spec: forall b1 b2 b3, encoding_size_from_header (Byte.of_bits (b1, (b2, (b3, (false, (true, (true, (true, true)))))))) = Some (FourBytes (b3, b2, b1)).
Proof.
  intros.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  eapply e4. reflexivity.
Defined.

Theorem parse_continuation_correct: forall byte rest b1 b2 b3 b4 b5 b6,
    parse_continuation (byte :: rest) = Ok ((b6, b5, b4, b3, b2, b1), rest) <-> byte = Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true))))))).
Proof.
  intros. split; intros.
  - destruct_parse_continuation. inversion H; subst. reflexivity.
  - subst. unfold parse_continuation. rewrite parser_map_correct. unfold predicate. rewrite Byte.to_bits_of_bits. unfold fmap, bind. assert (true && negb false = true). reflexivity. rewrite H. rewrite Byte.to_bits_of_bits. reflexivity.
Defined.

Theorem parse_continuation_strong_progress: forall suffix response text,
    (parse_continuation text = Ok (response, suffix)) ->
    length suffix < length text.
Proof.
  intros.
  generalize dependent response.
  generalize dependent suffix.
  induction text as [| byte1 text_rest]; intros.
  - inversion H.
  - destruct_parse_continuation. inversion H. subst.
    simpl. lia.
Defined.

Lemma parse_continuation_spec: forall rest b1 b2 b3 b4 b5 b6, parse_continuation ((Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, true)))))))) :: rest) = Ok ((b6, b5, b4, b3, b2, b1), rest).
Proof.
  intros.
  eapply parse_continuation_correct.
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
  for_all_valid_utf8_encodings c;
    auto;
    rewrite eq;
    unfold parse_codepoint, parse_header, bind, app;
    [ rewrite enc_one_spec | rewrite enc_two_spec | rewrite enc_three_spec | rewrite enc_four_spec];
    rewrite c_eq;
    repeat rewrite parse_continuation_spec;
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

Ltac no_overlong_encoding Hyp :=
  repeat match type of Hyp with
    | context[if ?bit then _ else _] => destruct bit
    | Err _ = Ok _ => discriminate Hyp
    end.

Lemma parse_codepoint_strong_progress: forall suffix response text,
    (parse_codepoint text = Ok (response, suffix)) ->
    length suffix < length text.
Proof.
  intros.
  generalize dependent response.
  generalize dependent suffix.
  induction text as [| byte1 text_rest1]; intros.
  - inversion H.
  - simpl. 
    to_bits byte1.
    unfold parse_codepoint, parse_header, encoding_size_from_header in H.
    rewrite byte_bits in H.
    repeat match goal with
           | [ H: context[if ?bit then _ else _] |- _ ] => destruct bit
           | [ H: (_ = _) |- _ ] => simpl in H; discriminate H
           end; simpl in H;
      (* encoding size = 1 *)
      try (inversion H; lia);
      (* encoding size = 2 *)
      destruct (parse_continuation text_rest1) as [[val1 text_rest2] | err] eqn:P_cont_text_rest1; try discriminate H;
      destruct_parse_continuation; to_bits val1; inversion H; subst; inversion P_cont_text_rest1; subst; clear H; simpl; try lia;
      no_overlong_encoding H1; inversion H1; try lia;
      (* encoding size = 3 *)
      destruct (parse_continuation text_rest2) as [[val2 text_rest3] | err] eqn:P_cont_text_rest2; try discriminate H1;
      destruct_parse_continuation; to_bits val2; inversion P_cont_text_rest2; inversion H1; subst; simpl; try lia;
      no_overlong_encoding H9; inversion H9; try lia;
      (* encoding size = 4 *)
      destruct (parse_continuation text_rest3) as [[val3 text_rest4] | err] eqn:P_cont_text_rest3; try discriminate H9;
      destruct_parse_continuation; to_bits val3; inversion P_cont_text_rest3; inversion H9; subst; simpl; try lia;
      no_overlong_encoding H11; inversion H11; lia.
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

Theorem decode_encode_correct_strong: forall (unicode: unicode_str) (bytes rest: list Byte.byte),
    forall lesser, ((length lesser) <= (length bytes)) ->
            (utf8_decode lesser = Ok (unicode, rest)) ->
            lesser = List.app (utf8_encode unicode) rest.
Proof.
  intros unicode bytes.
  generalize dependent unicode.
  destruct encoding_size_correct as [e1 [e2 [e3 e4]]].
  induction bytes; intros unicode rest lesser enough_fuel IH_bytes.
  - inversion enough_fuel. Search (List.length). rewrite length_zero_iff_nil in H0. subst. inversion IH_bytes. reflexivity.
  - unfold utf8_decode, many in IH_bytes. simpl in IH_bytes.
    destruct (parse_codepoint lesser) as [[val rest1] | err] eqn:Parse_lesser; [| inversion IH_bytes; reflexivity].
    destruct lesser as [| byte1 bytes_rest1].
    + inversion Parse_lesser; reflexivity.
    + unfold parse_codepoint, parse_header in Parse_lesser.
      destruct (encoding_size_from_header byte1) as [enc_size| ] eqn:Enc_byte1; simpl in Parse_lesser; [| inversion Parse_lesser; reflexivity].
      destruct enc_size as [ [[[[[[b7 b6] b5] b4]b3] b2] b1]| [[[[b11 b10] b9] b8] b7] | [[[b16 b15] b14] b13] | [[b21 b20] b19] ] eqn:E_enc_size;
        [ rewrite <- e1 in Enc_byte1 | rewrite <- e2 in Enc_byte1 |  rewrite <- e3 in Enc_byte1 | rewrite <- e4 in Enc_byte1 ];
        subst;
        unfold codepoint_range_to_codepoint, bind in Parse_lesser; simpl in Parse_lesser.
      * inversion Parse_lesser. subst. clear Parse_lesser.
        rewrite <- many_aux_saturation_aux with (n:= (S (Datatypes.length (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false))))))) :: rest1)))) in IH_bytes; [ | apply parse_codepoint_strong_progress | simpl; lia |  simpl; lia ].
        fold (many parse_codepoint rest1) in IH_bytes. fold (utf8_decode rest1) in IH_bytes.
        destruct (utf8_decode rest1) as [[val rest2] | err] eqn:U_rest1; [| discriminate IH_bytes ].
        inversion IH_bytes; apply IHbytes in U_rest1; subst. unfold utf8_encode, map. fold (map utf8_encode_codepoint). unfold concat. fold (concat (map utf8_encode_codepoint val)).
        unfold utf8_encode_codepoint, b4_zero; reflexivity. simpl in enough_fuel. lia.
      * destruct (parse_continuation bytes_rest1) as [[[[[[[b6 b5] b4] b3] b2] b1] bytes_rest2] | err] eqn: Parse_bytes_rest1; [ | discriminate Parse_lesser].
        no_overlong_encoding Parse_lesser; inversion Parse_lesser; subst; clear Parse_lesser;
        apply parse_continuation_strong_progress in Parse_bytes_rest1 as bytes_rest1_len;
        rewrite <- many_aux_saturation_aux with (n:= S (S (Datatypes.length bytes_rest1))) in IH_bytes; try apply parse_codepoint_strong_progress; try (simpl; lia);
        fold (many parse_codepoint rest1) in IH_bytes; fold (utf8_decode rest1) in IH_bytes;
        destruct (utf8_decode rest1) as [[val rest2] | err] eqn:U_rest1; try discriminate IH_bytes;
        inversion IH_bytes; apply IHbytes in U_rest1; subst; unfold utf8_encode, map; fold (map utf8_encode_codepoint); unfold concat; fold (concat (map utf8_encode_codepoint val));
        unfold utf8_encode_codepoint, b4_zero; fold utf8_encode_codepoint;
          destruct_parse_continuation; simpl in Parse_bytes_rest1; inversion Parse_bytes_rest1; subst;
          try reflexivity; simpl in enough_fuel; lia. 
      * destruct (parse_continuation bytes_rest1) as [[[[[[[b12 b11] b10] b9] b8] b7] bytes_rest2] | err] eqn: Parse_bytes_rest1; [ | discriminate Parse_lesser].
        destruct (parse_continuation bytes_rest2) as [[[[[[[b6 b5] b4] b3] b2] b1] bytes_rest3] | err] eqn: Parse_bytes_rest2; [ | discriminate Parse_lesser].
        no_overlong_encoding Parse_lesser; inversion Parse_lesser; subst; clear Parse_lesser;
          apply parse_continuation_strong_progress in Parse_bytes_rest1 as bytes_rest1_len;
          apply parse_continuation_strong_progress in Parse_bytes_rest2 as bytes_rest2_len;
          rewrite <- many_aux_saturation_aux with (n:= S (S (Datatypes.length bytes_rest1))) in IH_bytes; try apply parse_codepoint_strong_progress; try (simpl; lia);
          fold (many parse_codepoint rest1) in IH_bytes; fold (utf8_decode rest1) in IH_bytes; 
          destruct (utf8_decode rest1) as [[val rest2] | err] eqn:U_rest1; try discriminate IH_bytes;
          inversion IH_bytes; apply IHbytes in U_rest1; subst; unfold utf8_encode, map; fold (map utf8_encode_codepoint); unfold concat; fold (concat (map utf8_encode_codepoint val)); repeat destruct_parse_continuation;
          unfold utf8_encode_codepoint, b4_zero; fold utf8_encode_codepoint; inversion Parse_bytes_rest2; inversion Parse_bytes_rest1; subst; try reflexivity; simpl in enough_fuel; lia.
        * destruct (parse_continuation bytes_rest1) as [[[[[[[b18 b17] b16] b15] b14] b13] bytes_rest2] | err] eqn: Parse_bytes_rest1; [ | discriminate Parse_lesser].
          destruct (parse_continuation bytes_rest2) as [[[[[[[b12 b11] b10] b9] b8] b7] bytes_rest3] | err] eqn: Parse_bytes_rest2; [ | discriminate Parse_lesser].
          destruct (parse_continuation bytes_rest3) as [[[[[[[b6 b5] b4] b3] b2] b1] bytes_rest4] | err] eqn: Parse_bytes_rest3; [ | discriminate Parse_lesser].
          apply parse_continuation_strong_progress in Parse_bytes_rest1 as bytes_rest1_len;
            apply parse_continuation_strong_progress in Parse_bytes_rest2 as bytes_rest2_len;
            apply parse_continuation_strong_progress in Parse_bytes_rest3 as bytes_rest3_len;
          rewrite <- many_aux_saturation_aux with (n:= S (S (Datatypes.length bytes_rest1))) in IH_bytes;
            [ | apply parse_codepoint_strong_progress | | ];
            try (no_overlong_encoding Parse_lesser; inversion Parse_lesser; simpl; simpl in enough_fuel; subst; lia).
          fold (many parse_codepoint rest1) in IH_bytes; fold (utf8_decode rest1) in IH_bytes.
          destruct (utf8_decode rest1) as [[val2 rest2] | err] eqn:U_rest1; try discriminate IH_bytes.
          repeat destruct_parse_continuation. inversion Parse_bytes_rest1; inversion Parse_bytes_rest2; inversion Parse_bytes_rest3; subst.
          inversion IH_bytes; apply IHbytes in U_rest1;
            no_overlong_encoding Parse_lesser; inversion Parse_lesser; subst; clear Parse_lesser; subst;
            try (simpl in *; lia);
            unfold utf8_encode, map; fold (map utf8_encode_codepoint); unfold concat; fold (concat (map utf8_encode_codepoint val2)); try reflexivity.
Defined.

Theorem decode_encode_correct: forall (unicode: unicode_str) (bytes rest: list Byte.byte),
    (utf8_decode bytes = Ok (unicode, rest)) ->
    bytes = List.app (utf8_encode unicode) rest.
Proof.
  intros.
  apply decode_encode_correct_strong with (bytes:= bytes). lia. apply H.
Defined.
