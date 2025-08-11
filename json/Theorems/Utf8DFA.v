From Coq Require Import Strings.Byte.


Require Import Json.Parser.
Require Import Json.Utf8.
Require Import Json.Utf8DFA.
Require Import Json.Theorems.Parser.
Require Import Json.Theorems.Utf8.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lia.

Local Notation "0" := false.
Local Notation "1" := true.
Definition zero_codep : codepoint := (0, b4_zero, b4_zero, b4_zero, b4_zero, b4_zero).

Lemma byte_range_00_7f_bits : forall b,
    byte_range b = Range_00_7F ->
    exists b1 b2 b3 b4 b5 b6 b7,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (b5, (b6, (b7, 0))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_80_8f_bits : forall b,
    byte_range b = Range_80_8F ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (0, (0, (0, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_90_9f_bits : forall b,
    byte_range b = Range_90_9F ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (1, (0, (0, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_a0_bf_bits : forall b,
    byte_range b = Range_A0_BF ->
    exists b1 b2 b3 b4 b5,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (b5, (1, (0, 1))))))).
Proof.
  intros.
  - destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_c0_c1_bits : forall b,
    byte_range b = Range_C0_C1 ->
    exists b1,
      Byte.to_bits b = (b1, (0, (0, (0, (0, (0, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_range_c2_df_bits : forall b,
    byte_range b = Range_C2_DF ->
    exists b1 b2 b3 b4 b5,
      (Byte.to_bits b = (b1, (b2, (b3, (b4, (b5, (0, (1, 1))))))) /\
       (b3 = 0 /\ b4 = 0 /\ b5 = 0 -> b2 = 1)).
Proof.
  intros.
  destruct b; inversion H; repeat eexists; intros G; destruct G as [P1 [P2 P3]]; try discriminate; reflexivity.
Qed.

Lemma byte_e0_bits : forall b,
    byte_range b = Byte_E0 ->
    (Byte.to_bits b = (0, (0, (0, (0, (0, (1, (1, 1)))))))).
Proof.
  intros.
  destruct b; inversion H; reflexivity.
Qed.

Lemma byte_range_e1_ef_bits : forall b,
    byte_range b = Range_E1_EF ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (0, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_f0_bits : forall b,
    byte_range b = Byte_F0 ->
    Byte.to_bits b = (0, (0, (0, (0, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; reflexivity.
Qed.


Lemma byte_range_f1_f3_bits : forall b,
    byte_range b = Range_F1_F3 ->
    exists b1 b2,
      Byte.to_bits b = (b1, (b2, (0, (0, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.

Lemma byte_f4_bits : forall b,
    byte_range b = Byte_F4 ->
    Byte.to_bits b = (0, (0, (1, (0, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; reflexivity.
Qed.


Lemma byte_range_f5_ff_bits : forall b,
    byte_range b = Range_F5_FF ->
    exists b1 b2 b3 b4,
      Byte.to_bits b = (b1, (b2, (b3, (b4, (1, (1, (1, 1))))))).
Proof.
  intros.
  destruct b; inversion H; repeat eexists.
Qed.


Lemma byte_range_of_bits_a0_bf: forall b1 b2 b3 b4 b5,
    byte_range (of_bits (b1, (b2, (b3, (b4, (b5, (1, (0, 1)))))))) = Range_A0_BF.
Proof.
  intros.
  destruct (of_bits (b1, (b2, (b3, (b4, (b5, (1, (0, 1)))))))) eqn:H;
    apply (f_equal Byte.to_bits) in H;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    reflexivity.
Qed.

Lemma byte_range_of_bits_80_8f: forall (b1 b2 b3 b4: bool),
    byte_range (of_bits (b1, (b2, (b3, (b4, (0, (0, (0, 1)))))))) = Range_80_8F.
Proof.
  intros.
  destruct (of_bits (b1, (b2, (b3, (b4, (0, (0, (0, 1)))))))) eqn:H;
    apply (f_equal Byte.to_bits) in H;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.

Lemma byte_range_of_bits_80_bf: forall (b1 b2 b3 b4 b5 b6: bool),
    let b := of_bits (b1, (b2, (b3, (b4, (b5, (b6, (0, 1))))))) in
    (byte_range b = Range_80_8F) \/
      (byte_range b = Range_90_9F) \/
      (byte_range b = Range_A0_BF).
Proof.
  intros.
  destruct b eqn:H;
    apply (f_equal Byte.to_bits) in H;
    subst b;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.

Lemma byte_range_of_bits_90_9f: forall (b1 b2 b3 b4: bool),
    let b := of_bits (b1, (b2, (b3, (b4, (1, (0, (0, 1))))))) in
    (byte_range b = Range_90_9F).
Proof.
  intros.
  destruct b eqn:H;
    apply (f_equal Byte.to_bits) in H;
    subst b;
    rewrite Byte.to_bits_of_bits in H;
    inversion H;
    auto.
Qed.

Lemma next_state_expecting_1_80_bf :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (b16, (0, 1)))))))) in
    next_state Expecting_1_80_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (Finished (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_bf b21 b20 b19 b18 b17 b16) as [G | [G | G]]; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_2_80_bf :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (b16, (0, 1)))))))) in 
    next_state Expecting_2_80_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_1_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_bf b21 b20 b19 b18 b17 b16) as [G | [G | G]]; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.


Lemma next_state_expecting_3_80_bf :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (b16, (0, 1)))))))) in 
    next_state Expecting_3_80_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_2_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_bf b21 b20 b19 b18 b17 b16) as [G | [G | G]]; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_3_80_8f :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (0, (0, (0, 1)))))))) in
    next_state Expecting_3_80_8F (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_2_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 0, 0), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_80_8f b21 b20 b19 b18) as G.
  rewrite G.
  unfold push_bottom_bits.
  rewrite Byte.to_bits_of_bits. reflexivity.
Qed.

Lemma next_state_expecting_3_90_bf_p1 :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (1, (0, 1)))))))) in 
    next_state Expecting_3_90_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_2_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 1, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_a0_bf b21 b20 b19 b18 b17) as G.
  rewrite G.
  unfold push_bottom_bits.
  rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_3_90_bf_p2 :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (1, (0, (0, 1)))))))) in 
    next_state Expecting_3_90_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_2_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 0, 1), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_90_9f b21 b20 b19 b18) as G; rewrite G;
    unfold push_bottom_bits;
    rewrite Byte.to_bits_of_bits; reflexivity.
Qed.

Lemma next_state_expecting_2_a0_bf :
  forall c1 c2 c3 c4 c5 c6
    b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b17 b18 b19 b20 b21,
    let b := (of_bits (b21, (b20, (b19, (b18, (b17, (1, (0, 1)))))))) in
    next_state Expecting_2_A0_BF (c1, (c2, c3, c4, c5), (c6, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) b
    = Ok (More Expecting_1_80_BF (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, 1, b17), (b18, b19, b20, b21))).
Proof.
  intros.
  unfold next_state. subst b.
  pose proof (byte_range_of_bits_a0_bf b21 b20 b19 b18 b17) as G. rewrite G.
  unfold push_bottom_bits.
  rewrite Byte.to_bits_of_bits. reflexivity.
Qed.

Lemma if_redundant : forall T (P: T) (b: bool), (if b then P else P) = P.
Proof.
  destruct b; reflexivity.
Qed.

Theorem utf8_decoders_equal_strong : forall (bytes less: list byte),
    (List.length less) <= (List.length bytes) -> 
    utf8_dfa_decode less = utf8_decode less.
Proof.
  Opaque Byte.of_bits.
  intros bytes.
  induction bytes; intros.
  - inversion H. rewrite length_zero_iff_nil in H1. subst. reflexivity.
  - unfold utf8_dfa_decode, utf8_decode, all, all_aux. fold (all_aux parse_codepoint).   
    destruct less as [| byte byte_rest]; [ reflexivity | ]. 
    destruct (parse_codepoint (byte :: byte_rest)) as [[val rest] | err] eqn:P_byte_byte_rest.
    rewrite <- all_aux_saturation_aux with (n:= (S (S (Datatypes.length (rest))))).
    fold (all parse_codepoint rest). fold (utf8_decode rest). rewrite <- IHbytes.
    3: apply parse_codepoint_strong_progress.
    2,3,4: simpl in H; apply parse_codepoint_strong_progress in P_byte_byte_rest; simpl in P_byte_byte_rest; simpl; lia.
    simpl. 
    unfold parse_codepoint, parse_header, encoding_size_from_header in P_byte_byte_rest.
    unfold next_state, extract_3_bits, extract_4_bits, extract_5_bits, extract_7_bits.
    destruct (byte_range byte) eqn:B; [
        apply byte_range_00_7f_bits in B as byte_bits; destruct byte_bits as [b1 [b2 [b3 [b4 [b5 [b6 [b7 byte_bits]]]]]]]
      | apply byte_range_80_8f_bits in B as byte_bits; destruct byte_bits as [b1 [b2 [b3 [b4 byte_bits]]]]
      | apply byte_range_90_9f_bits in B as byte_bits; destruct byte_bits as [b1 [b2 [b3 [b4 byte_bits]]]]
      | apply byte_range_a0_bf_bits in B as byte_bits; destruct byte_bits as [b1 [b2 [b3 [b4 [b5 byte_bits]]]]]
      | apply byte_range_c0_c1_bits in B as byte_bits; destruct byte_bits as [b1 byte_bits]
      | apply byte_range_c2_df_bits in B as byte_bits; destruct byte_bits as [b1 [b2 [b3 [b4 [b5 [byte_bits not_c0_c1]]]]]]
      | apply byte_e0_bits in B as byte_bits
      | apply byte_range_e1_ef_bits in B as byte_bits; destruct byte_bits as [b1 [b2 [b3 [b4 byte_bits]]]]
      | apply byte_f0_bits in B as byte_bits
      | apply byte_range_f1_f3_bits in B as byte_bits; destruct byte_bits as [b1 [b2 byte_bits]]
      | apply byte_f4_bits in B as byte_bits
      | apply byte_range_f5_ff_bits in B as byte_bits; destruct byte_bits as [b1 [b2 [b3 [b4 byte_bits]]]]
      ]; rewrite byte_bits in *; simpl in *; try (crush_bits; simpl in *; inversion P_byte_byte_rest; subst; reflexivity).
    * destruct (parse_continuation byte_rest) as [[r byte_rest2] | err]; try discriminate.
    * repeat rewrite if_redundant in P_byte_byte_rest.
      simpl in *; destruct (parse_continuation byte_rest) as [[r byte_rest2] | err] eqn:P_cont_byte_rest; try discriminate.
      simpl in P_byte_byte_rest; to_bits r; inversion P_byte_byte_rest; subst.
      destruct byte_rest; try discriminate;
        destruct_parse_continuation; inversion P_cont_byte_rest; subst;
        crush_bits; simpl; unfold b4_zero;
        rewrite next_state_expecting_1_80_bf; simpl; inversion H1; subst; reflexivity.
    * destruct (parse_continuation byte_rest) as [[snd rest2] | err] eqn:P_cont_byte_rest; try discriminate. simpl in P_byte_byte_rest.
      destruct (parse_continuation rest2) as [[trd rest3] | err] eqn:P_cont_rest2; try discriminate. simpl in P_byte_byte_rest. to_bits snd; to_bits trd.
      crush_bits; try discriminate.
      repeat destruct_parse_continuation. inversion P_cont_byte_rest; inversion P_cont_rest2; inversion P_byte_byte_rest; subst.
      simpl. unfold b4_zero. rewrite next_state_expecting_2_a0_bf. simpl.
      rewrite next_state_expecting_1_80_bf. simpl. reflexivity.
    * rewrite if_redundant in P_byte_byte_rest.
      simpl in *.
      destruct (parse_continuation byte_rest) as [[snd rest2] | err] eqn:P_cont_byte_rest; try discriminate. simpl in P_byte_byte_rest.
      destruct (parse_continuation rest2) as [[trd rest3] | err] eqn:P_cont_rest2; try discriminate. simpl in P_byte_byte_rest. to_bits snd; to_bits trd.
      repeat destruct_parse_continuation.
      crush_bits; inversion P_cont_byte_rest; inversion P_cont_rest2; inversion P_byte_byte_rest; simpl; subst;
      unfold b4_zero;
      rewrite next_state_expecting_2_80_bf; simpl;
      rewrite next_state_expecting_1_80_bf; reflexivity.
    * destruct (parse_continuation byte_rest) as [[snd rest2] | err] eqn:P_cont_byte_rest; try discriminate. simpl in P_byte_byte_rest.
      destruct (parse_continuation rest2) as [[trd rest3] | err] eqn:P_cont_rest2; try discriminate. simpl in P_byte_byte_rest. to_bits snd; to_bits trd.
      destruct (parse_continuation rest3) as [[frth rest4] | err] eqn:P_cont_rest3; try discriminate. simpl in P_byte_byte_rest. to_bits frth.
      crush_bits; simpl; repeat destruct_parse_continuation;
        inversion P_cont_byte_rest; inversion P_cont_rest2; inversion P_cont_rest3; inversion P_byte_byte_rest; subst;
        simpl; unfold b4_zero;
        try rewrite next_state_expecting_3_90_bf_p1; try rewrite next_state_expecting_3_90_bf_p2; simpl;
             rewrite next_state_expecting_2_80_bf; simpl;
             rewrite next_state_expecting_1_80_bf; reflexivity.
    * destruct (parse_continuation byte_rest) as [[snd rest2] | err] eqn:P_cont_byte_rest; try discriminate. simpl in P_byte_byte_rest.
      destruct (parse_continuation rest2) as [[trd rest3] | err] eqn:P_cont_rest2; try discriminate. simpl in P_byte_byte_rest. to_bits snd; to_bits trd.
      destruct (parse_continuation rest3) as [[frth rest4] | err] eqn:P_cont_rest3; try discriminate. simpl in P_byte_byte_rest. to_bits frth. unfold b4_zero.
      crush_bits; simpl; repeat destruct_parse_continuation;
        inversion P_cont_byte_rest; inversion P_cont_rest2; inversion P_cont_rest3; inversion P_byte_byte_rest; subst; simpl;
        rewrite next_state_expecting_3_80_bf; simpl;
        rewrite next_state_expecting_2_80_bf; simpl;
        rewrite next_state_expecting_1_80_bf; reflexivity.
     * destruct (parse_continuation byte_rest) as [[snd rest2] | err] eqn:P_cont_byte_rest; try discriminate. simpl in P_byte_byte_rest.
      destruct (parse_continuation rest2) as [[trd rest3] | err] eqn:P_cont_rest2; try discriminate. simpl in P_byte_byte_rest. to_bits snd; to_bits trd.
      destruct (parse_continuation rest3) as [[frth rest4] | err] eqn:P_cont_rest3; try discriminate. simpl in P_byte_byte_rest. to_bits frth. unfold b4_zero.
      repeat destruct_parse_continuation.
      crush_bits; try discriminate.
        inversion P_cont_byte_rest; inversion P_cont_rest2; inversion P_cont_rest3; inversion P_byte_byte_rest; subst. simpl. unfold b4_zero.
      rewrite next_state_expecting_3_80_8f; simpl;
        rewrite next_state_expecting_2_80_bf; simpl;
        rewrite next_state_expecting_1_80_bf; reflexivity.
     * destruct byte; try discriminate B; inversion byte_bits; subst; simpl in P_byte_byte_rest;
       destruct (parse_continuation byte_rest) as [[snd rest2] | err] eqn:P_cont_byte_rest; try discriminate; simpl in P_byte_byte_rest;
      destruct (parse_continuation rest2) as [[trd rest3] | err] eqn:P_cont_rest2; try discriminate; simpl in P_byte_byte_rest; to_bits snd; to_bits trd;
         destruct (parse_continuation rest3) as [[frth rest4] | err] eqn:P_cont_rest3; try discriminate.
     * 
