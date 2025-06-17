Require Import json.

From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import Lia.


Lemma div_10_le : forall n time,
  n <= S time -> n / 10 <= time.
Proof.
  intros [|n] time H. simpl. lia.
  assert (S n / 10 < S n); try lia.
  apply Nat.div_lt; lia.
Qed.

Lemma digit_iso : forall n, nat_of_ascii (ascii_of_nat (mod_10 n)) = Some (proj1_sig (mod_10 n)).
Proof.
  intros.
  destruct (mod_10 n).
  repeat match goal with
         | m: nat  |- _  => destruct m; [ reflexivity | try lia ]
         end.
Defined.

Lemma mod_10_correct : forall n, (proj1_sig (mod_10 n)) = n mod 10.
Proof.
  intros. unfold mod_10. reflexivity.
Defined.
  
Theorem parse_nat_aux_iso : forall time n acc,
    (n <= time) -> 
    nat_of_string_aux 0 (string_of_nat_aux time n acc) = nat_of_string_aux n acc.
Proof.
  intros time.
  induction time as [|time' Htime]; intros n acc H.
  - simpl. inversion H. reflexivity.
  - apply div_10_le in H. unfold string_of_nat_aux. destruct (n / 10) as [|n'] eqn: En'.
    * unfold nat_of_string_aux. rewrite digit_iso. f_equal. pose (Nat.Div0.div_mod n 10) as N. rewrite En' in N. rewrite mod_10_correct. symmetry. apply N.
    * rewrite Htime.
      ** unfold nat_of_string_aux. rewrite digit_iso. f_equal. pose (Nat.Div0.div_mod n 10) as N. rewrite En' in N. rewrite mod_10_correct. symmetry. apply N.
      ** apply H.
Defined.

Theorem parse_nat_isomorphic : forall (n: nat), parse_nat (string_of_nat n) = Ok(n, EmptyString).
Proof.
  intros.
  unfold parse_nat. unfold string_of_nat.
  apply parse_nat_aux_iso. reflexivity.
Defined.

Open Scope string_scope.

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
  - 
  
  
