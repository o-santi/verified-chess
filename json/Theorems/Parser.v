From Coq Require Import Lists.List. Import ListNotations.
Require Import Json.Parser.
Require Import Lia.

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

Theorem many_aux_saturation_aux : forall A I E processor,
  (forall suffix response text,
    processor text = Ok (response, suffix) ->
    length suffix < length text) ->
  forall n text fuel,
  (S (length text)) < n ->
  (S (length text)) <= fuel ->
  @many_aux A I E processor (S (length text)) text = @many_aux A I E processor fuel text.
Proof.
  intros A I E processor processor_good.
  induction n; intros text fuel.
  - intros H. inversion H.
  - intros text_bounded enough_fuel.
    destruct text as [|text_head text_tail].
    destruct fuel; try inversion enough_fuel. reflexivity. simpl. destruct (processor []) eqn:response_definition.
    destruct x as [response suffix].
    exfalso. assert (@length I suffix < @length I nil).
    apply processor_good with (response := response) (suffix := suffix).
    apply response_definition.
    inversion H1.
    reflexivity. simpl in text_bounded. 
    destruct fuel. exfalso. inversion enough_fuel.
    simpl. destruct (processor (text_head :: text_tail)) eqn:response_definition.
    + destruct x as [val rest].
      replace (many_aux processor fuel rest) with (many_aux processor (S (length text_tail)) rest).
      reflexivity.
      assert (length rest < length (text_head :: text_tail)). {
        apply processor_good with (response := val).
        apply response_definition.
      } {
      replace
        (many_aux processor (S (length text_tail)) rest)
      with
        (many_aux processor (S (length rest)) rest).
      apply IHn. simpl in H. lia. lia.
      apply IHn. simpl in H. lia.
      simpl in H. lia.
      }
    + reflexivity.
Qed.

Theorem all_aux_saturation_aux : forall A I E processor,
  (forall suffix response text,
    processor text = Ok (response, suffix) ->
    length suffix < length text) ->
  forall n text fuel,
  (S (length text)) < n ->
  (S (length text)) <= fuel ->
  @all_aux A I E processor (S (length text)) text = @all_aux A I E processor fuel text.
Proof.
  intros A I E processor processor_good.
  induction n; intros text fuel.
  - intros H. inversion H.
  - intros text_bounded enough_fuel.
    destruct text as [|text_head text_tail].
    destruct fuel; try inversion enough_fuel. reflexivity. simpl. destruct (processor []) eqn:response_definition.
    destruct x as [response suffix].
    exfalso. assert (@length I suffix < @length I nil).
    apply processor_good with (response := response) (suffix := suffix).
    apply response_definition.
    inversion H1.
    reflexivity. simpl in text_bounded. 
    destruct fuel. exfalso. inversion enough_fuel.
    simpl. destruct (processor (text_head :: text_tail)) eqn:response_definition.
    + destruct x as [val rest].
      replace (all_aux processor fuel rest) with (all_aux processor (S (length text_tail)) rest).
      reflexivity.
      assert (length rest < length (text_head :: text_tail)). {
        apply processor_good with (response := val).
        apply response_definition.
      } {
      replace
        (all_aux processor (S (length text_tail)) rest)
      with
        (all_aux processor (S (length rest)) rest).
      apply IHn. simpl in H. lia. lia.
      apply IHn. simpl in H. lia.
      simpl in H. lia.
      }
    + reflexivity.
Qed.
