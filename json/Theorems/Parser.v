Require Import Json.Parser.

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
