From Coq Require Import Lists.List. Import ListNotations.
Require Import Lia.

Inductive result {T E: Type} : Type :=
| Ok (x: T) : @result T E
| Err (err: E) : @result T E.

Arguments Ok {T E}.
Arguments Err {T E}.

Definition bind {A B E} (r: @result A E) (f: A -> @result B E) :=
  match r with
  | Ok p => f p
  | Err err => Err err
  end.

Notation "'let*' p ':=' c1 'in' c2" :=
  (bind c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

Definition fmap { A B E } (f: A -> B) (r: @result A E) : @result B E :=
  bind r (fun x => Ok (f x)).

Inductive error {E: Type}: Type :=
| NoError
| Error (e: E)
| Both (left: @error E) (right: @error E).

Definition parser (T: Type) {I E: Type} := list I -> @result (T * (list I)) (@error E).

Definition parser_map {A B I E} (f: A -> B) (p: @parser A I E) : @parser B I E :=
  fun s =>
    let* (x, rest) := p s in
    Ok (f x, rest).

Definition maybe {A I E} (p: @parser A I E) : @parser (option A) I E :=
  fun s =>
    match p s with
    | Ok (x, rest) => Ok (Some x, rest)
    | Err _        => Ok (None, s)
    end.

Fixpoint any_aux {A I E} (parsers: list (@parser A I E)) (errs: @error E) : @parser A I E :=
  fun s =>
    match parsers with
    | [] => Err errs
    | p :: rest =>
        match p s with
        | Err err => any_aux rest (Both err errs) s
        | Ok p => Ok p
        end
    end.

Definition any {A I E} (parsers : list (@parser A I E)): @parser A I E := any_aux parsers NoError.

Definition predicate {I E} (pred: I -> bool) (err: option I -> E) : @parser I I E :=
  fun s => 
    match s with
    | [] => Err (Error (err None))
    | c :: rest =>
        match pred c with
        | true => Ok (c, rest)
        | false => Err (Error (err (Some c)))
        end
    end.

Fixpoint many_aux { A I E} (p: @parser A I E) (fuel: nat) : @parser (list A) I E :=
  fun s => 
    match fuel with
    | 0 => Ok ([], s)
    | S fuel' =>
        match p s with
        | Err _ => Ok ([], s)
        | Ok (val, rest) =>
            let* (vals, rest) := many_aux p fuel' rest in
            Ok (val :: vals, rest)
        end
    end.

Theorem many_aux_saturation_aux : forall A I E processor,
  (forall suffix response text,
    Ok (response, suffix) = processor text ->
    length suffix < length text) ->
  forall n text fuel,
  length text < n ->
  length text <= fuel ->
  @many_aux A I E processor (length text) text = @many_aux A I E processor fuel text.
Proof.
  intros A I E processor processor_good.
  induction n; intros text fuel.
  - intros H. inversion H.
  - intros text_bounded enough_fuel.
    destruct text as [|text_head text_tail].
    destruct fuel; simpl. reflexivity. destruct (processor []) eqn:response_definition.
    destruct x as [response suffix].
    exfalso. assert (@length I suffix < @length I []).
    apply processor_good with (response := response) (suffix := suffix).
    symmetry. apply response_definition.
    inversion H.
    reflexivity. simpl in text_bounded. 
    destruct fuel. exfalso. inversion enough_fuel.
    simpl. destruct (processor (text_head :: text_tail)) eqn:response_definition.
    + destruct x as [val rest].
      replace (many_aux processor fuel rest) with (many_aux processor (length text_tail) rest).
      reflexivity.
      assert (length rest < length (text_head :: text_tail)). {
        apply processor_good with (response := val).
        symmetry. apply response_definition.
      } {
      replace
        (many_aux processor (length text_tail) rest)
      with
        (many_aux processor (length rest) rest).
      apply IHn. simpl in H. lia. lia.
      apply IHn. simpl in H. lia.
      simpl in H. lia.
      }
    + reflexivity.
Qed.

Definition many {A I E} (p: @parser A I E): @parser (list A) I E :=
  fun s => many_aux p (S (length s)) s.

(* Fixpoint repeat_n {T I E} (n: nat) (p: @parser T I E) : @parser (Vector.t T n) I E := *)
(*   fun s => *)
(*     match n with *)
(*     | 0 => Ok (nil T, s) *)
(*     | S n' => *)
(*         let* (val, rest) := p s in *)
(*         let* (vals, rest) := repeat_n n' p rest in *)
(*         Ok (cons T val n' vals, rest) *)
(*     end. *)
