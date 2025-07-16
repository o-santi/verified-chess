From Coq Require Import Lists.List. Import ListNotations.

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

Definition many {A I E} (p: @parser A I E): @parser (list A) I E :=
  fun s => many_aux p (S (length s)) s.

Fixpoint all_aux { A I E} (p: @parser A I E) (fuel: nat) : @parser (list A) I E :=
  fun s => 
    match fuel with
    | 0 => Ok ([], s)
    | S fuel' =>
        match s with
        | [] => Ok ([], s)
        | _ => 
            match p s with
            | Err e => Err e
            | Ok (val, rest) =>
                let* (vals, rest) := all_aux p fuel' rest in
                Ok (val :: vals, rest)
            end
        end
    end.

Definition all {A I E} (p: @parser A I E): @parser (list A) I E :=
  fun s => all_aux p (S (length s)) s.

(* Fixpoint repeat_n {T I E} (n: nat) (p: @parser T I E) : @parser (Vector.t T n) I E := *)
(*   fun s => *)
(*     match n with *)
(*     | 0 => Ok (nil T, s) *)
(*     | S n' => *)
(*         let* (val, rest) := p s in *)
(*         let* (vals, rest) := repeat_n n' p rest in *)
(*         Ok (cons T val n' vals, rest) *)
(*     end. *)
