From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import ZArith.

From Coq Require Import Lists.List. Import ListNotations.

Open Scope char_scope.

Inductive json : Type :=
| JNull
| JTrue
| JFalse
| JNumber : nat -> json
| JString : string -> json
| JList   : list json -> json
| JObject : list (string * json) -> json.

Inductive ParserError :=
| UnexpectedEOF
| Expected (c: ascii) (got: ascii).

Inductive Result {T} : Type :=
| Ok (x: T) : @Result T
| Err (err: ParserError) : @Result T.

Arguments Ok {T}.
Arguments Err {T}.

Definition parser {T} := string -> @Result (T * string).

Definition map {A B} (f: A -> B) (p: @parser A) : @parser B :=
  fun s =>
    match p s with
    | Ok (x, rest) => Ok (f x, rest)
    | Err err => Err err
    end.

Definition bind {A B} (r: @Result A) (f: A -> @Result B) :=
  match r with
  | Ok p => f p
  | Err err => Err err
  end.

Notation "'let*' p ':=' c1 'in' c2" :=
  (bind c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

Lemma n_not_less_than_10 : forall n, 10 + n < 10 -> False.
Proof.
  intros.
  repeat apply PeanoNat.lt_S_n in H.
  apply Nat.nlt_0_r in H. apply H.
Defined.

Definition ascii_of_nat (s: {n: nat | n < 10}) : ascii :=
  match s with
  | exist _ 0 _ => "0"
  | exist _ 1 _ => "1"
  | exist _ 2 _ => "2"
  | exist _ 3 _ => "3"
  | exist _ 4 _ => "4"
  | exist _ 5 _ => "5"
  | exist _ 6 _ => "6"
  | exist _ 7 _ => "7"
  | exist _ 8 _ => "8"
  | exist _ 9 _ => "9"
  | exist _ _ p => match n_not_less_than_10 _ p with end
  end.

Definition mod_10 (n: nat) : { m: nat | m < 10}.
Proof.
  intros.
  refine (exist _ (n mod 10) _).
  apply Nat.mod_upper_bound. apply Nat.neq_succ_0.
Defined.

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := ascii_of_nat (mod_10 n) in
  let acc' := String d acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n EmptyString.

Definition nat_of_ascii (char: ascii) : option nat :=
  match char with
  | "0" => Some 0
  | "1" => Some 1
  | "2" => Some 2
  | "3" => Some 3
  | "4" => Some 4
  | "5" => Some 5
  | "6" => Some 6
  | "7" => Some 7
  | "8" => Some 8
  | "9" => Some 9
  | _ => None
  end.

Fixpoint nat_of_string_aux (acc: nat) (s: string) : @Result (nat * string) :=
  match s with
  | EmptyString => Ok (acc, s)
  | String c s' =>
      match nat_of_ascii c with
      | Some n => nat_of_string_aux (10 * acc + n) s'
      | None => Err UnexpectedEOF
      end
  end.

Definition parse_nat : @parser nat :=
  fun s => nat_of_string_aux 0 s.

Open Scope string_scope.
Definition serialize_json (obj: json) : option string :=
  match obj with
  | JNull => Some "null"
  | JTrue => Some "true"
  | JFalse => Some "false"
  | JNumber n => Some (string_of_nat n)
  | _ => None
  end.
Close Scope string_scope.

Definition parse_null: @parser json :=
  fun s =>
    if prefix "null" s then
      Ok((JNull, substring 4 (String.length s) s))
    else Err UnexpectedEOF.

Definition parse_true: @parser json :=
  fun s =>
    if prefix "true" s then
      Ok((JTrue, substring 4 (String.length s) s))
    else Err UnexpectedEOF.

Definition parse_false: @parser json :=
  fun s =>
    if prefix "false" s then
      Ok((JFalse, substring 5 (String.length s) s))
    else Err UnexpectedEOF.
