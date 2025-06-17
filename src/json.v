From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.Byte.
From Coq Require Import ZArith.

From Coq Require Import Lists.List. Import ListNotations.

Open Scope char_scope.

Inductive nonzero :=
| D1 | D2 | D3
| D4 | D5 | D6
| D7 | D8 | D9.

Inductive digit :=
| Zero
| NonZero : nonzero -> digit.

Inductive sign :=
| Positive
| Negative.

Inductive integer :=
| IntegerZero
| MoreThanZero (first_digit: nonzero) (rest_digits: list digit).

Record exponent := {
    exponent_sign: option sign;
    first_digit: digit;
    digits: list digit
  }.

Record number := {
    negative: bool;
    integer_part: integer;
    fractional_part: list digit;
    exponent_part: option exponent
  }.

Definition codepoint : Type := (byte * byte * byte * byte).
Definition unicode_str : Type := list codepoint.

Inductive json : Type :=
| JNull
| JTrue
| JFalse
| JNumber (n: number)
| JString (s: unicode_str)
| JList   (l: list json)
| JObject (obj: list (unicode_str * json)).

Definition codepoint_eqb (a b: codepoint) : bool :=
  let '(a1, a2, a3, a4) := a in
  let '(b1, b2, b3, b4) := b in
  (eqb a1 b1) && (eqb a2 b2) && (eqb a3 b3) && (eqb a4 b4).

Definition from_ascii (c: ascii) : codepoint :=
  let b := byte_of_ascii c in
  (b, x00, x00, x00).

Inductive error_message :=
| UnexpectedEOF
| UnexpectedChar (c: codepoint)
| ExpectedChar (c: codepoint) (got: codepoint).

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

Definition parser {T: Type} := unicode_str -> @result (T * unicode_str) (list error_message).

Definition parser_map {A B} (f: A -> B) (p: @parser A) : @parser B :=
  fun s =>
    let* (x, rest) := p s in
    Ok (f x, rest).

Definition maybe {A} (p: @parser A) : @parser (option A) :=
  fun s =>
    match p s with
    | Ok (x, rest) => Ok (Some x, rest)
    | Err _        => Ok (None, s)
    end.

Fixpoint any_aux {A} (parsers: list (@parser A)) (errs: list error_message) : @parser A :=
  fun s =>
    match parsers with
    | [] => Err errs
    | p :: rest =>
        match p s with
        | Err err => any_aux rest (err ++ errs) s
        | Ok p => Ok p
        end
    end.

Definition any {A} (parsers : list (@parser A)): @parser A := any_aux parsers [].

Definition predicate (pred: codepoint -> bool) (err: codepoint -> error_message) : @parser codepoint :=
  fun s => 
    match s with
    | [] => Err [ UnexpectedEOF ]
    | c :: rest =>
        match pred c with
        | true => Ok (c, rest)
        | false => Err [ err c ]
        end
    end.

Definition expect (c: ascii) : @parser codepoint :=
  predicate (codepoint_eqb (from_ascii c)) UnexpectedChar.

Definition not (c: ascii) : @parser codepoint :=
  predicate (fun c' => negb (codepoint_eqb (from_ascii c) c')) (ExpectedChar (from_ascii c)).

Fixpoint many_aux { A } (p: @parser A) (acc: list A) (fuel: nat) : @parser (list A) :=
  fun s => 
    match fuel with
    | 0 => Ok (acc, s)
    | S fuel' =>
        match p s as res with
        | Ok (val, rest) => many_aux p (val :: acc) fuel' rest
        | Err _ => Ok (acc, s)
        end
    end.

Definition many {A} (p: @parser A): @parser (list A) :=
  fun s => many_aux p [] (S (length s)) s.

(* ============================================== *)
(* JSON parser implementation                     *)
(* ============================================== *)

Definition parse_nonzero : @parser nonzero :=
  let p digit char := parser_map (fun _ => digit) (expect char) in
  any [
      p D1 "1"; p D2 "2"; p D3 "3";
      p D4 "4"; p D5 "5"; p D6 "6";
      p D7 "7"; p D8 "8"; p D9 "9"
    ].

Definition parse_digit : @parser digit :=
  let z := parser_map (fun _ => Zero) (expect "0") in
  let n := parser_map NonZero parse_nonzero in
  any [z; n].

Definition parse_integer : @parser integer :=
  let parse_integer_zero := parser_map (fun _ => IntegerZero) (expect "0") in
  let parse_more_than_zero :=
    fun s =>
      let* (fst, rest) := parse_nonzero s in
      let* (rest_digits, rest) := many parse_digit rest in
      Ok (MoreThanZero fst rest_digits, rest) in
  any [ parse_integer_zero; parse_more_than_zero ].

Definition parse_fraction: @parser (list digit) :=
  fun s =>
    let* (_dot, rest) := expect "." s in
    let* (digits, rest) := many parse_digit rest in
    Ok (digits, rest).

Definition parse_sign : @parser sign :=
  any [ parser_map (fun _ => Negative) (expect "-");
        parser_map (fun _ => Positive) (expect "+") ].

Definition parse_exponent: @parser exponent :=
  fun s =>
    let* (_e, rest) := any [ expect "e"; expect "E" ] s in
    let* (sign, rest) := maybe parse_sign rest in
    let* (fst_digit, rest) := parse_digit rest in
    let* (digits, rest) := many parse_digit rest in
    Ok( {| exponent_sign := sign; digits:= digits; first_digit:= fst_digit |}, rest).

Definition parse_number: @parser number :=
  fun s =>
    let* (negative, rest) := maybe (expect "-") s      in
    let* (integer, rest)  := parse_integer rest        in
    let* (fraction, rest) := maybe parse_fraction rest in
    let* (exponent, rest) := maybe parse_exponent rest in
    Ok({|
          negative := match negative with Some _ => true| None => false end;
          integer_part := integer;
          fractional_part := match fraction with Some l => l | None => [] end;
          exponent_part := exponent
        |}, rest).

Require Extraction.
Extraction parse_number.

Definition serialize_json (obj: json) : unicode_str :=
  match obj with
  | JNull => "null"
  | JTrue => "true"
  | JFalse => "false"
  | JNumber n => string_of_nat n
  | JString s => String "034"%char (s ++ (String "034"%char EmptyString))
  | _ => ""
  end.

Compute (serialize_json (JString "hello world")).
Close Scope string_scope.

Definition parse_constant (c: json) : @parser json :=
  let const_string := serialize_json c in 
  fun s =>
    if prefix const_string s then
      Ok((c, substring (String.length const_string) (String.length s) s))
    else
      Err (Message "Expected " ++ const_string).
                        
Definition parse_null: @parser json := parse_constant JNull.
Definition parse_true: @parser json := parse_constant JTrue.
Definition parse_false: @parser json := parse_constant JFalse.

Definition parse_string: @parser json :=
  fun s =>
    let* (_, rest) := expect """" s in
    let* (s, rest) := many (not """") rest in
    let* (_, rest) := expect """" rest in
    Ok (JString (string_of_list_ascii (rev s)), rest).

Definition parse_object_aux (fuel: nat) (acc: list (string * json)) : @parser json := 

Definition parse_object: @parser json := 

Compute (parse_string (serialize_json (JString "hello world"))).

Definition parse_value : @parser json :=
  any [
      parse_number;
      parse_string;
      parse_null;
      parse_true;
      parse_false
    ].
