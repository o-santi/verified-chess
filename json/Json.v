From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import ZArith.
From Coq Require Import Strings.Byte.
From Coq Require Import Lists.List. Import ListNotations.

Open Scope char_scope.

Require Import Json.Parser.
Require Import Json.Utf8.

Local Notation "0" := false.
Local Notation "1" := true.

(* ============================================== *)
(* JSON parser implementation                     *)
(* ============================================== *)

Inductive nonzero :=
| D1 | D2 | D3
| D4 | D5 | D6
| D7 | D8 | D9.

Inductive digit :=
| Zero
| NonZero (n: nonzero).

Inductive sign :=
| Positive
| Negative.

Inductive integer :=
| IntegerZero
| MoreThanZero (first_digit: nonzero) (rest_digits: list digit).

Inductive exp_indicator :=
| Lowercase
| Uppercase.

Record exponent := {
    indicator: exp_indicator;
    exponent_sign: option sign;
    first_digit: digit;
    digits: list digit
  }.

Record fraction := {
    fst: digit;
    rest_digits: list digit;
  }.

Record number := {
    negative: bool;
    integer_part: integer;
    fractional_part: option fraction;
    exponent_part: option exponent
  }.

Inductive error_message :=
| ExpectedNonZero (got: option codepoint)
| ExpectedDigit (got: option codepoint)
| UnexpectedChar (c: option codepoint)
| ExpectedChar (c: codepoint) (got: option codepoint).

Inductive json : Type :=
| JNull
| JTrue
| JFalse
| JNumber (n: number)
| JString (s: unicode_str)
| JList   (l: list json)
| JObject (obj: list (unicode_str * json)).

Definition json_parser (T: Type) := @parser T codepoint error_message.

Definition expect (c: ascii) : json_parser codepoint :=
  predicate (codepoint_eqb (from_ascii c)) UnexpectedChar.

Definition not (c: ascii) : json_parser codepoint :=
  predicate (fun c' => negb (codepoint_eqb (from_ascii c) c')) (ExpectedChar (from_ascii c)).

Compute (from_ascii "0").

Definition parse_nonzero : json_parser nonzero :=
  fun s =>
    match s with
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (0, 0, 0, 1)) :: rest) => Ok (D1, rest)
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (0, 0, 1, 0)) :: rest) => Ok (D2, rest)
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (0, 0, 1, 1)) :: rest) => Ok (D3, rest)
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (0, 1, 0, 0)) :: rest) => Ok (D4, rest)
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (0, 1, 0, 1)) :: rest) => Ok (D5, rest)
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (0, 1, 1, 0)) :: rest) => Ok (D6, rest)
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (0, 1, 1, 1)) :: rest) => Ok (D7, rest)
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (1, 0, 0, 0)) :: rest) => Ok (D8, rest)
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (1, 0, 0, 1)) :: rest) => Ok (D9, rest)
    | c :: rest => Err (Error (ExpectedNonZero (Some c)))
    | [] => Err (Error (ExpectedNonZero None))
    end.

Definition parse_digit : json_parser digit :=
  fun s =>
    match s with
    | ((0, (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 0, 0), (0, 0, 1, 1), (0, 0, 0, 0)) :: rest) => Ok (Zero, rest)
    | other =>
        match parse_nonzero other with
        | Ok (d, rest) => Ok (NonZero d, rest)
        | Err err => Err (Error (ExpectedDigit (hd_error other)))
        end
    end.

Definition parse_integer : json_parser integer :=
  let parse_integer_zero := parser_map (fun _ => IntegerZero) (expect "0") in
  let parse_more_than_zero :=
    fun s =>
      let* (fst, rest) := parse_nonzero s in
      let* (rest_digits, rest) := many parse_digit rest in
      Ok (MoreThanZero fst rest_digits, rest) in
  any [ parse_integer_zero; parse_more_than_zero ].

Definition parse_fraction: json_parser fraction :=
  fun s =>
    let* (_dot, rest) := expect "." s in
    let* (fst, rest) := parse_digit rest in
    let* (digits, rest) := many parse_digit rest in
    Ok ({| fst:= fst; rest_digits:= digits |}, rest).

Definition parse_sign : json_parser sign :=
  any [ parser_map (fun _ => Negative) (expect "-");
        parser_map (fun _ => Positive) (expect "+") ].

Definition parse_exponent: json_parser exponent :=
  fun s =>
    let* (e, rest) := any [ parser_map (fun _ => Lowercase) (expect "e");
                            parser_map (fun _ => Uppercase) (expect "E") ] s in
    let* (sign, rest) := maybe parse_sign rest in
    let* (fst_digit, rest) := parse_digit rest in
    let* (digits, rest) := many parse_digit rest in
    Ok( {| indicator := e; exponent_sign := sign; digits:= digits; first_digit:= fst_digit |}, rest).

Definition parse_number: json_parser number :=
  fun s =>
    let* (negative, rest) := maybe (expect "-") s      in
    let* (integer, rest)  := parse_integer rest        in
    let* (fraction, rest) := maybe parse_fraction rest in
    let* (exponent, rest) := maybe parse_exponent rest in
    Ok({|
          negative := match negative with Some _ => true | None => false end;
          integer_part := integer;
          fractional_part := fraction;
          exponent_part := exponent
        |}, rest).

Definition map_or {A B: Type} (f: A -> B) (opt: option A) (default: B) : B :=
  match opt with Some c => f c | None => default end.

Definition serialize_nonzero (n: nonzero) : codepoint :=
  match n with
  | D1 => from_ascii "1"
  | D2 => from_ascii "2"
  | D3 => from_ascii "3"
  | D4 => from_ascii "4"
  | D5 => from_ascii "5"
  | D6 => from_ascii "6"
  | D7 => from_ascii "7"
  | D8 => from_ascii "8"
  | D9 => from_ascii "9"
  end.

Definition serialize_digit (d: digit) : codepoint :=
  match d with
  | Zero => from_ascii "0"
  | NonZero nz => serialize_nonzero nz
  end.


Definition serialize_integer (int: integer) : unicode_str :=
  match int with
  | IntegerZero => [(from_ascii "0")]
  | MoreThanZero fst rest => (serialize_nonzero fst) :: (map serialize_digit rest)
  end.

Definition serialize_sign (s: sign) : codepoint :=
  from_ascii match s with
  | Positive => "+"
  | Negative => "-"
  end.

Definition serialize_fraction (frac: fraction) : unicode_str :=
  [ (from_ascii "."); serialize_digit frac.(fst) ] ++ (map serialize_digit frac.(rest_digits)).

Definition serialize_exponent (exp: exponent) : unicode_str :=
  let indicator := from_ascii match exp.(indicator) with Lowercase => "e"| Uppercase => "E" end in
  let sign := match exp.(exponent_sign) with
              | Some s => [serialize_sign s]
              | None => []
              end in
  [ indicator ] ++ sign ++ [serialize_digit exp.(first_digit) ] ++ (map serialize_digit exp.(digits)).

Definition serialize_number (num: number) : unicode_str :=
  let sign := if num.(negative) then [ from_ascii "-" ] else [] in
  let integer_part := serialize_integer num.(integer_part) in
  let frac_part := map_or serialize_fraction num.(fractional_part) [] in
  let exponent := map_or serialize_exponent num.(exponent_part) [] in
  sign ++ integer_part ++ frac_part ++ exponent.

Definition number_str : unicode_str.
  refine (
      let str := to_unicode "-123e-999"%string in
      (match str as e return e = to_unicode "-123e-999"%string -> unicode_str with
       | Ok v => fun H => v
       | Err e => fun H => _
       end) (eq_refl str)).
  unfold to_unicode in H.
  discriminate.
Defined.

Compute (utf8_encode (serialize_number {|
            negative := 1;
            integer_part := MoreThanZero D1 [NonZero D2; NonZero D3];
            fractional_part := None;
            exponent_part :=
              Some
                {|
                  indicator := Lowercase;
                  exponent_sign := Some Negative;
                  first_digit := NonZero D9;
                  digits := [NonZero D9; NonZero D9]
                |}
          |})).

Definition serialize_json (obj: json) : unicode_str :=
  match obj with
  | JNull => to_unicode "null"%string
  | JTrue => to_unicode "true"%string
  | JFalse => to_unicode "false"%string
  (* | JNumber n => string_of_nat n *)
  (* | JString s => String "034"%char (s ++ (String "034"%char EmptyString)) *)
  | _ => to_unicode ""%string
  end.

(* Close Scope string_scope. *)

(* Definition parse_constant (c: json) : json_parser json := *)
(*   let const_string := serialize_json c in  *)
(*   fun s => *)
(*     if prefix const_string s then *)
(*       Ok((c, substring (String.length const_string) (String.length s) s)) *)
(*     else *)
(*       Err (Message "Expected " ++ const_string). *)
                        
(* Definition parse_null: json_parser json := parse_constant JNull. *)
(* Definition parse_true: json_parser json := parse_constant JTrue. *)
(* Definition parse_false: json_parser json := parse_constant JFalse. *)

(* Definition parse_string: json_parser json := *)
(*   fun s => *)
(*     let* (_, rest) := expect """" s in *)
(*     let* (s, rest) := many (not """") rest in *)
(*     let* (_, rest) := expect """" rest in *)
(*     Ok (JString (string_of_list_ascii (rev s)), rest). *)

(* Definition parse_object_aux (fuel: nat) (acc: list (string * json)) : json_parser json :=  *)

(* Definition parse_object: json_parser json :=  *)

(* Definition parse_value : json_parser json := *)
(*   any [ *)
(*       parse_number; *)
(*       parse_string; *)
(*       parse_null; *)
(*       parse_true; *)
(*       parse_false *)
(*     ]. *)
