From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import ZArith.

From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Vectors.Vector.

From Coq Require Import Strings.Byte.

Search Vector.t.

Open Scope char_scope.
  
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

Definition parser (T: Type) {I E: Type} := list I -> @result (T * (list I)) (list E).

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

Fixpoint any_aux {A I E} (parsers: list (@parser A I E)) (errs: list E) : @parser A I E :=
  fun s =>
    match parsers with
    | [] => Err errs
    | p :: rest =>
        match p s with
        | Err err => any_aux rest (err ++ errs) s
        | Ok p => Ok p
        end
    end.

Definition any {A I E} (parsers : list (@parser A I E)): @parser A I E := any_aux parsers [].

Definition predicate {I E} (pred: I -> bool) (err: option I -> E) : @parser I I E :=
  fun s => 
    match s with
    | [] => Err [ err None ]
    | c :: rest =>
        match pred c with
        | true => Ok (c, rest)
        | false => Err [ err (Some c) ]
        end
    end.

Fixpoint many_aux { A I E} (p: @parser A I E) (acc: list A) (fuel: nat) : @parser (list A) I E :=
  fun s => 
    match fuel with
    | 0 => Ok (acc, s)
    | S fuel' =>
        match p s as res with
        | Ok (val, rest) => many_aux p (val :: acc) fuel' rest
        | Err _ => Ok (acc, s)
        end
    end.

Definition many {A I E} (p: @parser A I E): @parser (list A) I E :=
  fun s => many_aux p [] (S (length s)) s.

Fixpoint repeat_n {T I E} (n: nat) (p: @parser T I E) : @parser (Vector.t T n) I E :=
  fun s =>
    match n with
    | 0 => Ok (nil T, s)
    | S n' =>
        let* (val, rest) := p s in
        let* (vals, rest) := repeat_n n' p rest in
        Ok (cons T val n' vals, rest)
    end.

(* ============================================== *)
(* UTF-8 encoding and decoding                    *)
(* ============================================== *)


Definition b3 : Type := bool * bool * bool.
Definition b4 : Type := bool * bool * bool * bool.
Definition b5 : Type := bool * bool * bool * bool * bool.
Definition b6 : Type := bool * bool * bool * bool * bool * bool.
Definition b7 : Type := bool * bool * bool * bool * bool * bool * bool.

Definition b7_zero: b7 := (false, false, false, false, false, false, false).

Open Scope bool_scope.

Definition b7_equal (a b: b7) : bool :=
  let '(a1, a2, a3, a4, a5, a6, a7) := a in
  let '(b1, b2, b3, b4, b5, b6, b7) := b in
  (xorb a1 b1) && (xorb a2 b2) && (xorb a3 b3) && (xorb a4 b4) && (xorb a5 b5) && (xorb a6 b6) && (xorb a7 b7).


Definition continuation : Type := (bool * bool * bool * bool * bool * bool).

Inductive codepoint_range :=
| FirstRange (b: b7)
| SecondRange (fst: b5) (snd: b6)
| ThirdRange (fst: b4) (snd: b6) (trd: b6)
| FourthRange (fst: b3) (snd: b6) (trd: b6) (frth: b6).

Inductive unicode_error :=
| UnicodeUnexpectedEOF
| OverlongEncoding (cr: codepoint_range)
| InvalidContinuationHeader (x: byte)
| InvalidStartHeader (x: byte)
| IllegalSurrogatePair
| IllegalCodepoint.

Inductive encoding_size :=
| OneByte (b: b7)
| TwoBytes (b: b5)
| ThreeBytes (b: b4)
| FourBytes (b: b3).

Definition codepoint : Type := b7 * b7 * b7.

Definition codepoint_to_nat (c: codepoint) : nat :=
  

Definition codepoint_range_to_codepoint (cr: codepoint_range) : option codepoint :=
  match cr with
  | FirstRange b => Some (b, b7_zero, b7_zero)
  | _ => None
  end.

Definition unicode_str : Type := list codepoint.

Definition codepoint_eqb (a b: codepoint) : bool :=
  let '(a1, a2, a3) := a in
  let '(b1, b2, b3) := b in
  b7_equal a1 b1 && b7_equal a2 b2 && b7_equal a3 b3.

Definition from_ascii (c: ascii) : codepoint :=
  let '(_, (b1, (b2, (b3, (b4, (b5, (b6, b7))))))) := to_bits (byte_of_ascii c) in
  ((b1, b2, b3, b4, b5, b6, b7), b7_zero, b7_zero).

Definition encoding_size_from_header (b: byte) : option encoding_size :=
  match to_bits b with
  | (b1, (b2, (b3, (b4, (b5, (b6, (b7, false))))))) => Some (OneByte (b1, b2, b3, b4, b5, b6, b7))
  | (b1, (b2, (b3, (b4, (b5, (false, (true, true))))))) => Some (TwoBytes (b1, b2, b3, b4, b5))
  | (b1, (b2, (b3, (b4, (false, (true, (true, true))))))) => Some (ThreeBytes (b1, b2, b3, b4))
  | (b1, (b2, (b3, (false, (true, (true, (true, true))))))) => Some (FourBytes (b1, b2, b3))
  | _ => None
  end. 

Definition parse_continuation : @parser continuation byte unicode_error :=
  let continuation_from_byte :=
    fun b =>
      let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := to_bits b in
      (b1, b2, b3, b4, b5, b6) in
  let is_continuation :=
    fun (b: byte) =>
      let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := to_bits b in
      andb b8 (negb b7) in
  let handle_err_char :=
    fun c => match c with
          | Some c' => InvalidContinuationHeader c'
          | None => UnicodeUnexpectedEOF
          end in
  parser_map continuation_from_byte (predicate is_continuation handle_err_char).

Definition parse_header : @parser encoding_size byte unicode_error :=
  fun s =>
    match s with
    | [] => Err [ UnicodeUnexpectedEOF ]
    | h :: rest =>
        match encoding_size_from_header h with
        | None => Err [ InvalidStartHeader h ]
        | Some e => Ok (e, rest)
        end
    end.

Definition parse_codepoint : @parser codepoint byte unicode_error :=
  fun s =>
    let* (size, rest) := parse_header s in
    let* (codepoint_bits, rest) :=
      match size with
      | OneByte fst => Ok (FirstRange fst, rest)
      | TwoBytes fst =>
          let* (snd, rest) := parse_continuation rest in
          Ok (SecondRange fst snd, rest)
      | ThreeBytes fst =>
          let* (snd, rest) := parse_continuation rest in
          let* (trd, rest) := parse_continuation rest in
          Ok (ThirdRange fst snd trd, rest)
      | FourBytes fst =>
          let* (snd,  rest) := parse_continuation rest in
          let* (trd,  rest) := parse_continuation rest in
          let* (frth, rest) := parse_continuation rest in
          Ok (FourthRange fst snd trd frth, rest)
      end in
    match codepoint_range_to_codepoint codepoint_bits with
    | Some code => Ok (code, rest)
    | None      => Err [ OverlongEncoding codepoint_bits ]
    end.

Definition utf8_decode : @parser unicode_str byte unicode_error :=
  many parse_codepoint.

Compute (utf8_decode (List.map byte_of_ascii (list_ascii_of_string "hello"))).

Definition from_unicode_str (s: unicode_str) : option string.
  Admitted.

(* ============================================== *)
(* JSON parser implementation                     *)
(* ============================================== *)

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

Inductive error_message :=
| UnexpectedEOF
| UnexpectedChar (c: codepoint)
| ExpectedChar (c: codepoint) (got: codepoint).

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
  predicate (codepoint_eqb (from_ascii c))
    (fun c' => match c' with
            | Some c' => UnexpectedChar c'
            | None   => UnexpectedEOF
            end).

Definition not (c: ascii) : json_parser codepoint :=
  predicate (fun c' => negb (codepoint_eqb (from_ascii c) c'))
    (fun c' => match c' with
            | Some c' => ExpectedChar (from_ascii c) c'
            | None => UnexpectedEOF
            end).

Definition parse_nonzero : json_parser nonzero :=
  let p digit char := parser_map (fun _ => digit) (expect char) in
  any [
      p D1 "1"; p D2 "2"; p D3 "3";
      p D4 "4"; p D5 "5"; p D6 "6";
      p D7 "7"; p D8 "8"; p D9 "9"
    ].

Definition parse_digit : json_parser digit :=
  let z := parser_map (fun _ => Zero) (expect "0") in
  let n := parser_map NonZero parse_nonzero in
  any [z; n].

Definition parse_integer : json_parser integer :=
  let parse_integer_zero := parser_map (fun _ => IntegerZero) (expect "0") in
  let parse_more_than_zero :=
    fun s =>
      let* (fst, rest) := parse_nonzero s in
      let* (rest_digits, rest) := many parse_digit rest in
      Ok (MoreThanZero fst rest_digits, rest) in
  any [ parse_integer_zero; parse_more_than_zero ].

Definition parse_fraction: json_parser (list digit) :=
  fun s =>
    let* (_dot, rest) := expect "." s in
    let* (digits, rest) := many parse_digit rest in
    Ok (digits, rest).

Definition parse_sign : json_parser sign :=
  any [ parser_map (fun _ => Negative) (expect "-");
        parser_map (fun _ => Positive) (expect "+") ].

Definition parse_exponent: json_parser exponent :=
  fun s =>
    let* (_e, rest) := any [ expect "e"; expect "E" ] s in
    let* (sign, rest) := maybe parse_sign rest in
    let* (fst_digit, rest) := parse_digit rest in
    let* (digits, rest) := many parse_digit rest in
    Ok( {| exponent_sign := sign; digits:= digits; first_digit:= fst_digit |}, rest).

Definition parse_number: json_parser number :=
  fun s =>
    let* (negative, rest) := maybe (expect "-") s      in
    let* (integer, rest)  := parse_integer rest        in
    let* (fraction, rest) := maybe parse_fraction rest in
    let* (exponent, rest) := maybe parse_exponent rest in
    Ok({|
          negative := match negative with Some _ => true | None => false end;
          integer_part := integer;
          fractional_part := match fraction with Some l => l | None => [] end;
          exponent_part := exponent
        |}, rest).

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

Definition parse_constant (c: json) : json_parser json :=
  let const_string := serialize_json c in 
  fun s =>
    if prefix const_string s then
      Ok((c, substring (String.length const_string) (String.length s) s))
    else
      Err (Message "Expected " ++ const_string).
                        
Definition parse_null: json_parser json := parse_constant JNull.
Definition parse_true: json_parser json := parse_constant JTrue.
Definition parse_false: json_parser json := parse_constant JFalse.

Definition parse_string: json_parser json :=
  fun s =>
    let* (_, rest) := expect """" s in
    let* (s, rest) := many (not """") rest in
    let* (_, rest) := expect """" rest in
    Ok (JString (string_of_list_ascii (rev s)), rest).

Definition parse_object_aux (fuel: nat) (acc: list (string * json)) : json_parser json := 

Definition parse_object: json_parser json := 

Definition parse_value : json_parser json :=
  any [
      parse_number;
      parse_string;
      parse_null;
      parse_true;
      parse_false
    ].
