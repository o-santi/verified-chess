Require Import board.
Require Import moves.
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.
Require Import Program.
Require Import Lia.

Inductive ParserError :=
| InvalidPiece
| InvalidFile 
| InvalidRank
| UnexpectedEOF
| Expected (c: ascii) (got: ascii).

Inductive Result {T} : Type :=
| Ok (x: T) : @Result T
| Err (err: ParserError) : @Result T
.

Arguments Ok {T}.
Arguments Err {T}.

Definition parser {T: Type} := list nat -> @Result (T * list nat).

Fixpoint to_list s : list nat :=
  match s with
  | EmptyString => []
  | String c s => (nat_of_ascii c) :: (to_list s)
  end.

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

Notation "'let*' p ':=' c1 'in' c2" := (bind c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

Definition parse_piece : @parser Piece :=
  fun s =>
    match s with
    | 81 :: l => Ok (Queen , l)
    | 82 :: l => Ok (Rook  , l)
    | 75 :: l => Ok (King  , l)
    | 80 :: l => Ok (Pawn  , l)
    | 78 :: l => Ok (Horse , l)
    | 66 :: l => Ok (Bishop, l)
    | _ => Err InvalidPiece
    end.

Definition parse_file : @parser File :=
  fun s =>
    match s with
    | 61 :: l | 97 :: l  => Ok (A, l)
    | 62 :: l | 98 :: l  => Ok (B, l)
    | 63 :: l | 99 :: l  => Ok (C, l)
    | 64 :: l | 100 :: l => Ok (D, l)
    | 65 :: l | 101 :: l => Ok (E, l)
    | 66 :: l | 102 :: l => Ok (F, l)
    | 67 :: l | 103 :: l => Ok (G, l)
    | 68 :: l | 104 :: l => Ok (H, l)
    | _ => Err InvalidFile
    end.

Definition parse_rank : @parser Rank :=
  fun s =>
    match s with
    | 49 :: l => Ok (R1, l)
    | 50 :: l => Ok (R2, l)
    | 51 :: l => Ok (R3, l)
    | 52 :: l => Ok (R4, l)
    | 53 :: l => Ok (R5, l)
    | 54 :: l => Ok (R6, l)
    | 55 :: l => Ok (R7, l)
    | 56 :: l => Ok (R8, l)
    | _ => Err InvalidRank
    end.

Definition parse_square : @parser Square :=
  fun s =>
    let* (file, s) := parse_file s in
    let* (rank, s) := parse_rank s in
    Ok ({| file:= file; rank:= rank|}, s).

Definition whitespace : @parser unit :=
  fix ws s :=
    match s with
    | 32 :: l | 10 :: l => let* (_, rest) := ws l in Ok (tt, rest)
    | _ => Ok (tt, s)
    end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (ascii_of_nat (48 + (n mod 10))) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".


Definition maybe {A} (p: @parser A) : @parser (option A) :=
  fun s =>
    match p s with
    | Ok (p, rest) => Ok (Some p, rest)
    | Err err => Ok (None, s)
    end.

Definition or {A} (p1 p2: @parser A) : @parser A :=
  fun s =>
    match p1 s with
    | Ok r => Ok r
    | Err _ => p2 s
    end.

Definition expect_char (a: ascii) : @parser unit :=
  fun s =>
    match s with
    | c :: rest => if Nat.eqb (nat_of_ascii a) c then
                   Ok (tt, rest)
                 else
                   Err (Expected a (ascii_of_nat c))
    | [] => Err UnexpectedEOF
    end.

Fixpoint expect_string (str: string) (rest: list nat) :=
  match str, rest with
  | String a s, n :: l =>
      if Nat.eqb (nat_of_ascii a) n then
        expect_string s l
      else
        Err (Expected a (ascii_of_nat n))
  | _, [] => Err UnexpectedEOF
  | EmptyString, _ => Ok (tt, rest)
  end.

Record SAN := {
    from_file : option File;
    from_rank : option Rank;
    to : Square;
    piece : Piece;
    captures : bool;
    check : bool;
  }.

Definition is_some {A} (o: option A) := match o with Some _ => true | None => false end.
Definition or_default {A} (a: A) (o: option A) : A := match o with Some x => x | None => a end.

Definition parse_san : @parser SAN :=
  fun s =>
    let* (p, rest) := (map (or_default Pawn) (maybe parse_piece)) s in
    let* (maybe_f, rest) := maybe parse_file rest in
    let* (maybe_r, rest) := maybe parse_rank rest in
    let* (captures, rest) := maybe (expect_char "x") rest in
    let* (sq, rest) := maybe parse_square rest in
    let* (check, rest) := maybe (expect_char "+") rest in
    let* (f, r, sq) :=
      match maybe_f, maybe_r, sq with
      | Some f, Some r, None => Ok (None, None, Build_Square f r)
      | _, _, Some sq => Ok (maybe_f, maybe_r, sq)
      | _, _, None => Err UnexpectedEOF
      end in
    Ok ({| piece := p; captures := is_some captures; from_file:=f; from_rank:=r; to:=sq; check:= is_some check |}, rest).

Fixpoint parse_game (game_state: GameState) (gas: nat) (s: list nat) : @Result (ValidGame game_state) :=
  match gas with
  | S g =>
      let* (_, rest)      := expect_string (writeNat turn) s in
      let* (_, rest)      := expect_char "." rest in
      let* (_, rest)      := whitespace rest in
      let* (w_move, rest) := parse_san rest in
      let* (_, rest)      := whitespace rest in
      let* (b_move, rest) := parse_san rest in
      let* (_, rest)      := whitespace rest in
      let* (games, rest)  := parse_game (turn + 1) g rest in
      Ok ((w_move, b_move)::games, rest)
  | 0 => Ok ([], s)
  end.

Compute (parse_game 1 4 (to_list "1. e4 e5 2. Nf3 Nc6 3. Bb5 a6 4. Ba4 Nf6")).
