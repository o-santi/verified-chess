Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Require Import Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx. 

Inductive File : Type := A | B | C | D | E | F | G | H.

Inductive Rank: Type := R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8.

Definition Square : Type := File * Rank.


Definition file_equal (f1: File) (f2: File) :=
  match f1, f2 with
  | A, A | B, B | C, C | D, D | E, E | F, F | G, G | H, H => true
  | _, _ => false
  end.

Definition rank_equal (r1: Rank) (r2: Rank) :=
  match r1, r2 with
  | R1, R1 | R2, R2 | R3, R3 | R4, R4 | R5, R5 | R6, R6 | R7, R7 | R8, R8 => true
  | _, _ => false
  end.

Definition file_to_nat (f: File) :=
  match f with
  | A => 0
  | B => 1
  | C => 2
  | D => 3
  | E => 4
  | F => 5
  | G => 6
  | H => 7
  end.

Definition rank_to_nat (r: Rank) :=
  match r with
  | R1 => 0
  | R2 => 1
  | R3 => 2
  | R4 => 3
  | R5 => 4
  | R6 => 5
  | R7 => 6
  | R8 => 7
  end.

Definition square_to_nat (s: Square) :=
  let (file, rank) := s in
  8 * (file_to_nat file) + (rank_to_nat rank).
                         
Definition square_equal (sq1: Square) (sq2: Square) :=
  let (f1, r1) := sq1 in
  let (f2, r2) := sq2 in
  (andb (file_equal f1 f2) (rank_equal r1 r2)).

Theorem square_eq_refl : forall sq1 sq2, (square_equal sq1 sq2 = true) <-> sq1 = sq2.
Proof.
  split; intros; destruct sq1; destruct sq2; destruct f; destruct r; destruct f0; destruct r0; try discriminate; reflexivity.
Qed.
  
Theorem square_refl : forall sq1 sq2,
    square_to_nat sq1 = square_to_nat sq2 ->
    sq1 = sq2.
Proof.
  intros. destruct sq1; destruct sq2. destruct f; destruct r; destruct f0; destruct r0; try discriminate; reflexivity.
Qed.

Module S.
  Definition t := Square.
  Definition eq sq1 sq2 := square_equal sq1 sq2 = true.
  Definition lt sq1 sq2 := lt (square_to_nat sq1) (square_to_nat sq2).
  Theorem eq_refl : forall s, eq s s.
    unfold eq. intros. destruct s. destruct f; destruct r; reflexivity.
  Qed.
  Definition compare : forall (x y : S.t), OrderedType.Compare S.lt S.eq x y.
  Proof.
    intros. case_eq (Nat.compare (square_to_nat x) (square_to_nat y)); intro.
    - apply OrderedType.EQ. apply Compare_dec.nat_compare_eq in H0. apply square_refl in H0. destruct H0. apply eq_refl.
    - apply OrderedType.LT. apply Compare_dec.nat_compare_lt in H0. unfold lt. apply H0.
    - apply OrderedType.GT. apply Compare_dec.nat_compare_gt in H0. unfold lt. apply H0.
  Defined.
  Theorem eq_sym : forall x y : S.t, S.eq x y -> S.eq y x.
  Proof.
    intros. unfold eq in *. destruct x; destruct y. destruct f; destruct r; destruct f0; destruct r0; try reflexivity; discriminate.
  Qed.
  Theorem eq_trans : forall x y z : S.t, S.eq x y -> S.eq y z -> S.eq x z.
  Proof.
    intros. unfold eq in *. destruct x. destruct y. destruct z. destruct f; destruct r; destruct f0; destruct r0; try discriminate; apply square_eq_refl in H1; rewrite H1; apply eq_refl.
  Qed.
  Theorem lt_trans : forall x y z : S.t, S.lt x y -> S.lt y z -> S.lt x z.
  Proof.
    unfold lt. intros. Search (?a < ?b -> ?b < ?c ->  ?a < ?c). Check PeanoNat.Nat.lt_trans. apply (@PeanoNat.Nat.lt_trans (square_to_nat x) (square_to_nat y) (square_to_nat z)). apply H0. apply H1.
  Qed.
    
  Theorem lt_not_eq : forall x y : S.t, S.lt x y -> ~ S.eq x y.
  Proof.
    unfold eq. unfold lt. intros.
    destruct x. destruct y.
    destruct f; destruct r; destruct f0; destruct r0; intros contra; try discriminate; apply PeanoNat.Nat.lt_irrefl in H0; assumption. 
  Qed.
  Theorem eq_dec : forall x y : S.t, {S.eq x y} + {~ S.eq x y}.
  Proof.
    intros.
    unfold eq.
    destruct x; destruct y. destruct f; destruct r; destruct f0; destruct r0;
    try (left; reflexivity);
      right; discriminate.
  Qed.
End S.

Module Import SquareMap := FMapAVL.Make S.

Inductive Piece : Type := Pawn | Queen | King | Bishop | Rook | Horse.

Definition piece_equal (p1 p2: Piece) :=
  match p1, p2 with
  | Pawn, Pawn | Queen, Queen | King, King | Bishop, Bishop | Rook, Rook | Horse, Horse => true
  | _, _ => false
  end.

Inductive Color : Type := White | Black.

Definition color_equal (c1: Color) (c2: Color) :=
  match c1, c2 with
  | White, White | Black, Black => true
  | _, _ => false
  end.

Definition invert (c: Color) :=
  match c with
  | White => Black
  | Black => White
  end.

Definition Board : Type := SquareMap.t (Piece * Color).

Definition rank_inc (r: Rank) (c: Color) :=
  match c, r with
  | White, R1 => Some R2
  | White, R2 => Some R3
  | White, R3 => Some R4
  | White, R4 => Some R5
  | White, R5 => Some R6
  | White, R6 => Some R7
  | White, R7 => Some R8
  | White, R8 => None
  | Black, R1 => None
  | Black, R2 => Some R1
  | Black, R3 => Some R2
  | Black, R4 => Some R3
  | Black, R5 => Some R4
  | Black, R6 => Some R5
  | Black, R7 => Some R6
  | Black, R8 => Some R7
  end.

Definition file_inc (r: File) :=
  match r with
  | A => Some B
  | B => Some C
  | C => Some D
  | D => Some E
  | E => Some F
  | F => Some G
  | G => Some H
  | H => None
  end.

Definition file_dec (r: File) :=
  match r with
  | A => None
  | B => Some A
  | C => Some B
  | D => Some C
  | E => Some D
  | F => Some E
  | G => Some F
  | H => Some G
  end.


Definition get_square (b: Board) (sq1: Square) := SquareMap.find sq1 b.

Definition double_movement (c: Color) :=
  match c with
  | White => (R2, R4)
  | Black => (R7, R5)
  end.

Definition is_king (p: Piece) :=
  match p with
  | King => true
  | _ => false
  end.

Definition has_enemy (b: Board) (sq: Square) (color: Color) :=
  match get_square b sq with
  | Some (piece, enemy_color) => color_equal color (invert enemy_color)
  | None => false
  end.

Definition square_empty b sq :=
  match get_square b sq with
  | Some _ => false
  | None => true
  end.

Definition attacks (b: Board) (from: Square) :=
  let (from_file, from_rank) := from in
  match get_square b from with
  | Some (Pawn, color) =>
      match (rank_inc from_rank color) with
      | Some next_rank =>
          let left_attack :=
            match file_dec from_file with
            | Some next_file => 
                if has_enemy b (next_file, next_rank) color then
                  (next_file, next_rank) :: nil
                else
                  nil
            | None => nil
            end in
          let right_attack :=
            match file_inc from_file with
            | Some next_file => 
                if has_enemy b (next_file, next_rank) color then
                  (next_file, next_rank) :: nil
                else
                  nil
            | None => nil
            end in
          concat (left_attack :: right_attack :: nil)
      | None => nil
      end
  | _ => nil
  end.

Definition valid_moves (b: Board) (from: Square) :=
  match get_square b from with
  | Some (Pawn, color) =>
      let (from_file, from_rank) := from in
      let next_rank := rank_inc from_rank color in
      match next_rank with
      | Some next_rank =>
          let forward_movement :=
            if square_empty b (from_file, next_rank) then
              let (start_rank, jump_rank) := double_movement color in
              let goal := (from_file, jump_rank) in
              let double :=
                if andb (rank_equal from_rank start_rank) (square_empty b goal) then
                  goal :: nil
                else
                  nil in
              (from_file, next_rank) :: double
            else nil in
          concat ((attacks b from) :: forward_movement :: nil)
      | None => nil
      end
  (* | Some (King, color) => *)
  | _ => nil
  end.

Definition default_board :=
  SquareMap.add (A, R4) (Pawn, Black)
    (SquareMap.add (B, R3) (Pawn, Black)
       (SquareMap.add (A, R2) (Pawn, White) (empty (Piece * Color)))).

Compute (attacks default_board (A, R2)).
 
Inductive step : Board -> Color -> Type :=
| Movement board turn piece from to:
  get_square board from = Some (piece, turn) ->
  List.In to (valid_moves board from) ->
  step (SquareMap.add to (piece, turn) board) (invert turn).
