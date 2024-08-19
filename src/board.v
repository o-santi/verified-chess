Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FSetAVL.

Inductive File : Type := A | B | C | D | E | F | G | H.

Inductive Rank: Type := R1 | R2 | R3 | R4 | R5 | R6 | R7 | R8.

Record Square : Type := {
    file: File;
    rank: Rank;
  }.

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
  8 * (rank_to_nat rank) + (file_to_nat file).

Definition square_equal (sq1: Square) (sq2: Square) :=
  let (f1, r1) := sq1 in
  let (f2, r2) := sq2 in
  (andb (file_equal f1 f2) (rank_equal r1 r2)).

Theorem file_eq_refl : forall f1 f2, (file_equal f1 f2 = true) <-> f1 = f2.
Proof.
  split; intros.
  - unfold file_equal in H0. destruct f1; destruct f2; try discriminate; reflexivity.
  - destruct H0. unfold file_equal. destruct f1; reflexivity.
Defined.
    
Theorem rank_eq_refl : forall r1 r2, (rank_equal r1 r2 = true) <-> r1 = r2.
Proof.
  split; intros.
  - unfold file_equal in H0. destruct r1; destruct r2; try discriminate; reflexivity.
  - destruct H0. unfold file_equal. destruct r1; reflexivity.
Defined.

Theorem square_eq_refl : forall sq1 sq2, (square_equal sq1 sq2 = true) <-> sq1 = sq2.
Proof.
  split; intros; destruct sq1; destruct sq2.
  - unfold square_equal in H0. apply andb_prop in H0. destruct H0. apply file_eq_refl in H0. destruct H0. apply rank_eq_refl in H1. destruct H1. reflexivity.
  - destruct H0. unfold square_equal. destruct file0; destruct rank0; reflexivity.
Defined.

Theorem square_refl : forall sq1 sq2,
    square_to_nat sq1 = square_to_nat sq2 ->
    sq1 = sq2.
Proof.
  intros. destruct sq1; destruct sq2. destruct rank0; destruct rank1; simpl in H0; destruct file0; try discriminate; destruct file1; try discriminate; destruct H0; try reflexivity.
Qed.

Module S.
  Definition t := Square.
  Definition key := Square.
  Definition eq sq1 sq2 := square_equal sq1 sq2 = true.
  Definition lt sq1 sq2 := lt (square_to_nat sq1) (square_to_nat sq2).
  Theorem eq_refl : forall s, eq s s.
    unfold eq. intros. destruct s. destruct file0; destruct rank0; reflexivity.
  Qed.
  Theorem compare : forall (x y : S.t), OrderedType.Compare S.lt S.eq x y.
  Proof.
    intros. case_eq (Nat.compare (square_to_nat x) (square_to_nat y)); intro.
    - apply OrderedType.EQ. apply Compare_dec.nat_compare_eq in H0. apply square_refl in H0. destruct H0. apply eq_refl.
    - apply OrderedType.LT. apply Compare_dec.nat_compare_lt in H0. unfold lt. apply H0.
    - apply OrderedType.GT. apply Compare_dec.nat_compare_gt in H0. unfold lt. apply H0.
  Defined.
  Theorem eq_sym : forall x y : S.t, S.eq x y -> S.eq y x.
  Proof.
    intros. unfold eq in *. destruct x; destruct y. unfold square_equal in H0.
    apply andb_prop in H0. destruct H0. apply file_eq_refl in H0. apply rank_eq_refl in H1. destruct H0.
    destruct H1. apply eq_refl.
  Qed.
  Theorem eq_trans : forall x y z : S.t, S.eq x y -> S.eq y z -> S.eq x z.
  Proof.
    intros. unfold eq in *. destruct x. destruct y. destruct z.
    apply square_eq_refl in H0. apply square_eq_refl in H1. inversion H0; inversion H1; subst. apply eq_refl.
  Qed.
  Theorem lt_trans : forall x y z : S.t, S.lt x y -> S.lt y z -> S.lt x z.
  Proof.
    unfold lt. intros. apply (@PeanoNat.Nat.lt_trans (square_to_nat x) (square_to_nat y) (square_to_nat z)). apply H0. apply H1.
  Qed.
    
  Theorem lt_not_eq : forall x y : S.t, S.lt x y -> ~ S.eq x y.
  Proof.
    unfold eq. unfold lt. intros.
    destruct x. destruct y.
    destruct file0; destruct rank0; destruct file1; destruct rank1; intros contra; try discriminate; apply PeanoNat.Nat.lt_irrefl in H0; assumption. 
  Qed.
  Theorem eq_dec : forall x y : S.t, {S.eq x y} + {~ S.eq x y}.
  Proof.
    intros.
    unfold eq.
    destruct x; destruct y. destruct file0; destruct rank0; destruct file1; destruct rank1;
    try (left; reflexivity);
      right; discriminate.
  Qed.
End S.

Module Import SquareMap := FMapAVL.Make S.
Module Import SquareSet := FSetAVL.Make S.

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

Theorem color_eq_refl : forall c1, color_equal c1 c1 = true.
Proof.
  intros. destruct c1; reflexivity.
Qed.

Definition invert (c: Color) :=
  match c with
  | White => Black
  | Black => White
  end.

Record ColoredPiece := {
    piece: Piece;
    color: Color;
  }.

Definition Board : Type := SquareMap.t ColoredPiece.

Definition rank_inc (r: Rank) :=
  match r with
  |  R1 => Some R2
  |  R2 => Some R3
  |  R3 => Some R4
  |  R4 => Some R5
  |  R5 => Some R6
  |  R6 => Some R7
  |  R7 => Some R8
  |  R8 => None
  end.

Definition rank_dec (r: Rank) :=
  match r with
  | R1 => None
  | R2 => Some R1
  | R3 => Some R2
  | R4 => Some R3
  | R5 => Some R4
  | R6 => Some R5
  | R7 => Some R6
  | R8 => Some R7
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
