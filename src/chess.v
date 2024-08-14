Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Init.Datatypes.
Require Import Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.Classes.RelationClasses.

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
    unfold lt. intros. apply (@PeanoNat.Nat.lt_trans (square_to_nat x) (square_to_nat y) (square_to_nat z)). apply H0. apply H1.
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
Module Import SquareSet := FSetAVL.Make S.
Module SquareSetProp := WFacts_fun S.

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
  | Some (piece, enemy_color) => color_equal (invert color) enemy_color
  | None => false
  end.

Definition has_ally (b: Board) (sq: Square) (color: Color) :=
  match get_square b sq with
  | Some (piece, ally_color) => color_equal color ally_color
  | None => false
  end.

Definition square_empty b sq :=
  match get_square b sq with
  | Some _ => false
  | None => true
  end.

(* This is a little dumb but I can't think of anything better *)
(* while still convincing the compiler that it'll terminate *)
Definition cross (b: Board) (from: Square) (color: Color) :=
  let (file, rank) := from in
  let files: list File := [ A; B; C; D; E; F; G; H ] in
  let ranks: list Rank := [ R1; R2; R3; R4; R5; R6; R7; R8 ] in
  let (down, _) :=
    @fold_right (SquareSet.t * bool) Rank
      (fun r acc => let (can_move, hit) := acc in
                 if hit then
                   acc
                 else if Nat.ltb (rank_to_nat r) (rank_to_nat rank) then
                   if has_ally b (file, r) color then
                     (can_move, true)
                   else if has_enemy b (file, r) color then
                     (add (file, r) can_move, true)
                   else
                     (add (file, r) can_move, false)
                 else acc) (empty, false) ranks in
  let (up, _) :=
    @fold_left (SquareSet.t * bool) Rank
      (fun acc r => let (can_move, hit) := acc in
                 if hit then
                   acc
                 else if Nat.ltb (rank_to_nat rank) (rank_to_nat r) then
                   if has_ally b (file, r) color then
                     (can_move, true)
                   else if has_enemy b (file, r) color then
                     (add (file, r) can_move, true)
                   else
                     (add (file, r) can_move, false)
                      else acc) ranks (empty, false) in
  let (to_left, _) :=
    @fold_right (SquareSet.t * bool) File
      (fun f acc => let (can_move, hit) := acc in
                 if hit then
                   acc
                 else if Nat.ltb (file_to_nat f) (file_to_nat file) then
                   if has_ally b (f, rank) color then
                     (can_move, true)
                   else if has_enemy b (f, rank) color then
                     (add (f, rank) can_move, true)
                   else
                     (add (f, rank) can_move, false)
                 else acc) (empty, false) files in
  let (to_right, _) :=
    @fold_left (SquareSet.t * bool) File
      (fun acc f => let (can_move, hit) := acc in
                 if hit then
                   acc
                 else if Nat.ltb (file_to_nat file) (file_to_nat f) then
                   if has_ally b (f, rank) color then
                     (can_move, true)
                   else if has_enemy b (f, rank) color then
                     (add (f, rank) can_move, true)
                   else
                     (add (f, rank) can_move, false)
                 else acc) files (empty, false) in
  union (union (union down up) to_left) to_right.

Definition attacks (b: Board) (from: Square) : SquareSet.t :=
  let (from_file, from_rank) := from in
  let unwrap := fun o => match o with Some p => [p] | None => [] end in
  let flatten := flat_map unwrap in
  let flatten2 := flat_map (fun o => match o with Some o => unwrap o | None => [] end) in
  let flatten3 := flat_map (fun o => match o with Some o => match o with Some o => unwrap o | None => [] end | None => [] end) in
  match get_square b from with
  | Some (Pawn, color) =>
      match (rank_inc from_rank color) with
      | Some next_rank =>
          let left_attack :=
            match file_dec from_file with
            | Some next_file => add (next_file, next_rank) empty
            | None => empty
            end in
          let right_attack :=
            match file_inc from_file with
            | Some next_file => add (next_file, next_rank) empty
            | None => empty
            end in
          SquareSet.union left_attack right_attack
      | None => empty
      end
  | Some (King, color) =>
      let squares :=
        flatten [
            option_map (fun rank => (from_file, rank)) (rank_inc from_rank White);
            option_map (fun rank => (from_file, rank)) (rank_inc from_rank Black);
            option_map (fun file => (file, from_rank)) (file_inc from_file);
            option_map (fun file => (file, from_rank)) (file_dec from_file)
          ] ++ flatten2 [
            option_map (fun f => option_map (fun r => (f, r)) (rank_inc from_rank Black)) (file_inc from_file);
            option_map (fun f => option_map (fun r => (f, r)) (rank_inc from_rank Black)) (file_dec from_file);
            option_map (fun f => option_map (fun r => (f, r)) (rank_inc from_rank White)) (file_inc from_file);
            option_map (fun f => option_map (fun r => (f, r)) (rank_inc from_rank White)) (file_dec from_file)
          ] in
      fold_left (fun (acc: SquareSet.t) (elem: Square) => add elem acc) squares SquareSet.empty
  | Some (Horse, color) =>
      let squares :=
        flatten3 [
            option_map (fun f => option_map (fun f => option_map (fun r => (f, r)) (rank_inc from_rank White)) (file_inc f)) (file_inc from_file);
            option_map (fun f => option_map (fun f => option_map (fun r => (f, r)) (rank_inc from_rank Black)) (file_inc f)) (file_inc from_file);
            option_map (fun f => option_map (fun f => option_map (fun r => (f, r)) (rank_inc from_rank White)) (file_dec f)) (file_dec from_file);
            option_map (fun f => option_map (fun f => option_map (fun r => (f, r)) (rank_inc from_rank Black)) (file_dec f)) (file_dec from_file);
            option_map (fun r => option_map (fun r => option_map (fun f => (f, r)) (file_inc from_file)) (rank_inc r White)) (rank_inc from_rank White);
            option_map (fun r => option_map (fun r => option_map (fun f => (f, r)) (file_dec from_file)) (rank_inc r White)) (rank_inc from_rank White);
            option_map (fun r => option_map (fun r => option_map (fun f => (f, r)) (file_inc from_file)) (rank_inc r Black)) (rank_inc from_rank Black);
            option_map (fun r => option_map (fun r => option_map (fun f => (f, r)) (file_dec from_file)) (rank_inc r Black)) (rank_inc from_rank Black)
          ] in
      fold_left (fun (acc: SquareSet.t) (elem: Square) => add elem acc) squares SquareSet.empty
  | Some (Rook, color) => cross b from color
  | _ => empty
  end.

Definition is_attacked (b: Board) (original_square: Square) (original_color: Color) :=
  SquareMap.fold
    (fun square (piece_color: (Piece * Color)) acc =>
       let (piece, color) := piece_color in
       let piece_attacks := attacks b square in
       orb acc (andb (SquareSet.mem original_square piece_attacks) (color_equal (invert color) original_color))) b false.

Definition valid_moves (b: Board) (from: Square) (turn: Color) :=
  match get_square b from with
  | Some (piece, color) =>
      if color_equal color turn then
        match piece with
          | Pawn => 
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
                          add goal empty
                        else
                          empty in
                      add (from_file, next_rank) double
                    else empty in
                  let pawn_attacks := filter (fun sq => has_enemy b sq color) (attacks b from) in
                  union pawn_attacks forward_movement
              | None => empty
              end
        | King =>
            let attack_squares := attacks b from in
            filter (fun sq => andb (negb (is_attacked b sq color)) (negb (has_ally b sq color))) attack_squares
        | _ =>
            let attack_squares := attacks b from in
            filter (fun sq => negb (has_ally b sq color)) attack_squares
        end
      else empty
  | None => empty
  end.

Definition default_board :=
  SquareMap.add (C, R3) (Rook, White)
    (SquareMap.add (D, R4) (Horse, White)
       (SquareMap.add (B, R3) (King, Black) 
          (SquareMap.add (B, R2) (Pawn, White) (SquareMap.empty (Piece * Color))))).

Compute (elements (valid_moves default_board (C, R3) Black)).

Theorem king_cant_move_into_attack : forall b (from to : Square) color,
    get_square b from = Some (King, color) ->
    In to (valid_moves b from color) ->
    is_attacked b to color = false.
Proof.
  intros.
  unfold valid_moves in H1. unfold In in H1. rewrite H0 in H1. rewrite color_eq_refl in H1. apply filter_2 in H1.
  - apply andb_prop in H1. destruct H1. apply negb_true_iff in H1. apply H1.
  - unfold compat_bool. unfold Proper. unfold "==>". intros.
    rewrite square_eq_refl in H2. destruct H2. reflexivity.
Qed.

Theorem piece_cant_go_to_same_place : forall b (from: Square) piece color,
    get_square b from = Some (piece, color) ->
    ~ In from (valid_moves b from).
Proof. Admitted.

Theorem piece_cant_eat_same_color : forall b p1 p2 (from to: Square) c1 c2,
    get_square b from = Some (p1, c1) ->
    get_square b to = Some (p2, c2) ->
    SquareSet.In to (valid_moves b from) ->
    color_equal c1 c2 = false.
Proof. Admitted.

  (* intros. *)
  (* unfold valid_moves in H2. unfold In in H2. rewrite H0 in H2. destruct p1. *)
  (* - destruct from. destruct (rank_inc r c1). *)
  (*   + unfold square_empty in H2. destruct (get_square b (f, r0)). *)
  (*     * apply union_1 in H2. destruct H2. *)
  (*       -- apply filter_2 in H2. unfold has_enemy in H2. rewrite H1 in H2. unfold color_equal in *. destruct c1; destruct c2; simpl in *; symmetry in H2; try apply H2; reflexivity. *)
  (*          unfold compat_bool. unfold Proper. unfold "==>". intros. apply square_eq_refl in H3. destruct H3. reflexivity. *)
  (*       -- apply elements_1 in H2. unfold elements in H2. unfold MSet.elements in H2. unfold MSet.Raw.elements in H2. simpl in H2. apply InA_nil in H2. destruct H2. *)
  (*     * apply union_1 in H2. destruct H2. *)
  (*       -- apply filter_2 in H2. unfold has_enemy in H2. rewrite H1 in H2. unfold color_equal in *. destruct c1; destruct c2; simpl in *; symmetry in H2; try apply H2; reflexivity. *)
  (*          unfold compat_bool. unfold Proper. unfold "==>". intros. apply square_eq_refl in H3. destruct H3. reflexivity. *)
  (*       -- destruct c1; simpl in *. *)
  (*          --- destruct (rank_equal r R2). *)
  (*              ---- destruct (get_square b (f, R4)). *)

Inductive step : Board -> Color -> Type :=
| Checkmate board turn :
  forall square, (valid_moves b square turn) = empty ->
  step board turn
| Movement board turn piece from to:
  get_square board from = Some (piece, turn) ->
  SquareSet.In to (valid_moves board from) ->
  step (SquareMap.add to (piece, turn) board) (invert turn).
