Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Require Import Coq.Init.Datatypes.
Require Import Program.
Require Import Lia.
Require Import board.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FSetProperties.
Require Import Coq.Relations.Relation_Operators.

Module SquareMapProp := Coq.FSets.FMapFacts.WProperties_fun S SquareMap.
Module SquareSetProp := Coq.FSets.FSetProperties.WProperties_fun S SquareSet.
Module OrdSquareMapProp := Coq.FSets.FMapFacts.OrdProperties SquareMap.

Inductive Direction :=
| Up
| Down
| Left
| Right
| UpLeft
| UpRight
| DownLeft
| DownRight.

Definition square_inc_rank (sq: Square) := option_map (fun r => {| file:=sq.(file); rank:= r|}) (rank_inc sq.(rank)).
Definition square_dec_rank (sq: Square) := option_map (fun r => {| file:=sq.(file); rank:= r|}) (rank_dec sq.(rank)).
Definition square_inc_file (sq: Square) := option_map (fun f => {| file:=f; rank:= sq.(rank)|}) (file_inc sq.(file)).
Definition square_dec_file (sq: Square) := option_map (fun f => {| file:=f; rank:= sq.(rank)|}) (file_dec sq.(file)).
Definition opt_flatten {A} (o: option (option A)) := match o with Some p => p | None => None end.
Definition bind {A B} (f: A -> option B) (o: option A) :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition move_to (d: Direction) (from: Square) :=
  match d with
  | Up    => square_inc_rank from
  | Down  => square_dec_rank from
  | Right => square_inc_file from
  | Left  => square_dec_file from
  | UpRight   => bind square_inc_rank (square_inc_file from)
  | UpLeft    => bind square_inc_rank (square_dec_file from)
  | DownRight => bind square_dec_rank (square_inc_file from)
  | DownLeft  => bind square_dec_rank (square_dec_file from)
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

Definition has_ally (b: Board) (sq: Square) (color: Color) :=
  match get_square b sq with
  | Some {| color := ally_color; piece := piece |} => color_equal color ally_color
  | None => false
  end.

Definition has_enemy (b: Board) (sq: Square) (color: Color) := has_ally b sq (invert color).

Definition square_empty b sq :=
  match get_square b sq with
  | Some _ => false
  | None => true
  end.

Definition square_measure d sq :=
  match d with
  | Up   | Right | UpRight  | UpLeft => 64 - (square_to_nat sq)
  | Down | Left  | DownLeft | DownRight => square_to_nat sq
  end.

#[program]
Fixpoint squares (sq: Square) (d: Direction) { measure (square_measure d sq) } :=
  match (move_to d sq) with
  | Some sq => SquareSet.add sq (squares sq d)
  | None => SquareSet.empty
  end.
Next Obligation.
  clear squares. destruct sq. destruct sq0. unfold square_measure.
  destruct d;
    destruct rank0; try discriminate; simpl in Heq_anonymous; try discriminate; inversion Heq_anonymous; subst;
    destruct file0; try discriminate; simpl in Heq_anonymous; inversion Heq_anonymous; try discriminate; simpl; try lia. 
Defined.

Definition until_hit (b: Board) (squares: list Square) (color: Color) :=
  fst (@fold_left (SquareSet.t * bool) Square
    (fun acc sq =>
       let (valid_squares, hit) := acc in
       if hit then
         acc
       else if has_ally b sq color then
         (valid_squares, true)
       else if has_enemy b sq color then
              (SquareSet.add sq valid_squares, true)
            else
              (SquareSet.add sq valid_squares, false)) squares (SquareSet.empty, false)).

Definition cross (b: Board) (from: Square) (color: Color) :=
  SquareSet.union
    (SquareSet.union
       (until_hit b      (SquareSet.elements (squares from Up))    color)
       (until_hit b (rev (SquareSet.elements (squares from Down))) color))
    (SquareSet.union      
       (until_hit b (rev (SquareSet.elements (squares from Left))) color)
       (until_hit b      (SquareSet.elements (squares from Right)) color)).

Definition diag (b: Board) (from: Square) (color: Color) :=
  SquareSet.union
    (SquareSet.union
       (until_hit b      (SquareSet.elements (squares from UpRight))    color)
       (until_hit b      (SquareSet.elements (squares from UpLeft))     color))
    (SquareSet.union
       (until_hit b (rev (SquareSet.elements (squares from DownRight))) color)
       (until_hit b (rev (SquareSet.elements (squares from DownLeft)))  color)).
 
Definition attacks (b: Board) (from: Square) : SquareSet.t :=
  let maybe_add := fun square_set o => match o with Some e => SquareSet.add e square_set | None => square_set end in
  match get_square b from with
  | Some {| piece := Pawn; color := color |} =>
      let (left_dir, right_dir) :=
        match color with
        | White => (UpLeft, UpRight)
        | Black => (DownLeft, DownRight)
        end in
      let left_attack := move_to left_dir from in
      let right_attack := move_to right_dir from in
      maybe_add (maybe_add SquareSet.empty right_attack) left_attack
  | Some {| piece := King; color := color |} =>
      let squares := [
          move_to Up from;
          move_to Down from;
          move_to Left from;
          move_to Right from;
          move_to UpLeft from;
          move_to UpRight from;
          move_to DownLeft from;
          move_to DownRight from
        ] in
      fold_left maybe_add squares SquareSet.empty
  | Some {| piece := Horse; color := color |} =>
      let squares :=
        [
            bind square_inc_rank (bind square_inc_file (square_inc_file from));
            bind square_dec_rank (bind square_inc_file (square_inc_file from));
            bind square_inc_rank (bind square_dec_file (square_dec_file from));
            bind square_dec_rank (bind square_dec_file (square_dec_file from));
            bind square_inc_file (bind square_inc_rank (square_inc_rank from));
            bind square_dec_file (bind square_inc_rank (square_inc_rank from));
            bind square_inc_file (bind square_dec_rank (square_dec_rank from));
            bind square_dec_file (bind square_dec_rank (square_dec_rank from))
          ] in
      fold_left maybe_add squares SquareSet.empty
  | Some {| piece := Rook; color:=color |} => cross b from color
  | Some {| piece := Bishop; color:= color |} => diag b from color
  | Some {| piece := Queen; color:= color |} => SquareSet.union (diag b from color) (cross b from color)
  | _ => SquareSet.empty
  end.

Definition IsAttacked (board: Board) (turn: Color) (sq: Square) :=
  exists attacker_sq, SquareSet.In sq (attacks board attacker_sq) /\ has_enemy board attacker_sq turn = true.

Definition is_attacked (board: Board) (turn: Color) (square: Square) :=
  SquareMapProp.exists_
    (fun sq piece => (SquareSet.mem square (attacks board sq)) && (color_equal piece.(color) (invert turn))) board.

Definition exists_king (board: Board) (turn: Color) := SquareMapProp.exists_ (fun sq p => is_king p.(piece) && color_equal turn p.(color)) board.

Definition get_king (board: Board) (turn: Color) :=
  option_map fst (OrdSquareMapProp.min_elt (SquareMapProp.filter (fun sq p => is_king p.(piece) && color_equal turn p.(color)) board)).

Definition is_in_check (board: Board) (turn: Color) :=
  match get_king board turn with
  | Some sq => is_attacked board turn sq
  | _ => false
  end.

Definition possible_moves (board: Board) (turn: Color) (from: Square) :=
  match get_square board from with
  | None => SquareSet.empty
  | Some {| piece:=piece; color := piece_color |} =>
      if negb (color_equal piece_color turn) then SquareSet.empty else
        match piece with
        | Pawn =>
            let forward := match turn with
                           | White => Up
                           | Black => Down
                           end in
            match move_to forward from with
            | Some forward_square =>
                let forward_movement :=
                  if square_empty board forward_square then
                    let (start_rank, jump_rank) := double_movement turn in
                    let goal := {| file:= from.(file); rank :=jump_rank; |} in
                    let double :=
                      if andb (rank_equal from.(rank) start_rank) (square_empty board goal) then
                        SquareSet.add goal SquareSet.empty
                      else
                        SquareSet.empty in
                    SquareSet.add forward_square double
                  else SquareSet.empty in
                let pawn_attacks := SquareSet.filter (fun sq => has_enemy board sq turn) (attacks board from) in
                SquareSet.union pawn_attacks forward_movement
            | None => SquareSet.empty
            end
        | _ =>
            let attack_squares := attacks board from in
            SquareSet.filter (fun sq => negb (has_ally board sq turn)) attack_squares
        end
  end.

Definition play_move piece from to board turn :=
  SquareMap.remove from (SquareMap.add to {| piece := piece; color:= turn|} board).


Definition is_valid_move piece from to board turn :=
  let new_board := play_move piece from to board turn in
  get_square board from = Some {| piece:=piece; color:=turn|} /\
    SquareSet.mem to (possible_moves board turn from) = true /\
    is_in_check new_board turn = false.

Definition valid_moves (board: Board) turn from piece :=
  SquareSet.filter
    (fun to =>
       let new_board := play_move piece from to board turn in
       negb (is_in_check new_board turn)) (possible_moves board turn from).


Definition for_all_pieces_in_board (board: Board) (f: Square -> ColoredPiece -> Prop) :=
  SquareMap.fold (fun key element acc => acc /\ (f key element)) board True.

Definition no_more_moves (board: Board) (turn: Color) :=
  for_all_pieces_in_board board
    (fun from colored_piece =>
       let (piece, color) := colored_piece in
       if color_equal color turn then
         valid_moves board turn from piece = SquareSet.empty
       else
         True).

Definition for_all_valid_moves_from (board: Board) (turn: Color)
  (f: Piece -> Square -> Square -> Prop) :=
  for_all_pieces_in_board board
    (fun from piece =>
       let (from_piece, from_color) := piece in
       if color_equal from_color turn then
         let valid_moves_from := valid_moves board turn from from_piece in
         SquareSet.fold (fun to acc => acc /\ f from_piece from to) valid_moves_from True
       else
         True).

Inductive Match : forall (turn: Color) (board: Board), Prop :=
| NoMoreMoves : forall turn board,
    no_more_moves board turn ->
    Match turn board
| Movement piece from to : forall turn board,
    is_valid_move piece from to board turn ->
    let new_board := play_move piece from to board turn in
    Match (invert turn) new_board.

Definition board_disjunct : forall (sq add_sq: Square) (colored_piece add_colored_piece: ColoredPiece) board,
    SquareMap.MapsTo sq colored_piece (SquareMap.add add_sq add_colored_piece board)
    -> (sq = add_sq /\ colored_piece = add_colored_piece) \/
        SquareMap.MapsTo sq colored_piece board.
Proof.
  intros.
  apply SquareMap.find_1 in H.
  rewrite SquareMapProp.F.add_o in H.
  destruct (SquareSet.MF.eq_dec add_sq sq) eqn: SqEqual.
  - left. inversion H. symmetry in H1. split. { symmetry. rewrite <- square_eq_refl. apply e. } { reflexivity. }
  - right. apply SquareMap.find_2 in H. apply H.
Defined.

Fixpoint Mate_in (n: nat) : forall (board: Board) (turn: Color), Prop := fun board turn =>
  match n with
  | 0 => no_more_moves board (invert turn) /\ is_in_check board (invert turn) = true
  | S pred => exists piece from to,
      is_valid_move piece from to board turn ->
      let their_turn := invert turn in
      let their_board := play_move piece from to board turn in
      for_all_valid_moves_from their_board their_turn (fun op_piece op_from op_to =>
        let our_board := play_move op_piece op_from op_to their_board their_turn in
        Mate_in pred our_board turn)
  end.

Ltac for_all_possible_squares P :=
  repeat match type of P with
    | (_ /\ _) \/ ?other =>
        destruct P as [[square_eq piece_eq] | P]; [ subst; simpl | try for_all_possible_squares other ]
    | SquareMap.MapsTo ?sq1 ?piece1 (SquareMap.add ?sq2 ?piece2 ?board) => apply board_disjunct in P
    | SquareMap.MapsTo _ _ (SquareMap.remove _ _) => apply SquareMap.remove_3 in P
    | SquareMap.MapsTo _ _ (SquareMap.empty _) => apply SquareMapProp.F.empty_mapsto_iff in P; destruct P
    | SquareMap.MapsTo _ _ (play_move _ _ _ _ _) => unfold play_move in P
    end.

Definition squareset_disjunct : forall (sq add_sq: Square) moves,
    SquareSet.In sq (SquareSet.add add_sq moves)
    -> (sq = add_sq) \/ SquareSet.In sq moves.
Proof.
  intros.
  destruct (square_equal sq add_sq) eqn: E. apply square_eq_refl in E.
  - left. apply E.
  - apply SquareSet.add_3 in H. right. apply H.
    intro. apply square_eq_refl in H0. symmetry in H0. rewrite <- square_eq_refl in H0. rewrite H0 in E. discriminate.
Defined.


Ltac for_each_possible_response P :=
  let rec loop_squareset := fun is_valid squares => 
    match type of squares with
      | SquareSet.In ?sq SquareSet.empty => apply SquareSetProp.FM.empty_iff in squares; contradiction squares
      | SquareSet.In ?sq (SquareSet.add ?add_sq _) =>
          apply squareset_disjunct in squares as [ eq | rest]; [
            subst; vm_compute in is_valid; try discriminate
          | loop_squareset is_valid rest ]
  end in
  let compat_bool := unfold SetoidList.compat_bool, Morphisms.Proper, Morphisms.respectful;
                     intros ?sq1 ?sq2 ?eq; apply square_eq_refl in eq; subst; reflexivity in
  match type of P with
  | SquareSet.In ?sq (valid_moves _ _ _ _) =>
      let is_valid := fresh "is_valid" in
      let is_possible_move := fresh "is_possible_move" in
      let is_attack := fresh "is_attack" in
      let no_ally := fresh "no_ally" in
      apply SquareSetProp.Dec.F.filter_iff in P as [ ?is_possible_move ?is_valid ]; [
          apply SquareSetProp.Dec.F.filter_iff in is_possible_move as [ ?is_attack ?no_ally] ; [
            unfold attacks in is_attack; simpl in is_attack;
            loop_squareset is_valid is_attack
          | compat_bool ]
        | compat_bool ]
  end.

Ltac for_each_valid_move :=
  repeat match goal with
    | [ |- True ] => auto
    | [ |- context [for_all_valid_moves_from ?f ?turn ?pred] ] =>
        unfold for_all_valid_moves_from, for_all_pieces_in_board
    | [ |- SquareMap.fold ?f ?board ?acc] =>
        apply SquareMapProp.fold_rec_nodep
    | [ |- forall k e a, SquareMap.MapsTo k e ?board -> a -> a /\ _] =>
        let square := fresh "square" in
        let color_piece := fresh "color_piece" in
        let square_in_board := fresh "square_in_board" in
        let acc_pred := fresh "acc_pred" in
        let acc := fresh "acc" in 
        intros square color_piece acc_pred square_in_board acc;
        split; [ apply acc | for_all_possible_squares square_in_board ]
    | [ |- forall to_sq a, SquareSet.In _ _ -> a -> a /\ _] =>
        let square := fresh "square" in
        let acc_pred := fresh "acc_pred" in
        let square_is_in_valid_moves := fresh "square_is_in_valid_moves" in
        let acc := fresh "acc" in 
        intros square acc_pred square_is_in_valid_moves acc;
        split; [ apply acc | for_each_possible_response square_is_in_valid_moves ]
    | [ |- SquareSet.fold _ _ _ ] =>
        apply SquareSetProp.fold_rec_nodep
    end.

Definition example_board :=
  SquareMap.add {| file:=F; rank:=R1|} {|piece:= King; color:= White|}
    (SquareMap.add {| file:=D; rank:=R2|} {|piece:= Queen; color:= Black |}
       (SquareMap.add {|file:=F; rank:=R3|} {| piece:=King; color := Black |} (SquareMap.empty ColoredPiece))).

Definition example_game :=
  Movement Queen {|file:= D; rank:=R2|} {| file := D; rank := R1|} Black example_board
    ltac:(unfold is_valid_move; split; split; reflexivity).

Theorem is_in_mate_in_1 : Mate_in 1 example_board Black.
Proof.
  unfold Mate_in.
  exists Queen, {| file:=D; rank:=R2;|}, {| file:=D; rank:=R1;|}.
  unfold example_board.
  intros.
  for_each_valid_move.
Defined.

Theorem is_in_mate_in_2 : Mate_in 2 example_board Black.
Proof.
  unfold Mate_in.
  exists King, {| file:=F; rank:=R3;|}, {| file:=G; rank:=R3;|}.
  unfold example_board.
  intros.
  for_each_valid_move.
  exists Queen, {| file := D; rank := R2 |}, {| file := D; rank := R1 |}.
  intros.
  for_each_valid_move. vm_compute in is_valid0.
Defined.
  
