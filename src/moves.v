Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Init.Datatypes.
Require Import Program.
Require Import Lia.
Require Import board.
Require Import Coq.FSets.FMapFacts Coq.Structures.OrderedTypeEx.
Require Import Coq.Relations.Relation_Operators.

Module SquareMapProp := WProperties_fun S SquareMap.
Module OrdSquareMapProp := OrdProperties SquareMap.

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

Record GameState := {
    board : Board;
    player_turn: Color;
    moves: nat;
  }.

Definition IsAttacked (game_state: GameState) (sq: Square) :=
  exists attacker_sq, SquareSet.In sq (attacks game_state.(board) attacker_sq) /\ has_enemy (game_state.(board)) attacker_sq game_state.(player_turn) = true.

Definition is_attacked (board: Board) (turn: Color) (square: Square) :=
  SquareMapProp.exists_
    (fun sq piece => SquareSet.mem square (attacks board sq) && color_equal piece.(color) (invert turn)) board.

Definition exists_king (game_state: GameState) := SquareMapProp.exists_ (fun sq p => is_king p.(piece) && color_equal game_state.(player_turn) p.(color)) game_state.(board).

Definition get_king (board: Board) (turn: Color) :=
  option_map fst (OrdSquareMapProp.min_elt (SquareMapProp.filter (fun sq p => is_king p.(piece) && color_equal turn p.(color)) board)).

Definition is_in_check (board: Board) (turn: Color) :=
  match get_king board turn with
  | Some sq => is_attacked board turn sq
  | _ => false
  end.

Definition valid_moves (game_state: GameState) (from: Square) :=
  let b := game_state.(board) in
  let turn := game_state.(player_turn) in
  match get_square b from with
  | None => SquareSet.empty
  | Some {| piece:=piece; color := piece_color |} =>
      if negb (color_equal piece_color turn) then SquareSet.empty else
        match (is_in_check b turn, piece) with
        | (false, Pawn) =>
            let forward := match turn with
                           | White => Up
                           | Black => Down
                           end in
            match move_to forward from with
            | Some forward_square =>
                let forward_movement :=
                  if square_empty b forward_square then
                    let (start_rank, jump_rank) := double_movement turn in
                    let goal := {| file:= from.(file); rank :=jump_rank; |} in
                    let double :=
                      if andb (rank_equal from.(rank) start_rank) (square_empty b goal) then
                        SquareSet.add goal SquareSet.empty
                      else
                        SquareSet.empty in
                    SquareSet.add forward_square double
                  else SquareSet.empty in
                let pawn_attacks := SquareSet.filter (fun sq => has_enemy b sq turn) (attacks b from) in
                SquareSet.union pawn_attacks forward_movement
            | None => SquareSet.empty
            end
        | (_, King) =>
            let attack_squares := attacks b from in
            SquareSet.filter (fun sq => andb (negb (is_attacked b turn sq)) (negb (has_ally b sq turn))) attack_squares
        | (false, _) =>
            let attack_squares := attacks b from in
            SquareSet.filter (fun sq => negb (has_ally b sq turn)) attack_squares
        | (true, _) => SquareSet.empty
        end
  end.

Definition example_board :=
  SquareMap.add {| file:=D; rank:=R2|} {|piece:=Queen; color:=White|}
    (SquareMap.add {| file:=C; rank:=R3|} {|piece:=Rook; color:=Black |}
       (SquareMap.add {| file:=D; rank:=R4|} {| piece:=Horse; color:=Black|}
          (SquareMap.add {|file:=B; rank:=R2|} {| piece:=Pawn; color :=White |} (SquareMap.empty ColoredPiece)))).


Inductive game_step : GameState -> GameState -> Type :=
| Draw game_state :
  game_step game_state game_state
| Stalemate game_state :
  (forall square, (valid_moves game_state square) = SquareSet.empty) ->
  is_in_check game_state.(board) game_state.(player_turn) = false ->
  game_step game_state game_state
| Checkmate game_state :
  (forall square, (valid_moves game_state square) = SquareSet.empty) ->
  is_in_check game_state.(board) game_state.(player_turn) = true ->
  game_step game_state game_state
| Movement game_state p from to:
  let new_board := SquareMap.remove from (SquareMap.add to {| piece :=p; color:= game_state.(player_turn)|} game_state.(board)) in
  get_square game_state.(board) from = Some {| piece:=p; color:=game_state.(player_turn)|} ->
  SquareSet.In to (valid_moves game_state from) ->
  is_in_check new_board game_state.(player_turn) = false ->
  game_step game_state {|
              board := new_board;
              player_turn := invert game_state.(player_turn);
              moves := game_state.(moves) + 1
            |}.

Definition example_game :=
  let game_state :=
    {| board := example_board;
      moves := 0;
      player_turn := White
    |}
  in Movement game_state Queen {|file:= D; rank:=R2|} {| file := E; rank := R1|}
       ltac:(reflexivity) ltac:(apply SquareSet.mem_2; reflexivity) ltac:(reflexivity).

Compute example_game.

Inductive ValidGame: GameState -> GameState -> Type :=
| game_end : forall (x : GameState),
    game_step x x -> ValidGame x x
| game_next : forall (x y z : GameState),
    game_step x y ->
    ValidGame y z ->
    ValidGame x z.




