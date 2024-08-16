Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Init.Datatypes.
Require Import board.
Require Import moves.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.FSets.FMapFacts Coq.Structures.OrderedTypeEx.

Module SquareSetProp := WFacts_fun S SquareMap.
Module SquareMapProp := WProperties_fun S SquareMap.
Module SquareMapPropF := SquareMapProp.F.

Theorem set_is_empty : forall x, ~ SquareSet.In x SquareSet.empty.
Proof.
  intros x H.
  apply SquareSet.mem_1 in H. unfold SquareSet.mem in H. unfold SquareSet.MSet.mem in H. simpl in H. discriminate H.
Qed.

Theorem either_equal_or_in_set : forall x y s,
    SquareSet.In x (SquareSet.add y s) ->
    x = y \/ SquareSet.In x s.                                      
Proof.
  intros. destruct (square_equal x y) eqn:E.
  - left. apply square_eq_refl in E. apply E.
  - right. apply (@SquareSet.add_3 s y x).
    + intro contra. rewrite square_eq_refl in contra. rewrite contra in E. destruct x; destruct file; destruct rank; discriminate E.
    + apply H.
Defined.

Theorem in_one_element_set_means_equal : forall x y, SquareSet.In x (SquareSet.add y SquareSet.empty) -> x = y.
Proof.
  intros. apply either_equal_or_in_set in H. destruct H.
  - apply H.
  - apply set_is_empty in H. destruct H.
Defined.


Theorem king_cant_move_into_attack : forall game_state (from to : Square),
    get_square game_state.(board) from = Some {| piece:=King; color:= game_state.(player_turn) |} ->
    SquareSet.In to (valid_moves game_state from) ->
    is_attacked (game_state.(board)) to (game_state.(player_turn)) = false.
Proof.
  intros.
  unfold valid_moves in H0. simpl in H0. rewrite H in H0. rewrite color_eq_refl in H0. 
  destruct (is_in_check game_state); apply SquareSet.filter_2 in H0;
    try (apply andb_prop in H0; destruct H0; apply negb_true_iff in H0; apply H0);
    unfold compat_bool; unfold Proper; unfold "==>"; intros; rewrite square_eq_refl in H1; destruct H1; reflexivity.
Qed.

Theorem get_king_correct : forall board turn square,
    get_king board turn = Some square ->
    get_square board square = Some {| piece := King; color := turn |}.
Proof.
  intros.
  unfold get_king in H. unfold get_square. 
  destruct (OrdSquareMapProp.min_elt
              (moves.SquareMapProp.filter
                 (fun (_ : SquareMap.key) (p : ColoredPiece) =>
                    is_king (piece p) && color_equal turn (color p)) board)) eqn:E; try discriminate.
  destruct p. simpl in H. inversion H; subst; clear H.
  apply OrdSquareMapProp.min_elt_MapsTo in E.
  apply SquareMapProp.filter_iff in E.
  - destruct E. apply SquareMap.find_1 in H. destruct c.
    apply andb_prop in H0 as [King Color]. destruct piece; destruct color; destruct turn; try discriminate; apply H.
  - unfold Proper. intros sq1 sq2 G x y J. destruct J. reflexivity.
Defined.


Theorem needs_king_to_be_in_check : forall game_state,
    is_in_check game_state = true ->
    exists sq, get_square game_state.(board) sq = Some {| piece:=King; color:= game_state.(player_turn) |}.
Proof.
  intros. unfold is_in_check in H. destruct (get_king (board game_state) (player_turn game_state)) as [sq|] eqn:King; try discriminate.
  exists sq. apply get_king_correct in King. apply King.
Defined.

Theorem if_in_check_then_can_only_move_king : forall game_state from to,
    is_in_check game_state = true ->
    SquareSet.In to (valid_moves game_state from) ->
    get_square game_state.(board) from = Some {| piece:= King; color:= game_state.(player_turn)|}.
Proof.
  intros.
  unfold valid_moves in H0. rewrite H in H0. unfold is_in_check in H.
  destruct (get_king (board game_state) (player_turn game_state)) in H; try discriminate.
  destruct (get_square (board game_state) from).
  - destruct c. destruct (color_equal color (player_turn game_state)) eqn:C; destruct piece eqn:P; try (apply set_is_empty in H0; destruct H0). simpl in H0. destruct color; destruct (player_turn game_state); try discriminate; reflexivity.
  - apply set_is_empty in H0. destruct H0.
Qed.

