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


Theorem king_cant_move_into_attack : forall board turn (from to : Square),
    get_square board from = Some {| piece:=King; color:= turn |} ->
    SquareSet.In to (valid_moves board turn from) ->
    is_attacked board turn to = false.
Proof.
  intros.
  unfold valid_moves in H0. simpl in H0. rewrite H in H0. rewrite color_eq_refl in H0. 
  destruct (is_in_check board turn); apply SquareSet.filter_2 in H0;
    try (apply andb_prop in H0; destruct H0; apply negb_true_iff in H0; apply H0);
    unfold compat_bool; unfold Proper; unfold "==>"; intros; rewrite square_eq_refl in H1; destruct H1; reflexivity.
Defined.

Check king_cant_move_into_attack.

Theorem get_king_correct : forall board turn square,
    get_king board turn = Some square ->
    get_square board square = Some {| piece := King; color := turn |}.
Proof.
  intros.
  unfold get_king in H. unfold get_square.
  destruct (OrdSquareMapProp.min_elt
              (moves.SquareMapProp.filter
                 (fun (_ : SquareMap.key) (p : ColoredPiece) =>
                    is_king (piece p) &&
                      color_equal turn (color p)) board)) eqn:E; try discriminate.
  destruct p. simpl in H. inversion H; subst; clear H.
  apply OrdSquareMapProp.min_elt_MapsTo in E.
  apply SquareMapProp.filter_iff in E.
  - destruct E. apply SquareMap.find_1 in H. destruct c.
    apply andb_prop in H0 as [King Color]. destruct piece; destruct color; destruct turn; try discriminate; apply H.
  - unfold Proper. intros sq1 sq2 G x y J. destruct J. reflexivity.
Defined.

Theorem needs_king_to_be_in_check : forall board turn,
    is_in_check board turn = true ->
    exists sq, get_square board sq = Some {| piece:=King; color:= turn |}.
Proof.
  intros. unfold is_in_check in H. destruct (get_king board turn) as [sq|] eqn:King; try discriminate.
  exists sq. apply get_king_correct in King. apply King.
Defined.

Theorem if_in_check_then_can_only_move_king : forall board turn from to,
    is_in_check board turn = true ->
    SquareSet.In to (valid_moves board turn from) ->
    get_square board from = Some {| piece:= King; color:= turn|}.
Proof.
  intros.
  unfold valid_moves in H0. rewrite H in H0. unfold is_in_check in H.
  destruct (get_king board turn) in H; try discriminate.
  destruct (get_square board from).
  - destruct c. destruct (color_equal color turn) eqn:C; destruct piece eqn:P; try (apply set_is_empty in H0; destruct H0). simpl in H0. destruct color; destruct turn; try discriminate; reflexivity.
  - apply set_is_empty in H0. destruct H0.
Qed.

Theorem is_attacked_correct : forall board turn sq,
    IsAttacked board turn sq <-> is_attacked board turn sq = true.
Proof.
  split; intros.
  - unfold IsAttacked in H. unfold is_attacked. destruct H as [attacker_sq [in_attacks has_enemy_in_sq]].
    unfold has_enemy in has_enemy_in_sq. unfold has_ally in has_enemy_in_sq.
    rewrite SquareMapProp.exists_iff.
    + destruct (get_square board attacker_sq) eqn:E; try discriminate.
      exists (attacker_sq, c). split.
      * simpl. unfold get_square in E. apply SquareMap.find_2 in E. apply E.
      * apply andb_true_intro. split.
        { simpl. apply SquareSet.mem_1 in in_attacks. apply in_attacks. }
        { destruct c. simpl. destruct color; destruct turn; try discriminate; apply has_enemy_in_sq. }
    + unfold Proper. intros sq1 sq2 G x y J. destruct J. apply square_eq_refl in G. destruct G. reflexivity.
  - unfold IsAttacked. unfold is_attacked in H. rewrite SquareMapProp.exists_iff in H. destruct H as [[attacker_sq c_piece] [Maps Eq]].
    exists attacker_sq. split; apply andb_prop in Eq as [Attacks ColorEq].
    + apply SquareSet.mem_2 in Attacks. apply Attacks.
    + unfold has_enemy. unfold has_ally. unfold get_square. apply SquareMap.find_1 in Maps. simpl in Maps. rewrite Maps.
      destruct c_piece as [piece color]. simpl in ColorEq. destruct color; destruct turn; try discriminate; apply ColorEq.
    + unfold Proper. intros sq1 sq2 G x y J. destruct J. apply square_eq_refl in G. destruct G. reflexivity.
Defined.

Theorem is_in_check_correct : forall board turn square,
    get_king board turn = Some square ->
    is_in_check board turn = true <-> is_attacked board turn square = true.
Proof.
  split; intros.
  - unfold is_in_check in H0. rewrite H in H0. apply H0.
  - unfold is_in_check. rewrite H. apply H0.
Defined.

