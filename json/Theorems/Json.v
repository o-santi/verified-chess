Require Import parser.

From Coq Require Import Strings.String.
From Coq Require Import ZArith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.

(* Theorem parse_null_isomorphic : parse_null "null" = Ok((JNull, "")). *)
(*   reflexivity. *)
(* Qed. *)
(* Theorem parse_true_isomorphic : parse_true "true" = Ok((JTrue, "")). *)
(*   reflexivity. *)
(* Qed. *)
(* Theorem parse_false_isomorphic : parse_false "false" = Ok((JFalse, "")). *)
(*   reflexivity. *)
(* Qed. *)


(* Theorem parse_number_isomorphic :forall n, parse_number (serialize_json (JNumber n)) = Ok((JNumber n, "")). *)
(* Proof. *)
(*   intros. *)
(*   unfold parse_number, serialize_json. *)
(*   rewrite parser_map_correct. *)
(*   rewrite parse_nat_isomorphic. *)
(*   reflexivity. *)
(* Defined. *)

(* Theorem parse_correct_left (j: json) : parse_json (serialize_json j) = Ok((j, "")). *)
(* Proof. *)
(*   induction j; try auto. *)
(*   - unfold parse_json. unfold one_of. rewrite parse_number_isomorphic. reflexivity. *)
