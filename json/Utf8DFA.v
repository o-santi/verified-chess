From Coq Require Import Strings.Byte.

Require Import Json.Parser.
Require Import Json.Utf8.

Local Notation "0" := false.
Local Notation "1" := true.

(* An implementation of the fast and efficient UTF8 decoding DFA *)
(* presented in the following post: *)
(* https://bjoern.hoehrmann.de/utf-8/decoder/dfa/ *)

Inductive parsing_state : Type :=
  Start
| State1
| State2
| State3
| State4
| State5
| State6
| State7
| State8
| Finish (c: codepoint).

Inductive range: Type :=
| Range_00_7F (bits: b7)
| Range_80_8F
| Range_C2_DF
| Range_E1_EC
| Range_EE_EF
| Range_ED_ED
| Range_F4_F4
| Range_F1_F3
| Range_A0_BF
| Range_C0_C1
| Range_90_9F
| Range_E0_E0
| Range_F0_F0.

Definition next (state: parsing_state) (byte_range: range) : option parsing_state :=
  match state with
  | Start => match byte_range with
            | Range_00_7F (b1, b2, b3, b4, b5, b6, b7) => Some (Finish (0, b4_zero, b4_zero, b4_zero, (0, b1, b2, b3), (b4, b5, b6, b7)))
            | _ => None
            end
  | _ => None
  end.
  
Definition byte_to_range (byte: byte) : option range. Admitted.

Definition utf8_state_machine_decode : @parser unicode_str byte unicode_decode_error.
