From Coq Require Import Strings.Byte.

Require Import Json.Parser.
Require Import Json.Utf8.

Local Notation "0" := false.
Local Notation "1" := true.
Definition zero_codep : codepoint := (0, b4_zero, b4_zero, b4_zero, b4_zero, b4_zero).


(* An implementation of the fast and efficient UTF8 decoding DFA *)
(* presented in the following post: *)
(* https://bjoern.hoehrmann.de/utf-8/decoder/dfa/ *)

Inductive range :=
  Range_00_7F (*  0 *)
| Range_80_8F (*  1 *)
| Range_90_9F (*  9 *)
| Range_A0_BF (*  7 *)
| Range_C0_C1 (*  8 *)
| Range_C2_DF (*  2 *)
| Byte_E0     (* 10 *)
| Range_E1_EC (*  3 *)
| Byte_ED     (*  4 *)
| Range_EE_EF (*  3 *)
| Byte_F0     (* 11 *)
| Range_F1_F3 (*  6 *)
| Byte_F4     (*  5 *)
| Range_F5_FF (*  8 *)
.

Inductive parsing_state :=
  Initial (* State0 *)
| State2
| State3
| State4
| State5
| State6
| State7
| State8.

Inductive parsing_result :=
  Finished (codep: codepoint)
| More (state: parsing_state) (acc: codepoint).

Definition byte_range (b: byte) : range :=
  match b with
    x00 | x01 | x02 | x03 | x04 | x05 | x06 | x07 | x08 | x09 | x0a | x0b | x0c | x0d | x0e | x0f
  | x10 | x11 | x12 | x13 | x14 | x15 | x16 | x17 | x18 | x19 | x1a | x1b | x1c | x1d | x1e | x1f
  | x20 | x21 | x22 | x23 | x24 | x25 | x26 | x27 | x28 | x29 | x2a | x2b | x2c | x2d | x2e | x2f
  | x30 | x31 | x32 | x33 | x34 | x35 | x36 | x37 | x38 | x39 | x3a | x3b | x3c | x3d | x3e | x3f
  | x40 | x41 | x42 | x43 | x44 | x45 | x46 | x47 | x48 | x49 | x4a | x4b | x4c | x4d | x4e | x4f
  | x50 | x51 | x52 | x53 | x54 | x55 | x56 | x57 | x58 | x59 | x5a | x5b | x5c | x5d | x5e | x5f
  | x60 | x61 | x62 | x63 | x64 | x65 | x66 | x67 | x68 | x69 | x6a | x6b | x6c | x6d | x6e | x6f
  | x70 | x71 | x72 | x73 | x74 | x75 | x76 | x77 | x78 | x79 | x7a | x7b | x7c | x7d | x7e | x7f => Range_00_7F
  | x80 | x81 | x82 | x83 | x84 | x85 | x86 | x87 | x88 | x89 | x8a | x8b | x8c | x8d | x8e | x8f => Range_80_8F
  | x90 | x91 | x92 | x93 | x94 | x95 | x96 | x97 | x98 | x99 | x9a | x9b | x9c | x9d | x9e | x9f => Range_90_9F
  | xa0 | xa1 | xa2 | xa3 | xa4 | xa5 | xa6 | xa7 | xa8 | xa9 | xaa | xab | xac | xad | xae | xaf
  | xb0 | xb1 | xb2 | xb3 | xb4 | xb5 | xb6 | xb7 | xb8 | xb9 | xba | xbb | xbc | xbd | xbe | xbf => Range_A0_BF
  | xc0 | xc1 => Range_C0_C1
  | xc2 | xc3 | xc4 | xc5 | xc6 | xc7 | xc8 | xc9 | xca | xcb | xcc | xcd | xce | xcf
  | xd0 | xd1 | xd2 | xd3 | xd4 | xd5 | xd6 | xd7 | xd8 | xd9 | xda | xdb | xdc | xdd | xde | xdf => Range_C2_DF
  | xe0 => Byte_E0
  | xe1 | xe2 | xe3 | xe4 | xe5 | xe6 | xe7 | xe8 | xe9 | xea | xeb | xec => Range_E1_EC
  | xed => Byte_ED
  | xee | xef => Range_EE_EF
  | xf0 => Byte_F0
  | xf1 | xf2 | xf3 => Range_F1_F3
  | xf4 => Byte_F4
  | xf5 | xf6 | xf7 | xf8 | xf9 | xfa | xfb | xfc | xfd | xfe | xff => Range_F5_FF
  end.


Definition push_bottom_bits (carry: codepoint) (b: byte) : @result codepoint unicode_decode_error :=
  let '(_, _, (_, b1, b2, b3), (b4, b5, b6, b7), (b8, b9, b10, b11), (b12, b13, b14, b15)) := carry in
  let '(b21, (b20, (b19, (b18, (b17, (b16, (h1, h2))))))) := Byte.to_bits b in
  match (h1, h2) with
    (0, 1) => Ok (b1, (b2, b3, b4, b5), (b6, b7, b8, b9), (b10, b11, b12, b13), (b14, b15, b16, b17), (b18, b19, b20, b21))
  | _ => Err (InvalidContinuationHeader (Some b))
  end.

Definition extract_bits (b: byte) : @result codepoint unicode_decode_error :=
  let '(b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) := Byte.to_bits b in
  match byte_range b with
  | Range_00_7F => Ok (0, b4_zero, b4_zero, b4_zero, (0, b7, b6, b5), (b4, b3, b2, b1))
  | Range_C2_DF => Ok(0, b4_zero, b4_zero, b4_zero, (0, 0, 0, b5), (b4, b3, b2, b1))
  | Range_E1_EC | Range_EE_EF | Byte_E0 | Byte_ED  => Ok (0, b4_zero, b4_zero, b4_zero, b4_zero, (b4, b3, b2, b1))
  | Range_F1_F3 | Byte_F4 | Byte_F0 => Ok (0, b4_zero, b4_zero, b4_zero, b4_zero, (0, b3, b2, b1))
  | _ => Err (InvalidStartHeader (Some b))
  end.


Definition next_state (state: parsing_state) (carry: codepoint) (b: byte) : @result parsing_result unicode_decode_error :=
  let byte_kind: range := byte_range b in
  let* code: codepoint :=
    match state with
    | Initial => extract_bits b
    | _other => push_bottom_bits carry b
    end in
  match (state, byte_kind) with
  | (Initial, Range_00_7F)
  | (State2,  Range_A0_BF)
  | (State2,  Range_90_9F)
  | (State2,  Range_80_8F) => Ok (Finished code)
  | (Initial, Byte_F4)     => Ok (More State8 code)
  | (Initial, Range_F1_F3) => Ok (More State7 code)
  | (Initial, Byte_F0)     => Ok (More State6 code)
  | (Initial, Byte_E0)     => Ok (More State4 code)
  | (Initial, Byte_ED)     => Ok (More State5 code)
  | (State8,  Range_80_8F)
  | (State7,  Range_80_8F)
  | (State7,  Range_90_9F)
  | (State7,  Range_A0_BF)
  | (Initial, Range_E1_EC)
  | (Initial, Range_EE_EF)
  | (State6,  Range_90_9F)
  | (State6,  Range_A0_BF) => Ok (More State3 code)
  | (Initial, Range_C2_DF)
  | (State4,  Range_A0_BF)
  | (State5,  Range_80_8F)
  | (State5,  Range_90_9F)
  | (State3,  Range_80_8F)
  | (State3,  Range_90_9F)
  | (State3,  Range_A0_BF) => Ok (More State2 code)
  | _ => Err (InvalidContinuationHeader (Some b))
  end.

Fixpoint utf8_dfa_decode_rec (bytes: list byte) (carry: codepoint) (state: parsing_state) (acc: list codepoint) : @result (unicode_str * (list byte)) unicode_decode_error :=
  match bytes with
  | nil => Ok (List.rev acc, nil)
  | cons b rest =>
      let* next := next_state state carry b in
      match next with
      | Finished codep => utf8_dfa_decode_rec rest zero_codep Initial (codep :: acc)
      | More state codep => utf8_dfa_decode_rec rest codep state acc
      end
  end.
    
Definition utf8_dfa_decode (bytes: list byte) : @result (unicode_str * (list byte)) unicode_decode_error :=
  utf8_dfa_decode_rec bytes zero_codep Initial nil.

From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
Compute (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [x41; xe2; x89; xa2; xce; x91; x2e])).

(* The character sequence U+0041 U+2262 U+0391 U+002E "A<NOT IDENTICAL *)
(* TO><ALPHA>." is encoded in UTF-8 as follows: *)

(*     --+--------+-----+-- *)
(*     41 E2 89 A2 CE 91 2E *)
(*     --+--------+-----+-- *)
Definition test1 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [x41; xe2; x89; xa2; xce; x91; x2e]))
  = Ok (["U+0041"%string; "U+2262"%string; "U+0391"%string; "U+002E"%string], []).
  reflexivity.
Qed.

(* The character sequence U+D55C U+AD6D U+C5B4 (Korean "hangugeo", *)
(* meaning "the Korean language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     ED 95 9C EA B5 AD EC 96 B4 *)
(*     --------+--------+-------- *)
Definition test2 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [xed; x95; x9c; xea; xb5; xad; xec; x96; xb4]))
  = Ok (["U+D55C"%string; "U+AD6D"%string; "U+C5B4"%string], []).
  reflexivity.
Qed.


(* The character sequence U+65E5 U+672C U+8A9E (Japanese "nihongo", *)
(* meaning "the Japanese language") is encoded in UTF-8 as follows: *)

(*     --------+--------+-------- *)
(*     E6 97 A5 E6 9C AC E8 AA 9E *)
(*     --------+--------+-------- *)
Definition test3 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [xe6; x97; xa5; xe6; x9c; xac; xe8; xaa; x9e]))
  = Ok (["U+65E5"%string; "U+672C"%string; "U+8A9E"%string], []).
  reflexivity.
Qed.

(* The character U+233B4 (a Chinese character meaning 'stump of tree'), *)
(* prepended with a UTF-8 BOM, is encoded in UTF-8 as follows: *)

(*     --------+----------- *)
(*     EF BB BF F0 A3 8E B4 *)
(*     --------+----------- *)

Definition test4 :
  (fmap (fun '(s, r) => (List.map show_codepoint s, r)) (utf8_dfa_decode [xef; xbb; xbf; xf0; xa3; x8e; xb4]))
  = Ok (["U+FEFF"%string; "U+0233B4"%string], []).
  reflexivity.
Qed.
