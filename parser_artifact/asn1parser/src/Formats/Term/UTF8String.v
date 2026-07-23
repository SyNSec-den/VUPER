Require Import 
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Comb.SeqOf
  ASN1Parser.Formats.Term.NonNeg.

Require Import
  Coq.Strings.String
  Coq.Strings.Ascii.

(* This is a function that will judge if a string is 
   a valid utf8 string or not

U+0000…U+007F   →  0xxxxxxx
U+0080…U+07FF   →  110xxxxx 10xxxxxx
U+0800…U+FFFF   →  1110xxxx 10xxxxxx 10xxxxxx
U+10000…U+10FFFF → 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx

In the mean time, we want this process to be quick, thus
matching the bit pattern might be better
aka
(to_nat x) 
 *)

Eval compute in String ("a"%char) (String ("b"%char) EmptyString).

(* This is a function that will compare the prefix of 
   a byte. 
 *)
Definition match_prefix (n : nat)

Inductive valid_utf8 : string -> Prop :=
| empty : valid_utf8 EmptyString
| singleChar (a : ascii) (s2 : string)
  : valid_utf8 s2 -> valid_utf8 (String a s2)
| twoChar (a b : ascii) (s2 : string)
  : valid_utf8 s2 -> valid_utf8 (String a (String b s2))
| threeChar  (a b c : ascii) (s2 : string)
  : valid_utf8 s2 -> valid_utf8 (String a (String b (String c s2)))
| fourChar  (a b c d : ascii) (s2 : string)
  : valid_utf8 s2 -> valid_utf8 (String a (String b (String c (String d s2))))
.
  

Definition utf8_constraint (s : string) : bool :=
  

