Require Import
          BinInt
          ASN1Parser.Array.ByteBuffer
          ASN1Parser.Array.BitRep.

From Coq Require Extraction.

Require Export ExtrOcamlChar.
Require Export ExtrOcamlNatInt.
Require Export ExtrOcamlZInt.
Require Export ExtrOcamlNativeString.
(*Extraction Implicit byte_get [n].
Extraction Implicit byte_set [n].
 *)

Extract Inductive ByteBuffer => "BigArrayExtr.byte_buf"
                                  ["{ buf_len = buf_len; buffer = buffer}"].

Extract Inlined Constant buf_len => "BigArrayExtr.buf_len".
Extract Inlined Constant buffer => "BigArrayExtr.buffer".

Extract Inlined Constant byte_make => "BigArrayExtr.make".
Extract Inlined Constant byte_get => "BigArrayExtr.get".
Extract Inlined Constant byte_set => "BigArrayExtr.set".

(* Some byte or int related notations needs to be directly translated *) 
Extract Inlined Constant Byte.to_nat => "Char.code".
Extract Inlined Constant Byte.of_nat => "BigArrayExtr.byte_of_nat".

(* About int shift *)
Extract Inlined Constant Nat.mul  => "( * )".
Extract Inlined Constant Nat.shiftr => "Int.shift_right".
Extract Inlined Constant Nat.shiftl => "Int.shift_left".
Extract Inlined Constant Nat.div => "(/)".
Extract Inlined Constant Nat.modulo => "(mod)".
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.add => "(+)".
Extract Inlined Constant Nat.sub => "(-)".
Extract Inlined Constant Nat.land => "Int.logand".
Extract Inlined Constant Nat.lor => "Int.logor".
Extract Inlined Constant PeanoNat.Nat.lxor => "Int.logxor".
Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Nat.log2 => "BigArrayExtr.log2".
Extract Inlined Constant PeanoNat.Nat.ones => "BigArrayExtr.nat_ones".

Extract Inlined Constant Z.to_nat => "BigArrayExtr.int_id".
Extract Inlined Constant Z.of_nat => "BigArrayExtr.int_id".
Extract Inlined Constant Z.eq_dec => "(=)".

Extract Inlined Constant String.length => "String.length".
Extract Inlined Constant Ascii.nat_of_ascii => "Char.code".
Extract Inlined Constant Ascii.ascii_of_nat => "Char.chr".

(* Here, for utf8 string, we define our own function for 
   it
 *)
Require Import ExtrOCaml.ExtractHelper.
Extract Inlined Constant check_utf8_string_dec => "String.is_valid_utf_8".

(* The dec operations shall be extracted.
   How many else of Compare_dec we used?
 *)
Opaque Compare_dec.le_dec.

(* The following section is for printing debug info *)

Definition print_nat (n : nat) := tt .
Definition print_bool (b : bool) := tt.

Definition debug_print_opt (A : Type) (print_A : A -> unit) (c : option A)  : unit
  := match c with
     | Some a => print_A a
     | None => tt
     end.

(* 
Definition debug_print_byte := debug_print_opt (fun b => print_int (Byte.to_nat b)).
Definition debug_print_nat  := debug_print_opt print_int.
*)

Extract Inlined Constant print_bool => "DebugPrint.print_bool".
Extract Inlined Constant print_nat => "DebugPrint.print_nat".

Extract Inlined Constant debug_print_opt => "DebugPrint.print_opt".

Set Extraction KeepSingleton.
