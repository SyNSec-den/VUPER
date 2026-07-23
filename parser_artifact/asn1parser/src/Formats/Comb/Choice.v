Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.Comb.HelperComb
  ASN1Parser.Formats.Comb.SeqProd
  ASN1Parser.Array.ByteBuffer.

Require Import ASN1Parser.Formats.Term.NonNeg. 

 
(* Previously we used the dependent type of sum types to 
   indicate the type of Choice. 
   
   We will use a new notation this time. We could use the 
   notation of Fin.t or nat. Use this as the keys of Choice. 

   However, it might still be dependent types. 
 *)


(* Here, the question is whether we will consider extension.
   I suppose we ignore extension here for now. 

   Another problem is l is a list of Set. So we have to have 
   Set for terminal types. 
 *)

(* Here another thing that is missing is the interface of 
   a string to indicate the selection instead of n. We note 
   that such interface exists in enum, choice, and sequence. 

   The idea is to have a extensible mapping between the two. 

   The reason why we do not use Fin.t is that there are 
   extensions which would break Fin.t.
 *)
Definition empty_typ :=  {{Empty_set | fun _ : _ => True}}.

Definition nat_serial (n : nat)
  (pf1 : to_bit_sz n <= INT_MAX_LEN)
  := T_Serial _ _ (nat_format n pf1).

Definition nat_parse (n : nat) 
  (pf1 : to_bit_sz n <= INT_MAX_LEN)
  := T_Parse _ _ (nat_format n pf1).

Definition get_nth_typ (l : list typ) (n : nat) : typ :=
  (List.nth n l empty_typ).

(* This is probably not final, becasue we need to add extensions.
   But, we can put the idea of having a tag (n : nat) and a val
   of type (get_nth_type l n).

   Here, it is a sigT type
 *)
Definition choice (l : list typ) :=
  {n : nat & typ_set (get_nth_typ l n)}.

Definition choice_cond (l : list typ) : choice l -> Prop := 
  fun c =>
    let n := projT1 c in
    typ_cond (get_nth_typ l n) (projT2 c).

Definition get_nth_serial (l : list typ) :=
  get_nth_prod l (fun t => Serialize (typ_set t) (typ_cond t)) empty_typ.

Definition get_nth_parse (l : list typ) :=
  get_nth_prod l (fun t => Parse (typ_set t) (typ_cond t)) empty_typ.

Definition get_nth_to_len (l : list typ) :=
  get_nth_prod l (fun t => (typ_set t) -> option nat) empty_typ.

(* First part is encoding. The encoding of the latter part *)
(* Without Extensions
   It is better if we can say n < length l?
   But it is kind of unnecessary because we only use
   it after encode_nat which already entails that n < length l.

   Still need to conside the corner case where l is empty. 

   Here c means choice
 *)

Definition get_format_prodc (l : list typ) :=
  list_to_prod l (fun t => T_Format (typ_set t) (typ_cond t)) empty_typ. 

Definition get_serial_prodc (l : list typ) :=
  list_to_prod l (fun t => Serialize (typ_set t) (typ_cond t)) empty_typ.

Definition get_parse_prodc (l : list typ) :=
  list_to_prod l (fun t => Parse (typ_set t) (typ_cond t)) empty_typ.

Definition get_to_len_prodc (l : list typ) :=
  list_to_prod l (fun t => (typ_set t) -> option nat) empty_typ.


Definition choice_0_serial (l : list typ) (ser : get_serial_prodc l)
                    (n : nat)
  : Serialize (typ_set (get_nth_typ l n))
      (typ_cond (get_nth_typ l n) ) := 
  get_nth_serial l ser n. 

(* Then we combine it with the tag.
   
   It is very similar to sigma, but slightly different,
   basically, it is the sigma combinator. We can abstract is
 *)
(*Definition sigT_serialize {A : Set} {T : A -> Set}
  (PA : A -> Prop)
  (P : sigT T -> Prop)
  (encA : Serialize A P)
  (encT : forall a, Serialize (T a) ())
  : Serialize (sigT T) P := 
  
 *)

Definition length_cond (l : list typ) := 
  to_bit_sz (length2 l - 1) <= INT_MAX_LEN.

(* This serialize is only for choice with two or more item.
   Because for choice with only one item, we do not encode
   the tag, since there is no need to it.

 (l_ge_2 : 2 <= length l)
 *)
Definition choice_serial (l : list typ)
  (pf1 : length_cond l)
  (ser : get_serial_prodc l)
  : Serialize (choice l) (choice_cond l) :=
  fun bf pos c =>
    match ((nat_serial (length2 l - 1) pf1) bf pos (projT1 c)) with
    | Some (bf', pos', _) =>
        (choice_0_serial l ser (projT1 c) bf' pos' (projT2 c))
    | None => None
    end.

Definition choice_parse (l : list typ)
  (pf1 : length_cond l)
  (par : get_parse_prodc l)
  : Parse (choice l) (choice_cond l) :=
  bind_parse (nat_parse (length2 l - 1) pf1)
    (fun n _ _ =>
       bind_parse (get_nth_parse l par n)
         (fun v pf_v flg =>
            return_parse
              (exist _
                 (existT
                    (fun n0 => typ_set (get_nth_typ l n0)) n v) pf_v)
              flg)).

Definition choice_to_len (l : list typ)
  (tl : get_to_len_prodc l)
  (c : choice l)
 : option nat :=
  match c with
  | existT _ n a =>
      if (Nat.leb n (length2 l)) then
        (* First consider the length of choice, which is
           to_bit_sz (length2 l - 1). Then is the length of
           the encoding. 
         *)
        add_opt (Some (to_bit_sz (length2 l - 1)))
          (get_nth_prod l _ empty_typ tl n a)
      else
        (* if n too big, there is no encoding *)
        None
  end.

  
                         
