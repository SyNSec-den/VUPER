Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Term.BoolList
  
  ASN1Parser.Array.ByteBuffer
  ASN1Parser.Formats.Comb.SeqProd
  ASN1Parser.Formats.Comb.HelperComb
  
  Coq.Logic.FunctionalExtensionality.

(* Here eqb means that the two are the same, 
   such that the default is used here. 

   We will see how pycrate deal with default.
   Remove the value if they are equal 

   We shall add the prop that X shall satisfy 
   to the seq_elm (sequence element). 

   We must make sure that the default value 
   satisfy the condictions. Otherwise it does
   not make sense. 
 *)
Inductive seq_elem :=
| Nor (A : Set) : (A -> Prop) -> seq_elem
| Opt (A : Set) : (A -> Prop) -> seq_elem
| Dft (A : Set) (P : A -> Prop)  (default : A)
      (pf_dft : P default)
      (eqb_dec : forall a b : A, {a = b} + {a <> b}) : seq_elem. 

(* Slight problem here, that the default  *)

Definition n_list (f : seq_elem -> Set) (tl : list seq_elem)
  := List.map f tl. 


Definition seq_elem_to_type (X : seq_elem) : Set :=
  match X with
  | Nor A _ => A
  | Opt A _ => option A
  | Dft A _ _ _ _ => A
  end. 

Definition seq_set_list (l : list seq_elem) :=
  List.map seq_elem_to_type l.

Definition seq_type (l : list seq_elem) : Set :=
  list_to_prod_set l seq_elem_to_type (Nor unit (fun _ => True)).

(* Here, there might be a pattern which I can utilize. *)

Definition seq_cond (l : list seq_elem) : (seq_type l) -> Prop.
  intro. induction l.
  - apply True.
  - destruct a; unfold seq_type in H; simpl in H.
    + apply (P (fst H) /\ IHl (snd H)).
    + apply (opt_cond P (fst H) /\ IHl (snd H)). 
    + apply (P (fst H) /\ IHl (snd H)). 
Defined.

(*Definition seq_format_prod (l : list seq_elem) : Type :=
  list_to_prod l seq_elem_to_format (Nor unit (fun _ => True)).  *)

(* test *)
Module test1.
  Import Lists.List.

  Lemma ten_ge_1 : 10 >= 1. Lia.lia. Qed.
  
  Definition l0 := (Nor nat (ge 10)) ::
                     (Opt nat (ge 10)) ::
                     (Nor bool (fun _ => True)) ::
                     (Dft nat (ge 10) 1 ten_ge_1  PeanoNat.Nat.eq_dec) ::
                     nil.

  Definition tp := Eval compute in  seq_type l0. 
 
End test1.
(* end test *)

(* 
     This type indicates what is in encoded 
     in the bit-vector that 
     Is it 1 or 0 or not encoded at all. 
     option, present => 1; not present => 0
     default, non-default => 1; default => 0
     tru => 1; fal => 0
 *)
Inductive opt_types : Set :=
| norm
| tru
| fal.

Definition bit_list_len (l : list seq_elem) : nat :=
  List.fold_right (fun (h : seq_elem) =>
                     match h with
                     | Opt _ _ => S
                     | Dft _ _ _ _ _ => S
                     | Nor _ _ => id
                     end)
    0 l. 

Definition bit_list_length (l : list opt_types) : nat :=
  List.fold_right (fun x =>
                     match x with
                     | norm => id 
                     | _ => S 
                     end)
    0 l.

(* The bit 1 shall indicate the presence of the 
   component, while 0 shall indicate the absence 
   of it. 

   Here the function 
 *)

Definition seq_type_to_bit_list
  (ls : list seq_elem) (x : seq_type ls) : list bool.
  induction ls.
  - apply nil.
  - destruct x.
    destruct a eqn:E.
    (* Case of Normal type *)
    + apply (IHls l).
    (* Case of Option type.
       If Some _ then 1
       Else None then 0
     *)
    + apply (cons (match s with
                   | Some _ => true
                   | None => false
                   end)
                  (IHls l)). 
    + simpl in s.
      (* Case of Default type.
         If s = default then 0
         Else s <> default then 1 
       *)
      apply (cons (match eqb_dec default s with
                   | left _ => false
                   | right _ => true
                   end) (IHls l)) .
  Defined.

Lemma seq_type_to_bit_list_len_correct
  (l : list seq_elem)
  (a : seq_type l)
  : length (seq_type_to_bit_list l a) = bit_list_len l.
Proof.
  induction l; simpl ; auto. 
  destruct a. destruct a0.
  - unfold id.  apply IHl.
  - simpl in s. destruct s eqn:Es;  simpl; f_equal; apply IHl.
  - destruct (eqb_dec default s) eqn:Eb; simpl; f_equal; apply IHl.
Qed.
  
(* test *)
Module test2.
  Definition bit_list1 := seq_type_to_bit_list test1.l0.
  Definition x1 : test1.tp  :=
    (1, (Some 1, (true, (1, tt)))). 

  Definition test_bit_list := Eval compute in bit_list1 x1.
  
End test2.

(* Instead of generating directly the format, it might 
     be better if we can generate the Serializer and Parser
     functions separately. 
 *)
Definition seq_elem_to_set (seqo : seq_elem) : Set :=
  match seqo with
  | Nor X _ => X
  | Opt X _ => X
  | Dft X _ _ _ _ => X
  end.

Definition seq_elem_to_cond (seqo : seq_elem) : seq_elem_to_set seqo -> Prop :=
  match seqo with
  | Nor X P => P
  | Opt X P => P
  | Dft X P _ _ _ => P
  end.

Definition seq_elem_to_serial (se : seq_elem) :=
  Serialize (seq_elem_to_set se) (seq_elem_to_cond se). 
(*  match X with
  | Nor A P => Serialize A P
  | Opt A P => Serialize A P
  | Dft A P _ _ _  => Serialize A P
  end. *)

Definition seq_elem_to_parse (se : seq_elem) :=
  Parse (seq_elem_to_set se) (seq_elem_to_cond se).
(*  match X with
  | Nor A P => Parse A P
  | Opt A P => Parse A P
  | Dft A P _ _ _  => Parse A P
  end. *)

Definition seq_elem_to_format (se : seq_elem) :=
  T_Format (seq_elem_to_set se) (seq_elem_to_cond se).

Definition seq_format_prod l := 
  list_to_prod l seq_elem_to_format (Nor unit (fun _ => True)).

Definition seq_serial_prod (l : list seq_elem) : Type :=
  list_to_prod l seq_elem_to_serial (Nor unit (fun _ => True)).

Definition seq_to_len_prod (l : list seq_elem) : Type :=
  list_to_prod l
    (fun z => seq_elem_to_set z -> option nat)
    (Nor unit (fun _ => True)).

(* we would define a function that would 
     serialize something. 
 *)
Require Import ASN1Parser.Formats.Term.Unit.

Definition seq_serialize_latter (l : list seq_elem)
  (ser : seq_serial_prod l)
  : Serialize (seq_type l) (seq_cond l). 
  induction l.
  - apply (put_unit). 
  - destruct a.
    + apply (append_serialize (fst ser) (IHl (snd ser)) ).
    + apply (append_serialize 
               (opt_serialize (fst ser))
               (IHl (snd ser))).
    + apply (append_serialize
               (dft_serialize (fst ser) eqb_dec default pf_dft)
               (IHl (snd ser))).
Defined.

(* Here we can use Lemma seq_type_to_bit_list_len_correct, 
     to show that some parts of the proof can be removed

 (fun z => seq_type_to_bit_list l z)
Serialize (seq_type l) (seq_cond l) :=
 *)


Definition seq_serialize (l : list seq_elem)
  (ser : seq_serial_prod l) : Serialize (seq_type l) (seq_cond l) :=
    prepend_serialize (seq_type_to_bit_list l)
      (bool_list_serialize (bit_list_len l))
      (seq_serialize_latter l ser).

(* END of serializing function *)

Definition seq_parse_prod (l : list seq_elem) : Type :=
  list_to_prod l seq_elem_to_parse (Nor unit (fun _ => True)).

Definition seq_parse_latter
  (l : list seq_elem) (par : seq_parse_prod l)
  (bl : list bool)  (pf_bl : length bl = bit_list_len l)
  : Parse (seq_type l) (seq_cond l).
  generalize dependent bl.
  induction l; intros.
  - apply read_unit.
  - unfold seq_type. 
    simpl. unfold seq_parse_prod in par. 
    (*destruct par. *)
    destruct a.
    + apply (append_parse (fst par) (IHl (snd par) bl pf_bl)).
    + (*simpl. simpl in pf_bl. *) destruct bl.
      * apply fail_parse. (* inversion pf_bl. I could simply define a false parser *)
      * apply (append_parse
                 (opt_parse (fst par) b)
                 (IHl (snd par) bl
                    (eq_add_S (length bl) (bit_list_len l) pf_bl))). 
    + (*simpl. simpl in pf_bl. *) destruct bl.
      * apply fail_parse.
      * apply (append_parse
                 (dft_parse (fst par) default pf_dft eqb_dec  b)
                 (IHl (snd par) bl
                    (eq_add_S (length bl) (bit_list_len l) pf_bl))). 
Defined.

Definition seq_parse (l : list seq_elem) (par : seq_parse_prod l)
  :  Parse (seq_type l) (seq_cond l) := 
  bind_parse (bool_list_parse (bit_list_len l))
    (fun bl pf_bl _ =>
       (seq_parse_latter l par bl pf_bl)). 

(*
  If there is a correctness combinator, they should take the a product
  of correctness as the input.

  First, we need to give an outline of the proof. Before we actually do
  the proofs. 
 *)

(* Now we try to calculate the length of a seq_parse *)
Definition seq_to_len_latter (l : list seq_elem) (tl : seq_to_len_prod l)
  (c : seq_type l) : option nat.
  induction l.
  - apply (Some 0).
  - destruct a.
    + apply (add_opt ((fst tl) (fst c)) (IHl (snd tl) (snd c))).
    + destruct c.
      apply (add_opt (match s with
                      | Some a => (fst tl) a
                      | None => Some 0
                      end) (IHl (snd tl) l0)).
    + destruct c.
      apply (add_opt (match (eqb_dec default s) with
                      | left _ => Some 0
                      | right _ => (fst tl) s
                      end) (IHl (snd tl) l0)). 
Defined.
    
Definition seq_to_len (l : list seq_elem) (tl : seq_to_len_prod l)
  (c : seq_type l) : option nat :=
  add_opt (Some (bit_list_len l)) (seq_to_len_latter l tl c).

