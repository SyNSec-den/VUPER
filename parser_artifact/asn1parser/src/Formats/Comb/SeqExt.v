Require Import
          ASN1Parser.Formats.Comb
          ASN1Parser.Formats.CombFormat
          ASN1Parser.Array.ByteBuffer.

Require Import
  ASN1Parser.Formats.Comb.SeqProd 
  ASN1Parser.Formats.Comb.Seq
  ASN1Parser.Formats.Term.Unit
  ASN1Parser.Formats.Term.Boolean
  ASN1Parser.Formats.Term.LengthDet
  ASN1Parser.Formats.Comb.HelperComb
  ASN1Parser.Formats.Comb.OpenType.

Definition ext_elem_to_type (t : typ) :=
  option (typ_set t).

Fixpoint list_to_prod_dft 
  {X : Type} (l : list X) (f : X -> Set) (default : Set) {struct l} : Set :=
  match l with
  | nil => default
  | (h :: t)%list => (f h * list_to_prod_dft t f default)%type
  end.

Definition seq_ext_type (ext : list typ) : Set :=
  list_to_prod_dft ext ext_elem_to_type unit.

Definition seq_ext_cond (ext : list typ) :
  seq_ext_type ext -> Prop.
  induction ext; intros. 
  - apply True.
  -  apply (opt_cond (typ_cond a) (fst H) /\ (IHext (snd H))).
Defined.

(* Now it is a lot harder to calculate the length, but 
     it is still possible. But it would complicate things
     a bit. So every serialize function would be accompanied
     by a get_len function which would take a element in that
     type and gives a length afterwards. 
     Here, decode is a lot more loose. 
*)
  

(* We actually want to change it a bit. We cannot unironically use

     We can see that 
     1. In ASN1c, they are grouped into a struct inside the 
        extension, which is no different than directly using a 
        struct representation-wise
     2. In Pycrate, 
 *)


(* Similar to Serialize, first we need to encode the number of extensions
     as well as the bit-map which indicates the existence of extensions. 

     Here, we first consider the latter part, which is the open-type of 
     each components
 *)

Definition prepend_serialize_opt {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (f : B -> option A)
  (serA : Serialize A Pa) 
  (serB : Serialize B Pb)
  : Serialize B Pb :=
  fun bf pos b =>
    match (f b) with
    | Some a => 
        match (serA bf pos a) with
        | Some (bf', pos', _ ) => serB bf' pos' b
        | None => None
        end
    | None => None
    end.

(* We will need to change this function. Because it is very hard to
   reason on TP. But we will have to be sure that this function is
   indeed the function.

   The thing is to_length_opt is not wrong. But we must Eval
   compute it first in Coq, before we plug it into the parsing
   procedure.

   So we will pass them into the function 
 *)

(*Eval compute in get_byte_num 1. *)

(* We can prove that the length of opt-type is always a 
     multiple of 8. 
 *)

(* Here, I must have that list of length function

   We also need to check if evey term is None, then we would
   simply output 
 *)
Require Import
  ASN1Parser.Formats.Term.Unit
  ASN1Parser.Formats.Term.BoolList.

Definition ext_serialize_latter (ext : list typ)
  (ser : get_serial_prod ext)
  (len_prod : get_to_len_prod ext) :
  Serialize (seq_ext_type ext) (seq_ext_cond ext).
  induction ext.
  - apply put_unit.
  - apply (append_serialize
             (opt_serialize (open_typ_serialize (fst ser) (fst len_prod)))
             (IHext (snd ser) (snd len_prod))). 
Defined.

(* If there is nothing, obviously it should be None *)
Definition check_all_none (ext : list typ) (s : seq_ext_type ext) : Prop.
  induction ext.
  - apply True.
  - destruct s.  destruct e.
    + apply False.
    + apply (IHext l).
Defined.

Definition check_all_none_bool (ext : list typ) (s : seq_ext_type ext) : bool.
  induction ext.
  - apply true.
  - destruct s.
    apply (match e with
           | Some _ => false
           | None => IHext l
           end). 
Defined.

Lemma check_all_none_helper1  (ext : list typ) (s : seq_ext_type ext) : check_all_none_bool ext s = true -> check_all_none ext s.
Proof.
  induction ext; intros; simpl; auto. 
  destruct s. destruct e eqn:E.
  - simpl in H.  inversion H.
  - apply IHext.  simpl in H.  auto.
Qed.

Lemma check_all_none_helper2  (ext : list typ) (s : seq_ext_type ext) : check_all_none_bool ext s = false ->  ~ check_all_none ext s.
Proof.
  induction ext; intros. 
  - simpl. simpl in H. inversion H.
  - destruct s, e; simpl in H; intro. auto. 
    simpl in H0.  apply IHext in H.  destruct (H H0). 
Qed.

Definition check_all_none_dec (ext : list typ)
  : dec_P (check_all_none ext).
  intro. 
  destruct (check_all_none_bool ext a) eqn:E.
  - apply left. apply check_all_none_helper1. apply E.
  - apply right. apply check_all_none_helper2. apply E. 
Defined.


Require Import List. 
Definition l1 := unit_typ :: unit_typ :: unit_typ :: unit_typ ::  nil.
(*Eval compute in (check_all_none_dec l1).   *)

(* END of test *)

Definition opt_bool {A : Type} (a : option A) : bool :=
  match a with
  | Some _ => true
  | None => false
  end.

Definition ext_to_bit_list (ext : list typ)
  (s : seq_ext_type ext) : list bool.
  induction ext.
  - apply nil.
  - apply (cons (opt_bool (fst s)) (IHext (snd s))).
Defined.

Lemma ext_to_bit_list_len : forall (ext : list typ)
                                   (s : (seq_ext_type ext)),
    length ext = length (ext_to_bit_list ext s).
  intros ext.
  induction ext; intros. 
  - simpl.  auto.
  - simpl.  f_equal.
    apply IHext.
Qed.

Definition ext_serialize (ext : list typ)
  (ser : get_serial_prod ext)
  (len_prod : get_to_len_prod ext)
  :=
  prepend_serialize (fun z => length2 ext)
    (small_enc)
    ((prepend_serialize (fun z => ext_to_bit_list ext z)
       (bool_list_serialize (length2 ext)))
       (ext_serialize_latter ext ser len_prod)).
  
(*  prepend_serialize (fun z => ext_to_bit_list ext z)
    (prepend_serialize (fun bl => length bl)
       (small_enc)
       (bool_list_serialize (length2 ext)))
    (ext_serialize_latter ext ser len_prod). *)

(* We need combine this with normal sequence serialize. 
     We could make an abstraction of the problem, that is 
 *)


Definition serialize_opt_tuple {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (serA : Serialize A Pa) (serB : Serialize B Pb)
  : Serialize (A * option B)   (fun z => Pa (fst z) /\
                                              (opt_cond Pb (snd z))) :=
  prepend_serialize   (fun z => opt_bool (snd z))
    (bool_enc)
    (append_serialize
       serA
       (opt_serialize serB)).
            

(* There are 3 cases, length bl < length ext,
       len bl = len ext, and len bl > len ext. 
       
       We should write a parser for each of the cases. 

       using Compare_dec.lt_eq_lt_dec
 *)

Definition to_parse_latter_eq (ext : list typ) (par : get_parse_prod ext)
  (bl : list bool) (len_eq : length bl = length2 ext)
  : Parse (seq_ext_type ext) (seq_ext_cond ext).
  generalize dependent bl.
  induction ext; intros. 
  - apply read_unit.
  - destruct bl.
    + apply fail_parse.
    (*unfold seq_ext_type, seq_ext_cond.  simpl. *)
    + eapply (append_parse
                (opt_parse (open_typ_parse (fst par)) b)
                (IHext (snd par) bl (eq_add_S (length bl)
                                       (length2 ext) len_eq))). 
Defined.

(* This is when there is nothing to parse, just simply return 
     None for every term.

   We don't even need to skip here

   Set to different version tho
 *)
Definition ext_all_none (ext : list typ) : seq_ext_type ext. 
  induction ext.
  - apply tt.
  - apply (None, IHext).
Defined.

Lemma ext_all_none_is_all_none (ext : list typ) : 
  check_all_none ext (ext_all_none ext).
Proof. induction ext; simpl; auto. Qed.

Lemma ext_all_none_pf (ext : list typ)  : (seq_ext_cond ext (ext_all_none ext)).
Proof. induction ext; simpl; auto. Qed.


Definition to_parse_none (ext' : list typ)
  : Parse (seq_ext_type ext') (seq_ext_cond ext') := 
  bind_parse read_unit
    (fun _ _ flg =>  
       (return_parse (exist _ (ext_all_none ext') (ext_all_none_pf ext')) DiffVer)). 


Definition to_parse_latter_le (ext : list typ) (par : get_parse_prod ext)
  (bl : list bool) (len_eq : length bl < length2 ext)
  : Parse (seq_ext_type ext) (seq_ext_cond ext).
  generalize dependent bl.
  induction ext; intros.
  - apply read_unit.
  - destruct bl.
    + (* When bl is actual 0, then, everything would be 
           set to None
       *)
      apply (to_parse_none (a :: ext)). 
    + (* When bl is not 0, continue *)
      eapply (append_parse (opt_parse (open_typ_parse (fst par)) b)
                (IHext (snd par) bl
                   (PeanoNat.lt_S_n
                      (length bl) (length2 ext) len_eq))). 
Defined.

(* It would skip n open types, but note that the 
   n open types might exist or not. So we have to 
   keep that bool list for now
 *)
Fixpoint to_parse_skip (n : nat) (bl : list bool) : Parse unit (fun _ => True) :=
  match n with
  | 0 => read_unit
  | S m =>
      match bl with
      | nil => fail_parse
      | h :: tbl =>
          if h then 
            bind_parse open_type_skip_parse (fun _ _ _ => to_parse_skip m tbl)
          else
            to_parse_skip m tbl
      end
  end.

Definition to_parse_latter_ge (ext : list typ) (par : get_parse_prod ext)
  (bl : list bool) (len_eq : length bl > length2 ext)
  : Parse (seq_ext_type ext) (seq_ext_cond  ext) :=
  let n := length2 ext in
  let l0 := List.firstn n bl in
  bind_parse 
    (to_parse_latter_eq ext par l0
       (List.firstn_length_le bl
         (PeanoNat.Nat.lt_le_incl n (length bl) len_eq) ))
    (fun e pf_e _  =>
       bind_parse (to_parse_skip (length bl - n) (skipn n bl))
         (fun _ _ _ =>
            return_parse (exist _ e pf_e) DiffVer)
    ).
(* We first read the whole thing, by cut of bl at length ext.
      Then we apply open_type_skip to skip throught the back
 *)

Inductive three_split (P1 P2 P3 : Prop) :=
| left3 (pf : P1)
| middle3 (pf : P2)
| right3 (pf : P3).

(* Here, the problem is lt_le_eq_dec used lt_eq_lt_dec in the first place *)
Definition lt_le_eq_dec (n m : nat) (pf_n_le_m : n <= m) :
  {n < m} + {n = m} := 
  match (Compare_dec.le_lt_dec m n) with
  | left pf_m_le_n => right (PeanoNat.Nat.le_antisymm n m pf_n_le_m pf_m_le_n)
  | right pf_n_lt_m => left pf_n_lt_m
  end.

Definition lt_eq_lt_dec_new (n m : nat)
  : three_split (n < m) (n = m) (m < n) :=
  match (Compare_dec.le_lt_dec n m) with
  | left pf_n_le_m =>
      match (lt_le_eq_dec n m pf_n_le_m) with
      | left pf_n_lt_m => left3 _ _ _ pf_n_lt_m
      | right pf_n_eq_m => middle3 _ _ _ pf_n_eq_m
      end
  | right pf_m_lt_n =>
      right3 _ _ _ pf_m_lt_n     
  end.

Definition ext_parse (ext : list typ) (par : get_parse_prod ext)
  : Parse (seq_ext_type ext) (seq_ext_cond ext) :=
  bind_parse small_dec
    (* It would read that there are n extensions *)
    (fun n _ _ =>
       bind_parse (bool_list_parse n)
         (fun bl _  _ =>
            (match ( lt_eq_lt_dec_new (length bl) (length2 ext)) with
             | left3 _ _ _  pf1 => to_parse_latter_le ext par bl pf1
             | middle3 _ _ _ pf2 => to_parse_latter_eq ext par bl pf2
             | right3 _ _ _ pf3 => to_parse_latter_ge ext par bl pf3
             end)
         )
    ).

Definition seq_ext_to_len_latter (ext : list typ)
  (tl : get_to_len_prod ext) (s : seq_ext_type ext) : option nat.
  induction ext.
  - apply (Some 0).
  - destruct s, tl.
    apply (add_opt (match e with
                    | Some t => open_type_to_len o t
                    | None => Some 0
                    end) (IHext l0 l)).
Defined.

(* First, a len-enc  *)
Definition seq_ext_to_len (ext : list typ)
  (tl : get_to_len_prod ext) (s : seq_ext_type ext) : option nat :=
  let len_e := length2 ext in 
  add_opt (T_to_len _ _ normally_small_len_det_format len_e)
    (add_opt (Some len_e)
       (seq_ext_to_len_latter ext tl s)). 

(* Need to change this.
   The extension should not be put in a tuple. Instead, if all
   the fields are absent in B, then B should not be encoded.

   Problem is extension groups. If all fields are absent in extension
   group, should it be encoded?
 *)

Definition parse_opt_tuple {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (parA : Parse A Pa) (parB : Parse B Pb)
  : Parse (A * option B)   (fun z => Pa (fst z) /\
                                          (opt_cond Pb (snd z))) :=
  bind_parse (T_Parse _ _ bool_format)
    (fun b _ _ =>
       append_parse parA (opt_parse parB b)).


(* We need to consider the special case for ExtensionAdditionGroup,
   this is when all the fields are OPTIONAL. Then, we would have
   it not-encoded if all optional fields are empty. The problem is
   during decoding, say we have
   SEQUENCE {,..., [[ x1 OPTIONAL, x2 OPTIONAL, x3 OPTIONAL ]]}

   And this corresponds to { option {{option x1, option x2, option x3 }
   Then does it mean both
     None
   and
     Some (None, None, None)
   will be encoded to the same value?

   The easy solution is to restrict the encoding/decoding to not include
   the case Some (None, None, None). If we are only testing the decoding,
   this shall not be a huge problem. 
 *)

(* Similarly, for Extension Addition Group, we need to have something
   similar. We already have the seq_list, then first, if
   that seq_list is all OPTIONAL, we can have the following.
   Note all OPTIONAL is a condition for this function 
 *)

(* Returns True if all elements are OPTIONAL  *)
Fixpoint check_all_optional (ls : list seq_elem) :=
  match ls with
  | nil => True
  | cons h t =>
      match h with
      | Opt _ _ => check_all_optional t
      | _ => False
      end
  end.

(* It will return true if all are none. Thus
   if it is true, we should not encode it or we
   should not decode it to something correct. 
 *)
Definition check_all_none_seq
  (ls : list seq_elem)
  (all_o : check_all_optional ls)
  (s : seq_type ls) : bool.
  induction ls.
  - apply true.
  - destruct s. destruct a; simpl in  all_o.
    + destruct all_o.
    + destruct s eqn:Es.
      * apply false. 
      * apply (IHls all_o l).
    + destruct all_o.
Defined.

(* We can combine the sequence and sequence ext together and combine it into 
   the larger combinator. 

   Explanations:
   1. For the extension part, if all the extensions are absent, we do not encode
      the extension (aka extension bit set to 0). Here, the extensions are 
      represented as a tuple of option types. Given 
      (seq-type, seq-ext-type) 
      ( (a, (b, unit)),  (option a', (option b', unit)))
     
      if all option in seq-ext-type is None, then the extension bit is set to 0.
      otherwise set to 1. In the compiler this will be mapped into 
      {  a ; b ; option a'; option b' }
      using a projection format. 

   2. For the extension addition group, it gets a bit complicated. They are formed
      as a sequence. there are two cases 
      (1) The sequence is NOT all options, then it is treated as a normal sequence
      (2) The sequence is ALL options. Then we also need to consider the special 
          case where all the options are None, in which case the sequence should 
          not be encoded. The solution is to apply a restrict_format on the 
          format to rule out the case where all options are None, render it as 
          invalid. 
 *)

Definition check_all_none_pf (ext : list typ) (t : seq_ext_type ext)
  : check_all_none ext t -> seq_ext_cond ext t.
  intros.
  induction ext.
  - simpl.  apply I.
  - simpl.  destruct t.
    destruct e.
    + simpl in H.  destruct H.
    + simpl in H.   apply IHext in H.  simpl.
      auto.
Qed.

(* This function returns a all-none construct *)

Definition seq_ext_serialize
  (l : list seq_elem)
  (ser : seq_serial_prod l)
  (ext : list typ)
  (ser_ext : get_serial_prod ext)
  (len_prod : get_to_len_prod ext)
  : Serialize (seq_type l * seq_ext_type ext)  (fun z => seq_cond l (fst z) /\ (seq_ext_cond ext) (snd z)) :=
  fun bf pos z =>
    (* First see if the seq-ext is all None, 
       if so, then, we set the boolean to 0, and only encode
       the non-ext part
     *)
    let seq_enc := seq_serialize l ser in 
    match check_all_none_dec ext (snd z) with
    | left pf_none =>
        match (bool_enc bf pos false) with
        | Some (bf', pos', _) => 
            match seq_enc bf' pos' (fst z) with
            | Some (bf'', pos'', pf') =>
                Some (bf'', pos'', conj pf' (check_all_none_pf _ _ pf_none))
            | None => None        
            end
        | None => None
        end
    | right _ =>
        match (bool_enc bf pos true) with
        | Some (bf', pos', _) => 
            match seq_enc bf' pos' (fst z) with
            | Some (bf'', pos'', pf') =>
                match (ext_serialize ext ser_ext len_prod) bf'' pos'' (snd z) with
                | Some (bf3, pos3, pf'') =>  
                    Some (bf3, pos3, conj pf' pf'')
                | None => None
                end
            | None => None        
            end
        | None => None
        end
    end.

Definition seq_ext_parse
  (l : list seq_elem)
  (par : seq_parse_prod l)
  (ext : list typ)
  (par_ext : get_parse_prod ext)
  : Parse (seq_type l * seq_ext_type ext)
      (fun z => seq_cond l (fst z) /\ (seq_ext_cond ext) (snd z)) :=
  let seq_dec := seq_parse l par in 
  bind_parse (T_Parse _ _ bool_format)
    (fun b _ _  =>
       if b then
         (* The case where b is true, which means ext is encoded *)
         bind_parse seq_dec
           (fun sa pf_sa flg1 =>
              bind_parse (ext_parse ext par_ext)
                (fun se pf_se flg2 =>
                   (* Before we can return, we also need to make sure that it is NOT a all-none *)
                   match (check_all_none_dec ext se) with
                   | left _ => fail_parse
                   | right _ => 
                       return_parse (exist _ (sa, se) (conj pf_sa pf_se)) (flg_add flg1 flg2)
                   end))
       else
         bind_parse seq_dec
           (fun sa pf_sa flg1 =>
              (* Directly return all-none and the proof for all none *)
              return_parse
                (exist _ (sa, (ext_all_none ext)) (conj pf_sa (ext_all_none_pf ext))) flg1)).


Definition seq_ext_to_len0
  (l : list seq_elem)
  (tl : seq_to_len_prod l)
  (ext : list typ)
  (tl_ext : get_to_len_prod ext)
  : (seq_type l * seq_ext_type ext) -> option nat :=
  fun z =>
  match check_all_none_dec ext (snd z) with
  | left _ =>
      (* all-none: encoding is bool(false) + seq only *)
      add_opt (Some 1) (seq_to_len l tl (fst z))
  | right _ =>
      (* not-all-none: encoding is bool(true) + seq + ext *)
      add_opt (Some 1)
        (add_opt (seq_to_len l tl (fst z))
           (seq_ext_to_len ext tl_ext (snd z)))
  end.


(*Definition restrict_enc {A : Set} {P : A -> Prop} (ser : Serialize A P)
                        (cond_b : A -> bool)
  : Serialize A P :=
  fun bf pos a => 
    if (cond_b a)
    then None
    else ser bf pos a.

Definition restrict_dec {A : Set} {P : A -> Prop} (par : Parse A P)
  (cond_b : A -> bool) : Parse A P := 
  fun bf pos => 
    match par bf pos with
    | Some (exist _ a pf_a, pos', flg) => 
        if (cond_b a)
        then None
        else Some (exist _ a pf_a, pos', flg)
    | None => None
    end.*)

(*Module test2.
  Definition l2 := (cons (Opt bool (fun _ => True))
                      ((cons (Opt nat (fun _ => True))
                          (((cons (Opt nat (fun _ => True)) nil)))))).
  
  Lemma l2__all_opt : check_all_optional l2. 
    unfold l2. simpl. auto.
  Qed. *)

(* We also need to add the to-len function for extensions *)



(*
Definition to_len_opt_tuple {A B : Set}
  (na : A -> option nat) (nb : B -> option nat)
  : (A * option B) -> option nat :=
  fun z =>
    match z with
    | (a, Some b) => add_opt (Some 1) (add_opt (na a) (nb b))
    | (a, None) => add_opt (Some 1) (na a)
    end.
                            
*)
