Require Import
          ASN1Parser.Formats.Comb
          ASN1Parser.AbsArray
          ASN1Parser.Array.BitRep
          ASN1Parser.Array.ByteBuffer
          ASN1Parser.Formats.CombFormat.

Require Import
  ASN1Parser.Formats.Term.Unit
  ASN1Parser.Formats.Term.Boolean
  ASN1Parser.Formats.Term.LengthDet.

(* Some basic formats that is used in various different

   Here, we want to have a slight different notation for
   Parse. Serialize would stay the same. 
 *)

Definition bool_enc : Serialize bool (fun _ => True)
  := T_Serial _ _ bool_format. 

(* We could potentially compute this partially
   in this file. 
 *)

(* Option Bind for option monad *)
Definition opt_bind {A B : Type} (a_opt : option A)
  (f : A -> option B)
  : option B :=
  match a_opt with
  | Some a' => f a'
  | None => None
  end.

Definition extend_true {A B} {C D : Prop} 
  (p : option (A * B * C) ) (pf : D) : option (A * B * (D /\ C)) :=
  match p with
  | Some (a, b, c) => Some (a, b, conj pf c)
  | None => None
  end.

(* Simple failure parse. Used in impossible cases *)
Definition fail_parse {A : Set} {P : A -> Prop} : Parse A P :=
  fun bf pos => None.

(* About option used in Sequence and Seq Extensions.
   Both serialize and parse
 *)
(* We add some support for options in general *)
Definition opt_cond {A : Set} (P : A -> Prop) : option A -> Prop :=
  fun a' =>
    match a' with
    | Some a => P a
    | None => True
    end.

Definition opt_serialize {A : Set} {P : A -> Prop} (ser : Serialize A P)
  : Serialize (option A) (opt_cond P) :=
  fun bf pos a =>
    match a with
    | Some a' => ser bf pos a'
    | None => put_unit bf pos tt
    end.

(* Here, opt_parse would depend on some boolean
   read from the bool list.
 *)
Definition opt_parse {A : Set} {P : A -> Prop} (par : Parse A P) (b : bool)
  : Parse (option A) (opt_cond P) :=
  if b
  then bind_parse (par)
          (fun a pf_a flg =>
             return_parse (exist _ (Some a) pf_a) flg)
  else return_parse (exist _ None I) SameVer. 

(* Here are the encoding of default, which is Sequence
   specific. 
 *)
Definition put_fixed_item {A : Set} {P : A -> Prop} (a0 : A) (pf_a0 : P a0) :=
  fun bf pos => match (put_unit bf pos tt) with
                | Some (bf', pos', _) => Some (bf', pos', pf_a0)
                | None => None
                end.

Definition read_fixed_item {A : Set} {P : A -> Prop} (a : {x : A | P x})
  : Parse A P :=
  fun bf pos => match (read_unit bf pos) with
                | Some (_, pos', _) => Some (a, pos', SameVer)
                | None => None
                end. 

Definition dft_serialize {A : Set} {P : A -> Prop} (ser : Serialize A P)
  (eqb_dec : (forall a b : A, {a = b} + {a <> b}))
  (dft : A) (pf_dft : P dft) : Serialize A P :=
  fun bf pos a =>
    match (eqb_dec dft a) with
    | left e => put_fixed_item dft  (eq_ind dft P pf_dft a e) bf pos
    | right _ => ser bf pos a
    end.

(*      
   We could enforce a stronger correctness notation.
   remove the item if it is equal. 
 *)
Definition dft_parse {A : Set} {P : A -> Prop} (par : Parse A P)
  (dft : A) (pf_dft : P dft)
  (eqb_dec : (forall a b : A, {a = b} + {a <> b}))
  (b : bool)
  : Parse A P :=
    if b then
      bind_parse par
        (fun a pf_a flg => 
          match eqb_dec dft a with
          | left _ => fail_parse
          | right _  => return_parse (exist _ a pf_a) flg
          end)
    else
      return_parse (exist _ dft pf_dft) SameVer.

Definition append_parse {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop}
  (parse1 : Parse A P1) (parse2 : Parse B P2)
  : Parse (A * B) (fun z => P1 (fst z) /\ P2 (snd z)) :=
  bind_parse parse1
    (fun a pf_Pa flg1 =>
       bind_parse parse2
         (fun b pf_Pb flg2 =>
            return_parse
              (exist (fun z => P1 (fst z) /\ P2 (snd z))
                 (a, b) (conj pf_Pa pf_Pb)) (flg_add flg1 flg2))).

(* Here, is a serialize function that will append some information. 
     But we do not need any of the proofs for this information. 
 *)
Definition prepend_serialize {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (f : B -> A)
  (serA : Serialize A Pa) 
  (serB : Serialize B Pb)
  : Serialize B Pb :=
  fun bf pos b =>
    match (append_serialize serA serB bf pos ((f b), b)) with
    | Some (bf', pos', conj _ pf_b) => Some (bf', pos', pf_b)
    | None => None
    end.

(* Here, v is encoded before the encoding of B *)
Definition prepend_serialize_fixed {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (v : A)
  (serA : Serialize A Pa)
  (serB : Serialize B Pb)
  : Serialize B Pb :=
  fun bf pos b =>
    match (append_serialize serA serB bf pos (v, b)) with
    | Some (bf', pos', conj _ pf_b) => Some (bf', pos', pf_b)
    | None => None
    end.

(* The transparent version of length, used in Extension and Choice *)
Fixpoint length2 {A : Type} (l : list A) :=
  match l with
  | nil => 0
  | cons h t => S (length2 t)
  end.


Definition proj2_serialize  {A B : Set} (P1 : A -> Prop)
  {P2 : B -> Prop}
  (s : Serialize B P2) (f_inv : B -> A) (f : A -> B)
  (imp2 : forall a: A, f_inv (f a) = a)
  (imp_inv : forall b : B, P2 b -> P1 (f_inv b) /\ f (f_inv b) = b)
  : Serialize A P1
    :=
  fun (bf : BitRep.BA.Buffer) (pos : BitRep.BA.Pos) (a : A) => 
  match s bf pos (f a) with
  | Some (bf', pos', pf_a) => Some (bf', pos',
                                  eq_ind _ P1 (proj1 (imp_inv (f a) pf_a)) a (imp2 a))
  | None => None
  end.

Require Import ASN1Parser.tact.
Require Import ProofIrrelevance.

Section proj2_correct_proofs.
  Context {A B : Set}.
  Context {P2 : B -> Prop}.
  Context {P1 : A -> Prop}.
  Context {b_format : T_Format B P2}.
  Context {f : A -> B}.
  Context {f_inv : B -> A}.
  Hypothesis imp : forall a : A, P1 a -> P2 (f a).
  Hypothesis imp2 : forall a : A, f_inv (f a) = a.
  Hypothesis imp_inv : forall b : B, P2 b -> P1 (f_inv b) /\ f (f_inv b) = b.

  Lemma proj2_enc_consist :
    encode_consistent A P1
      (proj2_serialize P1 (T_Serial B P2 b_format) f_inv f imp2 imp_inv).
  Proof.
    unfold encode_consistent. intros.
    unfold proj2_serialize in H, H0.
    destruct_enc. destruct_enc. inversion H0. inversion H.  subst.
    eassert (EC := CombProp.fmt_enc_consist (T_Correct _ _ b_format)).
    unfold encode_consistent in EC.
    eapply EC.
    - apply E0.
    - rewrite (proof_irrelevance _ p0 p2) in E.
      apply E.
  Qed.

  Lemma proj2_dec_consist :
    decode_consistent A P1
      (proj_parse (T_Parse B P2 b_format) f_inv
         (fun (b : B) (pf_b : P2 b) => proj1 (imp_inv b pf_b))).
  Proof.
    eassert (DC := CombProp.fmt_dec_consist (T_Correct _ _ b_format)).
    unfold decode_consistent in *.
    intros.  unfold proj_parse in H.
    destruct_enc. inversion H. subst.
    eassert (G := DC _ _ _ _ _ _ E).
    split_and. split; auto.
    unfold proj_parse. intros. 
    rewrite (H1 _ _ _ H2).
    decode_eq. 
  Qed.
  
  Lemma proj2_non_inter :
    encode_non_inter A P1
      (proj2_serialize P1 (T_Serial B P2 b_format) f_inv f imp2 imp_inv).
  Proof. 
    eassert (EI := CombProp.fmt_enc_ni (T_Correct _ _ b_format)).
    unfold encode_non_inter in *.
    intros. unfold proj2_serialize in H.
    destruct_enc.  inversion H; subst.
    apply EI in E.  auto.
  Qed.
  
  Lemma proj2_surj :
    format_correct_surj A P1
    (proj2_serialize P1 (T_Serial B P2 b_format) f_inv f imp2 imp_inv)
    (proj_parse (T_Parse B P2 b_format) f_inv
       (fun (b : B) (pf_b : P2 b) => proj1 (imp_inv b pf_b))).
  Proof.
    eassert (EI := CombProp.fmt_surj (T_Correct _ _ b_format)).
    unfold format_correct_surj in *. intros.
    unfold proj2_serialize in H. unfold proj_parse.
    destruct_enc. inversion H. subst.
    apply EI in E.
    rewrite E. decode_eq.
  Qed.
      
  Lemma proj2_inj_same : format_correct_inj_same A P1
    (proj2_serialize P1 (T_Serial B P2 b_format) f_inv f imp2 imp_inv)
    (proj_parse (T_Parse B P2 b_format) f_inv
       (fun (b : B) (pf_b : P2 b) => proj1 (imp_inv b pf_b))).
  Proof. 
    eassert (EI := CombProp.fmt_inj_same (T_Correct _ _ b_format)).
    unfold format_correct_inj_same in *. intros.
    unfold proj_parse in  H. unfold proj2_serialize.
    destruct_enc.
    inversion H.  subst.
    eapply EI in E.  shelve.
    apply H0.
    Unshelve.
    destruct E.  split_and.
    exists x0.
    assert (G := proj2 (imp_inv x p0)).
    split; auto.

    clear H.
    assert (K : exists pf', (T_Serial B P2 b_format bf0 pos (f (f_inv x))) = Some (x0, pos', pf') ).
    { rewrite G. exists p0.  apply H2. }
    destruct K.  rewrite H.  encode_eq. 
  Qed.
      
  Lemma proj2_inj_diff : format_correct_inj_diff A P1
    (proj2_serialize P1 (T_Serial B P2 b_format) f_inv f imp2 imp_inv)
    (proj_parse (T_Parse B P2 b_format) f_inv
       (fun (b : B) (pf_b : P2 b) => proj1 (imp_inv b pf_b)))
    (fun a : A => T_to_len B P2 b_format (f a)).
    unfold format_correct_inj_diff. intros.
    unfold proj_parse in H. destruct_enc. inversion H. subst.
    
    eassert (EI := CombProp.fmt_inj_diff  (T_Correct _ _ b_format)).
    unfold format_correct_inj_diff in EI .
    eassert (G := EI _ _ _ _ _ _ E).
    destruct G.
    clear EI. exists x0.
    intros.
    eassert (G0 := H0 _ _ H1).
    eassert (K := proj2 (imp_inv x p0)). 
    destruct G0.
    - left. clear H0.
      rewrite K. auto.
    - right.  destruct H2. destruct H2.  exists x1. exists x2.
      clear H.
      destruct H2.
      unfold proj2_serialize. (*destruct H2.*)
      
      assert (EqK : exists pf', T_Serial B P2 b_format bf0 pos0 (f (f_inv x)) = Some (x1, x2, pf')).
      { rewrite K. exists p0.
        auto. }
      destruct EqK. rewrite H3. split. 
      * encode_eq.
      * Lia.lia.
  Qed.
  
          
  Lemma proj2_len_correct : format_to_len_correct A P1
    (proj2_serialize P1 (T_Serial B P2 b_format) f_inv f imp2 imp_inv)
    (proj_parse (T_Parse B P2 b_format) f_inv
       (fun (b : B) (pf_b : P2 b) => proj1 (imp_inv b pf_b)))
    (fun a : A => T_to_len B P2 b_format (f a)).
  Proof.
    eassert (EI := CombProp.fmt_len_c (T_Correct _ _ b_format)).
    unfold format_to_len_correct in *.
    split.
    - intros.  unfold proj2_serialize in H.
      destruct_enc. inversion H. subst.
      destruct EI.
      apply H0 in E. auto.
    - intros. unfold proj_parse in H.
      destruct_enc. inversion H. subst. destruct EI.
      apply H1 in E.
      destruct E. exists x0.
      assert (G :=  proj2 (imp_inv x p0)).
      rewrite G.  apply H2.
  Qed.
    
  Lemma proj2_correct : format_correct
         (proj2_serialize P1 (T_Serial B P2 b_format) f_inv f imp2 imp_inv)
         (proj_parse (T_Parse B P2 b_format) f_inv
            (fun (b : B) (pf_b : P2 b) => proj1 (imp_inv b pf_b)))
         (fun a : A => T_to_len B P2 b_format (f a)).
    unfold format_correct.
    split. apply proj2_enc_consist. 
    split. apply proj2_dec_consist. 
    split. apply proj2_non_inter.
    split. apply proj2_surj. 
    split. apply proj2_inj_same.
    split. 
    apply proj2_inj_diff. 
    apply proj2_len_correct. 
  Qed.
  
  
End proj2_correct_proofs. 

Definition proj2_format 
   {A B : Set} {P2 : B -> Prop} (P1 : A -> Prop) (b_format : T_Format B P2) 
   (f : A -> B) (f_inv : B -> A)
   (imp : forall a : A, P1 a -> P2 (f a))
   (imp2 : forall a: A, f_inv (f a) = a)
   (imp_inv : forall b : B, P2 b -> P1 (f_inv b) /\ f (f_inv b) = b) := 
  mk_format
    _ _ 
    (proj2_serialize P1 (T_Serial B P2 b_format) f_inv f imp2 imp_inv )
    
    (proj_parse (T_Parse B P2 b_format) f_inv (fun (b : B) (pf_b : P2 b) => proj1 (imp_inv b pf_b)))
    (fun a : A => T_to_len B P2 b_format (f a))
    (proj2_correct imp2 imp_inv).


(*

Definition det_enc :=  Serialize_T uncons_len_det_format.
Definition small_enc := Serialize_T normally_small_len_det_format.

Definition det_dec :=  Parse_T uncons_len_det_format.
Definition small_dec := Parse_T normally_small_len_det_format.


Definition small_integer_helper : 7 <= INT_MAX_LEN.
  unfold INT_MAX_LEN. Lia.lia. Qed.

Lemma small_integer_helper1 :
  (forall a : nat,
      (fun n : nat => n <= 63) a -> (fun z : nat => z < Nat.pow 2 7) a).
Proof. intros. simpl in *. Lia.lia. Qed.

Definition small_integer_format :=
  Restrict
    (fun n => n <= 63)
    (BasicBits 7 small_integer_helper)
    small_integer_helper1
    (fun n => Compare_dec.le_dec n 63).

Definition small_integer_enc := Serialize_T small_integer_format.
Definition small_integer_dec := Parse_T small_integer_format.
Definition small_integer_to_len := format_length_opt small_integer_format. 

*)
