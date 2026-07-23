Require Import
          ASN1Parser.AbsArray
          ASN1Parser.Formats.Comb
          ASN1Parser.Formats.CombProp
          ASN1Parser.Formats.Comb.HelperComb
          ASN1Parser.Array.BitRep
          Lia.

(* Very trivial lemmas about Serialize_T and Parse_T.
   And we can bring it to 
 *)
Require Import ASN1Parser.tact.

Lemma append_parse_consist {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop}
  (parse1 : Parse A P1)
  (parse2 : Parse B P2)
  (p_1 : decode_consistent _ _ parse1)
  (p_2 : decode_consistent _ _ parse2) : 
  decode_consistent _ _ (append_parse parse1 parse2).
Proof.
  intros. unfold decode_consistent. intros.
  unfold append_parse in *.
  apply bind_parse_consist; auto.  intros.
  apply bind_parse_consist; auto.  intros.
  apply return_parse_consist.
Qed.


Require Import ASN1Parser.Formats.Comb.SeqProd. 

Definition get_cond_prod
  (l : list typ)
  (ser : get_serial_prod l)
  (cond : encode_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a;
      apply (cond _ _ (fst ser) /\ IHl (snd ser)). 
Defined.

Definition get_cond_de_prod
  (l : list typ)
  (par : get_parse_prod l)
  (cond : decode_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a;
      apply (cond _ _ (fst par) /\ IHl (snd par)). 
Defined.

Definition get_cond_both_prod
  (l : list typ)
  (ser : get_serial_prod l)
  (par : get_parse_prod l)
  (cond : en_decode_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a. 
    apply (cond _ _ (fst ser) (fst par) /\ IHl (snd ser) (snd par)). 
Defined.

(* The only proposition is format_to_len_correct. *)
Definition get_cond_tl_prod
  (l : list typ)
  (ser : get_serial_prod l)
  (par : get_parse_prod l)
  (tl : get_to_len_prod l)
  (cond : en_de_tl_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a.
    apply (cond  _ _ (fst ser) (fst par) (fst tl) /\ IHl (snd ser) (snd par) (snd tl)).
Defined.

Require Import ASN1Parser.Formats.Term.Unit.

Lemma put_unit_pos_no_change :
  forall bf bf' pos pos', 
    put_unit bf pos tt = Some (bf', pos', I) ->
    (bf = bf' /\ pos = pos').
Proof.
  intros.
  unfold put_unit in H. destruct_if_in.
  auto.
Qed.

(* To prove sequence non-inter property, since we used
   this function prepend_serialize, we can simply prove that
   this function would satisfy these properties and then
   prove this whole thing. The same with encode_consistent
 *)
Lemma prepend_non_inter 
  {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (f : B -> A)
  (serA : Serialize A Pa) 
  (serB : Serialize B Pb)
  (p_A : encode_non_inter _ _ serA)
  (p_B : encode_non_inter _ _ serB)
  : encode_non_inter _ _ (prepend_serialize f serA serB).
Proof.
  unfold prepend_serialize.
  assert (G := append_non_inter serA serB p_A p_B).
  unfold encode_non_inter. intros.
  destruct_match_new. repeat destruct_let. 
  inversion H; subst. 
  eassert (G1 := G _ _ _ _ _ _ E).
  auto.
Qed.
  
Lemma prepend_consistent
  {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (f : B -> A)
  (serA : Serialize A Pa) 
  (serB : Serialize B Pb)
  (p_A : encode_consistent _ _ serA)
  (p_B : encode_consistent _ _ serB)
  (Bnon_inter : encode_non_inter _ _ serB)
  : encode_consistent _ _ (prepend_serialize f serA serB).
Proof.
  unfold prepend_serialize.
  assert (G := append_encode_consist serA serB p_A p_B).
  unfold encode_consistent. intros.
  repeat destruct_match_new; repeat destruct_let.

  inversion H; inversion H0; subst.
  eapply G; auto. 
  - apply E0.
  - rewrite E. encode_eq. 
Qed.

Definition format_correct_surj_dep 
  {A B : Set} {Pa : A -> Prop}  {Pb : B -> Prop}
  (encode : Serialize B Pb)
  (decode : forall a, Pa a -> Flg -> Parse B Pb)
  (f : B -> A) :=
  forall (b : B) (bf bf' : BA.Buffer) (pos pos' : BA.Pos)
         (pf : Pb b) (pf_a : Pa (f b)),
      encode bf pos b = Some (bf', pos', pf) ->
      decode (f b) pf_a SameVer bf' pos =
        Some (exist Pb b pf, pos', SameVer). 


Lemma prepend_surj_dep {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (f : B -> A)
  (serA : Serialize A Pa) (serB : Serialize B Pb)
  (parA : Parse A Pa) (parB : forall a, Pa a -> Flg -> Parse B Pb)
  (dec_con_A : decode_consistent _ _ parA)
  (non_inter_B : encode_non_inter _ _ serB)
  (surjA : format_correct_surj _ _ serA parA)
  (surjB : format_correct_surj_dep serB parB f)
  : format_correct_surj _ _ 
      (prepend_serialize f serA serB)
      (bind_parse parA
         (fun a pf_a flg => parB a pf_a flg)). 
Proof.
  unfold format_correct_surj. intros.
  unfold prepend_serialize, append_serialize in H.
  repeat (destruct_match_new; repeat destruct_let). 
  inversion E. inversion H. subst. simpl in *.

  unfold bind_parse.
  eassert (G := surjA _ _ _ _ _ _ E0). 
  clear_redu_all.
  eassert (EB1 := non_inter_B _  _  _ _ _ _ E1). 
  destruct (dec_con_A _ _ _ _ _ _ G). split_and. 
  unfold BProp.le_pos in H. 
  eassert (EA := H0 _ _ _ (equiv_b_le_zero _ _ _ _ H H1)).
  rewrite EA. 
  eapply surjB. rewrite E1.  encode_eq.
Qed.

Lemma append_surj_dep {A B C: Set} {Pa : A -> Prop} {Pb : B -> Prop}
                      {Pc : C -> Prop}
  (f : B -> C) 
  (serA : Serialize A Pa) (serB : Serialize B Pb)
  (parA : Parse A Pa)  (parB : forall c, Pc c -> Flg -> Parse B Pb)
  (dec_con_A : decode_consistent _ _ parA)
  (non_inter_B : encode_non_inter _ _ serB)
  (surjA : format_correct_surj _ _ serA parA)
  (surjB : format_correct_surj_dep serB parB f)
  : format_correct_surj_dep  
      (append_serialize serA serB)
      (fun c pf_c flg => append_parse parA (parB c pf_c flg))
      (fun z => f (snd z)).
  (* g = fun z => f (snd z)  *)
Proof.
  unfold format_correct_surj_dep. intros.
  unfold append_serialize in H.
  repeat (destruct_match_new; repeat destruct_let).
  inversion H; subst. clear_redu_all.  
  
  unfold append_parse, bind_parse, return_parse.

  eassert (EB1 := non_inter_B _  _  _ _ _ _ E0).
  eassert (G := surjA _  _ _ _ _ _ E). 
  destruct (dec_con_A _ _ _ _ _ _ G). split_and. 
  unfold BProp.le_pos in H. 
  eassert (EA := H0 _ _ _ (equiv_b_le_zero _ _ _ _ H H1)).

  rewrite EA.
  eassert (EB := surjB _ _ _ _ _ _ _ E0). rewrite EB.

  destruct b. simpl.  decode_eq. 
Qed.

(* This proof should be similar, we need to have this theorem
   on the latter half. Then we can do a induction of l.
 *)
Definition format_correct_inj_dep 
  {A B : Set} {Pa : A -> Prop}  {Pb : B -> Prop}
  (encode : Serialize B Pb)
  (decode : forall a, Pa a -> Flg -> Parse B Pb)
  (f : B -> A) :=
  forall (b : B) (bf : BA.Buffer) (pos pos' : BA.Pos)
         (pf : Pb b) (pf_a : Pa (f b)),
    decode (f b) pf_a SameVer bf pos =
      Some (exist Pb b pf, pos', SameVer) -> 
    (forall bf0 : BA.Buffer,
        BA.len bf0 = BA.len bf ->
        exists bf0' : BA.Buffer,
          encode bf0 pos b = Some (bf0', pos', pf) /\
            EQ.equiv_b bf bf0' pos pos' pos pos').


Lemma append_inj_dep {A B C: Set} {Pa : A -> Prop} {Pb : B -> Prop}
                      {Pc : C -> Prop}
  (f : B -> C) 
  (serA : Serialize A Pa) (serB : Serialize B Pb)
  (parA : Parse A Pa)  (parB : forall c, Pc c -> Flg -> Parse B Pb)
  (non_inter_A : encode_non_inter _ _ serA)
  (non_inter_B : encode_non_inter _ _ serB)
  (injA : format_correct_inj_same _ _ serA parA)
  (injB : format_correct_inj_dep serB parB f)
  : format_correct_inj_dep  
      (append_serialize serA serB)
      (fun c pf_c flg => append_parse parA (parB c pf_c flg))
      (fun z => f (snd z)).
Proof.
  unfold format_correct_inj_dep. intros.
  unfold append_parse, bind_parse, return_parse in H.
  repeat destruct_enc. inversion H.  subst. unfold append_serialize.
  
  destruct (flg_add_to_same _ _ H4). subst. clear H. clear H4. 
  destruct (injA _ _ _ _ _ E bf0 H0). split_and.
  simpl in *.  rewrite H1.

  eassert (LE := same_len_after_enc serA non_inter_A H1).
  assert (BA.len x1 = BA.len bf). { Lia.lia. }
  destruct (injB _ _ _ _ _ _ E0 _ H4). split_and. 
  
  rewrite H6. exists x2. split.
  - encode_eq.
  - eapply format_correct_inj_helper.
    + apply H2.
    + apply H7.
    + eapply non_inter_B. apply H6.
Qed.


Definition format_to_len_correct_dep
  {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (encode : Serialize B Pb)
  (decode : forall a, Pa a -> Flg -> Parse B Pb)
  (to_len : B -> option nat)
  (f : B -> A) := 
  (forall (b : B) (bf bf' : BA.Buffer) (pos pos' : BA.Pos) (pf : Pb b),
      encode bf pos b = Some (bf', pos', pf) ->
      to_len b = Some (BA.to_nat pos' - BA.to_nat pos)) /\
    (forall (b : B) (bf : BA.Buffer) (pos pos' : BA.Pos) (pf : Pb b) (pf_a : Pa (f b)) (flg flg' : Flg),
        decode (f b) pf_a flg bf pos = Some (exist Pb b pf, pos', flg') ->
        exists n : nat, to_len b = Some n).


Definition format_correct_inj_diff_dep 
  {A B : Set} {Pa : A -> Prop}  {Pb : B -> Prop}
  (encode : Serialize B Pb)
  (decode : forall a, Pa a -> Flg -> Parse B Pb)
  (get_len : B -> option nat)
  (f : B -> A) :=
  forall (b : B) (bf : BA.Buffer) (pos pos' : BA.Pos)
         (pf : Pb b) (pf_a : Pa (f b)) (flg flg' : Flg),
    decode (f b) pf_a flg bf pos =
      Some (exist Pb b pf, pos', flg') ->
    (exists min_len : nat,
      forall pos0 bf0,
        BA.to_nat pos0 + min_len <= BA.len bf0 ->
        (~ (match (get_len b) with
            | Some a' => get_byte_len a' < Nat.pow 2 14
            | None => True
            end)) \/
          (exists (bf0' : BA.Buffer) pos0',
              (encode bf0 pos0 b = Some (bf0', pos0', pf) /\
                 BA.to_nat pos0' <= BA.to_nat pos0 + min_len))).

Opaque Nat.pow.
Lemma append_inj_diff_dep {A B C: Set} {Pa : A -> Prop} {Pb : B -> Prop}
                      {Pc : C -> Prop}
  (f : B -> C) 
  (serA : Serialize A Pa) (serB : Serialize B Pb)
  (tlA : A -> option nat)
  (parA : Parse A Pa)  (parB : forall c, Pc c -> Flg -> Parse B Pb)
  (tlB : B -> option nat)
  (non_inter_A : encode_non_inter _ _ serA)
  (tl_crtA : format_to_len_correct _ _ serA parA tlA)
  (tl_crtB : format_to_len_correct_dep serB parB tlB f)
  (injA : format_correct_inj_diff _ _ serA parA tlA)
  (injB : format_correct_inj_diff_dep serB parB tlB f)
  : format_correct_inj_diff_dep  
      (append_serialize serA serB)
      (fun c pf_c flg => append_parse parA (parB c pf_c flg))
      (append_to_len tlA tlB)
      (fun z => f (snd z)).
Proof.
  unfold format_correct_inj_diff_dep. intros.
  unfold append_parse, bind_parse, return_parse in H.
  repeat destruct_enc. inversion H. subst. unfold append_serialize.
  
  clear H.  simpl in *. 
  eassert (Ga := injA _ _ _ _ _ _ E). 
  eassert ( Gb := injB _ _ _ _ _ _ _ _ E0).
  destruct_ex.
  
  exists (x1 + x2). intros.
  assert (BA.to_nat pos0 + x2 <= BA.len bf0). { Lia.lia. }

  eassert (K1 := (proj2 tl_crtA) _ _ _ _ _ _  E).
  eassert (K2 := (proj2 tl_crtB) x0 bf p pos' p2 pf_a flg _ E0). 
  
  destruct_ex.  unfold append_to_len.  simpl.
  rewrite H3. rewrite H4. 
  simpl.
  eassert (G'' := H0 _ _ H2). destruct_ex. split_and. 

  destruct G''.
  { left. rewrite H4 in H7.
    assert (x4 <= x4 + x3). { lia. }
    apply get_byte_len_mono in H8. lia. } 

  destruct_ex. split_and. rewrite H8. 
  eassert (LE :=  same_len_after_enc serA non_inter_A H8).
  assert (BA.to_nat x6 + x1 <= BA.len x5).  { lia. }
  
  assert (G' := H _  _  H7).
  destruct G'.
  { left. rewrite H3 in H10. 
    assert (x3 <= x4 + x3). { lia. }
    apply get_byte_len_mono in H11. lia. } 
    
  destruct_ex. split_and. 
  rewrite H11.  right. 

  exists x7. exists x8.
  split.
  - encode_eq.
  - lia. 
Qed.

(* This is for option type *)
Lemma opt_non_inter
  {A : Set} {P : A -> Prop} (ser : Serialize A P)
  (p_S : encode_non_inter _ _ ser)
  : encode_non_inter _ _ (opt_serialize ser).
Proof.
  unfold opt_serialize,
    encode_non_inter. intros.
  destruct_match_new.
  - eapply p_S.  apply H.
  - eapply put_unit_non_inter. apply H.
Qed.

Lemma opt_encode_consist
  {A : Set} {P : A -> Prop} (ser : Serialize A P)
  (p_S : encode_consistent _ _ ser)
  : encode_consistent _ _ (opt_serialize ser).
Proof.
  unfold opt_serialize, encode_consistent.
  intros. repeat destruct_match_new.
  - eapply p_S.
    + apply H.
    + apply H0.
  - eapply put_unit_consist.
    + apply H.
    + apply H0.
Qed.

Lemma opt_decode_consist
  {A : Set} {P : A -> Prop} (par : Parse A P)
  (p_S : decode_consistent _ _ par)
  (b : bool)
  : decode_consistent _ _ (opt_parse par b).
Proof.
  unfold opt_parse.
  destruct b.
  - apply bind_parse_consist; auto. intros. 
    apply return_parse_consist.
  - apply return_parse_consist.
Qed.

