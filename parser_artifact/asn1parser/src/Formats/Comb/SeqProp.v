Require Import
  ASN1Parser.Array.ByteBuffer
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.CombProp
  ASN1Parser.Formats.Comb.SeqProd
  ASN1Parser.Formats.Comb.Seq
  ASN1Parser.Formats.Comb.HelperComb
  ASN1Parser.Formats.Comb.HelperProp.

Require Import ASN1Parser.Formats.Term.Unit.

Require Import ASN1Parser.tact.

Require Import ProofIrrelevance.

(* Here are for the format correctness combinators
   Note we have 6 different properties for the
   encoders and decoders. 
 *)

Definition seq_cond_prod
  (l : list seq_elem)
  (ser : seq_serial_prod l)
  (cond : encode_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a;
      apply (cond _ _ (fst ser) /\ IHl (snd ser)). 
Defined.

Definition seq_cond_de_prod
  (l : list seq_elem)
  (ser : seq_parse_prod l)
  (cond : decode_cond_type) : Prop.
  induction l.
  - apply True. 
  - destruct a;
      apply (cond _ _ (fst ser) /\ IHl (snd ser)). 
Defined.

Definition seq_cond_both_prod
  (l : list seq_elem)
  (ser : seq_serial_prod l)  (par : seq_parse_prod l)
  (cond : en_decode_cond_type) : Prop.
  induction l.
  - apply True. 
  - destruct a;
      apply (cond _ _ (fst ser) (fst par) /\ IHl (snd ser) (snd par)). 
Defined.

Definition seq_cond_tl_prod
  (l : list seq_elem)
  (ser : seq_serial_prod l)
  (par : seq_parse_prod l)
  (tl : seq_to_len_prod l)
  (cond : en_de_tl_cond_type) : Prop.
  induction l.
  - apply True.
  - destruct a;
      apply (cond _ _ (fst ser) (fst par) (fst tl) /\ IHl (snd ser) (snd par) (snd tl)). 
Defined.

Lemma dft_non_inter
  {A : Set} {P : A -> Prop} (ser : Serialize A P)
  (eqb_dec : (forall a b : A, {a = b} + {a <> b}))
  (dft : A) (pf_dft : P dft)
  (p_S : encode_non_inter _ _ ser)
  : encode_non_inter _ _ (dft_serialize ser eqb_dec dft pf_dft).
Proof.
  unfold dft_serialize, encode_non_inter.
  intros. 
  destruct_match_dec_new.
  - unfold put_fixed_item in H. destruct_match_new.
    repeat destruct_let. inversion H. subst. 
    eapply put_unit_non_inter. apply E0.
  - eapply p_S. apply H. 
Qed.

Lemma seq_latter_non_inter
  (l : list seq_elem) (ser : seq_serial_prod l)
  (non_iter_prod : seq_cond_prod l ser encode_non_inter) :
  encode_non_inter _ _  (seq_serialize_latter l ser).
Proof.
  generalize dependent ser. 
  induction l; intros.
  - simpl. apply put_unit_non_inter.
  - destruct a; simpl; destruct non_iter_prod as [H H0];
      apply append_non_inter; auto;
      try (apply IHl; auto).
    + apply opt_non_inter. auto.
    + apply dft_non_inter. auto.
Qed.

Lemma dft_encode_consist
  {A : Set} {P : A -> Prop} (ser : Serialize A P)
  (eqb_dec : (forall a b : A, {a = b} + {a <> b}))
  (dft : A) (pf_dft : P dft)
  (p_S : encode_consistent _ _ ser)
  : encode_consistent _ _ (dft_serialize ser eqb_dec dft pf_dft).
Proof.
  unfold dft_serialize, encode_consistent.
  intros. unfold put_fixed_item in *.
  repeat destruct_match_dec_new; repeat destruct_match_new;
    repeat destruct_let;
    inversion H0; inversion H; subst.
  - eapply put_unit_consist.
    + apply E1.
    + rewrite E0. encode_eq.
  - eapply p_S.
    + apply H3.
    + apply H0.
Qed.
  
Lemma seq_latter_encode_consist
  (l : list seq_elem) (ser : seq_serial_prod l)
  (non_iter_prod : seq_cond_prod l ser encode_non_inter)
  (en_consist_prod : seq_cond_prod l ser encode_consistent) :
  encode_consistent _ _ (seq_serialize_latter l ser).
Proof.
  generalize dependent ser.
  induction l; intros.
  - simpl. apply put_unit_consist.
  - destruct a; simpl; destruct ser, en_consist_prod, non_iter_prod;
      simpl in *;
      apply append_encode_consist; auto; try (apply IHl; auto);
      try (apply seq_latter_non_inter; auto).
    + apply opt_encode_consist. auto.
    + apply dft_encode_consist. auto.
Qed.

Lemma fail_decode_consist (A : Set) (P : A -> Prop) : 
  decode_consistent A P fail_parse.
Proof.
  unfold decode_consistent. intros.
  inversion H.
Qed.

Lemma dft_decode_consist
  {A : Set} {P : A -> Prop} (par : Parse A P)
  (eqb_dec : (forall a b : A, {a = b} + {a <> b}))
  (dft : A) (pf_dft : P dft)
  (p_S : decode_consistent _ _ par)
  (b : bool)
  : decode_consistent _ _ (dft_parse par dft pf_dft eqb_dec b).
Proof.
  unfold dft_parse.
  destruct b.
  - apply bind_parse_consist; auto.  intros.
    destruct (eqb_dec dft a).
    + apply fail_decode_consist.
    + apply return_parse_consist.
  - apply return_parse_consist.
Qed.
  
Lemma seq_latter_decode_consist  (l : list seq_elem) :
  forall (par : seq_parse_prod l)
  (bl : list bool)  (pf_bl : length bl = bit_list_len l)
  (decode_consist_prod : seq_cond_de_prod l par decode_consistent),
  decode_consistent _ _ (seq_parse_latter l par bl pf_bl).
Proof. 
  induction l; intros. 
  - unfold seq_type, seq_cond. simpl. 
    apply read_unit_consist. 
    
  - destruct a; simpl. 
    + simpl in *.  unfold id in pf_bl.  destruct par.  
      simpl in *.  destruct decode_consist_prod.
      apply append_parse_consist; simpl; auto.
    + simpl in pf_bl. destruct bl; inversion pf_bl.
      destruct par.  simpl in *.  destruct decode_consist_prod.
      apply append_parse_consist; simpl; auto.
      apply  opt_decode_consist. auto.
    + simpl in pf_bl. destruct bl; inversion pf_bl.
      destruct par.  simpl in *.  destruct decode_consist_prod.
      apply append_parse_consist; simpl; auto.
      apply dft_decode_consist. auto.
Qed.


Require Import ASN1Parser.Array.BitRep.

Lemma append_unit_eq_nothing {A : Set} {Pr : A -> Prop}
  (encode : Serialize A Pr)
  (enc_ni : encode_non_inter _ _  encode)
  : forall bf bf' pos pos' a pf_a,
    append_serialize put_unit encode bf pos (tt, a) =
      Some (bf', pos', conj I pf_a) <->
      encode bf pos a = Some (bf', pos', pf_a).
Proof.
  intros. 
  unfold append_serialize.
  split; intros.
  - repeat destruct_enc. inversion H. subst.
    destruct t. 
    destruct (put_unit_pos_no_change _ _ _ _ E). subst.
    simpl in *. rewrite E0; encode_eq.
  - unfold put_unit. 
    destruct (Compare_dec.le_dec (BA.to_nat pos) (BA.len bf)).
    + simpl. rewrite H.  encode_eq.
    + apply enc_ni in H. split_and.
      apply EQ.equiv_b_implies_valid_pair in H0. split_and.
      unfold EQ.valid_pos_pair in *.  Lia.lia.
Qed.

Lemma seq_latter_surj 
  (l : list seq_elem) :
  forall (ser : seq_serial_prod l)
         (par : seq_parse_prod l)
         (par_consist : seq_cond_de_prod l par decode_consistent)
         (ser_non_inter : seq_cond_prod l ser encode_non_inter)
         (prod_surj : seq_cond_both_prod l ser par format_correct_surj),
    format_correct_surj_dep (seq_serialize_latter l ser)
      (fun (a : list bool)
           (pf_a : length a = bit_list_len l) (_ : Flg) =>
         seq_parse_latter l par a pf_a) (seq_type_to_bit_list l).
Proof.
  induction l; intros.
  - simpl. unfold format_correct_surj_dep.  intros.
    eapply unit_format_surj.  apply H. 
    
  - unfold format_correct_surj_dep. intros. destruct b, ser, par.
    destruct a. 
    + simpl in *. split_and. 
      eassert (G := IHl l1 l2 H7 H5 H3).
      eassert (T := append_surj_dep _
                      _ _ _ _ H6
                      (seq_latter_non_inter _ _ H5) H2 G
                      (s, l0) bf bf' pos pos' (conj H0 H1) _ H). 
      simpl in T. rewrite T.  auto.
    +  (* Similar to before,  *)
      simpl in *. split_and.
      eassert (G := IHl l1 l2 H7 H5 H3). 
      destruct s eqn:Es. 
      * inversion pf_a. 
        eassert (T := append_surj_dep _
                        _ _ _ _ H6 
                        (seq_latter_non_inter _ _ H5) H2 G
                      (a, l0) bf  bf' pos pos' (conj H0 H1) H9 H).
        simpl in T.
        
        unfold append_parse, bind_parse, return_parse in T.
        repeat (destruct_match_new; repeat destruct_let). 
        inversion T. subst. 
        simpl. unfold append_parse, bind_parse, return_parse.
        rewrite E. 
        assert ((eq_add_S (length (seq_type_to_bit_list l l0))
                   (bit_list_len l) pf_a) = H9).
        { apply proof_irrelevance. }
        rewrite H8, E0. decode_eq.
      * unfold seq_elem_to_serial in s0. simpl in s0. 
        assert (append_serialize (opt_serialize s0)
                  (seq_serialize_latter l l1) bf pos (None, l0) =
                  append_serialize put_unit
                    (seq_serialize_latter l l1) bf pos (tt, l0)).
        { unfold append_serialize. simpl.  auto. } 
        destruct H0. 
        rewrite H in H8.
        eassert (AN := append_unit_eq_nothing _
                         (seq_latter_non_inter _ _ H5)
                         bf bf' pos pos' l0 H1).
        rewrite AN in H.

        unfold opt_parse, append_parse, bind_parse, return_parse.
        eapply G in H. 
        rewrite H. decode_eq.
        
    + simpl in *. split_and.
      eassert (G := IHl l1 l2 H7 H5 H3). 
      destruct (eqb_dec default s) eqn:Es.
      * subst. unfold seq_elem_to_serial in s0. simpl in s0. 
        assert (append_serialize
                  (dft_serialize s0 eqb_dec s pf_dft)
                  (seq_serialize_latter l l1) bf pos (s, l0) =
                  match (append_serialize put_unit
                           (seq_serialize_latter l l1) bf pos (tt, l0)) with
                  | Some (bf'', pos'', conj _ Hl) =>
                      Some (bf'', pos'', conj H0 Hl)
                  | None => None
                  end
               ).
        { unfold dft_serialize, append_serialize. simpl.
          rewrite Es. simpl. unfold put_fixed_item. 
          destruct (put_unit bf pos tt); repeat destruct_let_goal;
            auto.
          destruct (seq_serialize_latter l l1 b p l0); repeat destruct_let_goal; auto.
          encode_eq. } 
        rewrite H8 in H.
        destruct_enc. inversion H. subst.
        clear H. 

        simpl. unfold append_parse, bind_parse, return_parse.

        eassert (AN := append_unit_eq_nothing _
                        (seq_latter_non_inter _ _ H5)
                        bf bf' pos pos' l0 H1).
        destruct t. 
        assert (H1 = s2). { apply proof_irrelevance. }
        rewrite <- H in E.  rewrite AN in E. 
        
        eassert (G' := G _ _ _ _ _ _ _ E). 
        
        rewrite G'.  decode_eq.
      * simpl in *.
        inversion pf_a.  unfold seq_elem_to_serial in s0. simpl in s0. 
        assert ( append_serialize
                   (dft_serialize s0 eqb_dec default pf_dft)
                   (seq_serialize_latter l l1) bf pos (s, l0) =
                   append_serialize s0
                     (seq_serialize_latter l l1) bf pos (s, l0)
               ).
        { unfold append_serialize, dft_serialize.
          simpl. 
          rewrite Es. auto. } 
        rewrite H8 in H.
        eassert (T := append_surj_dep _
                        _ _ _ _ H6 
                        (seq_latter_non_inter _ _ H5) H2 G
                      (s, l0) bf  bf' pos pos' (conj H0 H1) H9 H).
        simpl in T. 

        unfold append_parse, bind_parse, return_parse.
        unfold append_parse, bind_parse, return_parse in T.
        repeat (destruct_match_new; repeat destruct_let). 
        inversion T. subst. 
        rewrite Es. 
        assert ( (eq_add_S (length (seq_type_to_bit_list l l0))
                    (bit_list_len l) pf_a) =
                   H9). { apply proof_irrelevance. }
        rewrite H10, E0. decode_eq.
Qed.
        
Lemma seq_surj  (l : list seq_elem) :
  forall (ser : seq_serial_prod l)
         (par : seq_parse_prod l)
         (ser_non_inter : seq_cond_prod l ser encode_non_inter)
         (par_consist : seq_cond_de_prod l par decode_consistent)
         (prod_surj : seq_cond_both_prod l ser par format_correct_surj),
    format_correct_surj _ _
      (seq_serialize l ser)
      (seq_parse l par).
Proof.
  intros.
  unfold format_correct_surj. unfold seq_serialize, seq_parse.
  assert (G := T_Correct _ _ (BoolList.list_bool_format (bit_list_len l))).
  apply prepend_surj_dep. 
  - apply fmt_dec_consist in G. unfold BoolList.bool_list_parse.
    auto. 
  - apply seq_latter_non_inter. auto. 
  - apply fmt_surj in G. unfold BoolList.bool_list_parse, BoolList.bool_list_serialize.
    auto. 
  - apply seq_latter_surj; auto. 
Qed.
  
      (*
prepend_serialize f enc1 enc2 

     And z <- dec1 ;;
         y <- dec2 z ;;

     very similar to sigma.

     iff bl = (seq_type_to_bit_list l a) and a is the input. 
     surj (ser_latter l ser) (par_latter l par bl pf_bl)

     in other words, bl = f a as the input. 
   *)

(* We know that serA is a basic type, which means it will
   always output a SameVer. We should add that here. 
 *)

(* Question is that is this lemma more general? *)

Lemma seq_type_to_bit_list_valid_inj (l : list seq_elem) :
  forall
    (par : seq_parse_prod l)
    (a : seq_type l) pf x pf_l bf pos pos' flg,
    seq_parse_latter l par x pf_l bf pos = Some (exist (seq_cond l) a pf, pos', flg) -> 
    seq_type_to_bit_list l a = x. 
Proof.
  induction l.
  - intros.  simpl in *.  destruct x; auto.
    simpl in pf_l. inversion pf_l.
  - intros. simpl in H.  unfold append_parse, bind_parse, return_parse in H.
    destruct a; simpl in a0; destruct a0; destruct par.
    + simpl. simpl in H. 
      repeat destruct_enc. inversion H. subst. 
      clear H. 
      eapply IHl. apply E0.
    + destruct x.
      * simpl in pf_l. inversion pf_l.
      * repeat destruct_enc.  simpl in E. inversion H. 
        subst. clear H. 
        unfold opt_parse, bind_parse, return_parse in E.
        
        destruct b eqn:Eb.
        { destruct_enc. inversion E. subst. clear E. 
          simpl. f_equal.  eapply IHl. apply E0. } 
        { inversion E. subst. simpl. f_equal.
          eapply IHl. apply E0. }
        
    + destruct x.
      * simpl in pf_l.  inversion pf_l.
      * repeat destruct_enc. inversion H. 
        subst. clear H.
        unfold dft_parse, bind_parse, return_parse in E.
        
        destruct b eqn:Eb. 
        { destruct_enc. destruct (eqb_dec default x0) eqn:Ed.
          - unfold fail_parse in E. inversion E.
          - inversion E. subst. simpl.
            rewrite Ed. f_equal. eapply IHl. apply E0. }
        { (* default equals s *)
          inversion E. simpl in E0.
          simpl.
          destruct (eqb_dec default s).
          - f_equal.  eapply IHl.
            apply E0.
          - destruct (n H0). 
        }
Qed.
  
Lemma seq_latter_inj_same
  (l : list seq_elem) :
  forall (ser : seq_serial_prod l)
         (par : seq_parse_prod l)
         (ser_non_inter : seq_cond_prod l ser encode_non_inter)
         (prod_inj : seq_cond_both_prod l ser par format_correct_inj_same),
    format_correct_inj_dep (seq_serialize_latter l ser)
      (fun (a : list bool)
           (pf_a : length a = bit_list_len l) (_ : Flg) =>
         seq_parse_latter l par a pf_a) (seq_type_to_bit_list l).
Proof.
  induction l; unfold format_correct_inj_dep; intros. 
  - simpl in H. simpl.
    apply unit_format_inj. auto. auto. 
  - intros. 
    destruct a; destruct ser, ser_non_inter, prod_inj, b. 
    + eassert (G := append_inj_dep _ _ _ _ _ H1
                      (seq_latter_non_inter _ _ H2)
                      H3
                      (IHl _ _  H2 H4)).

      simpl in H. simpl in G. 
      eassert (G1 := G _ bf pos pos' pf pf_a H). 
      apply G1. auto.
    + simpl in s0.  destruct s0 eqn:Es. 
      * simpl in H. simpl in *.
        destruct pf. inversion pf_a.
        unfold seq_elem_to_serial in s. simpl in s. 
        assert (append_parse (fst par)
                  (seq_parse_latter l (snd par) (seq_type_to_bit_list l l1) H6) bf pos =
                  Some (exist _ (a, l1) (conj p s1), pos', SameVer)).
        { unfold append_parse, bind_parse, return_parse in *.
          repeat destruct_enc. inversion H. inversion E. subst. 
          destruct par. simpl in *.
          assert (H6 = (eq_add_S (length (seq_type_to_bit_list l l1)) (bit_list_len l) pf_a)).
          { apply proof_irrelevance. }
          subst. rewrite E0. inversion H11. subst. decode_eq. }
        
        eassert (G := append_inj_dep _ _ _ _ _ H1
                        (seq_latter_non_inter _ _ H2)
                        H3
                        (IHl _ _ H2 H4) (a, _) bf pos pos' (conj p s1) H6 H5
                        bf0 H0).

        destruct G; split_and. 
        exists x. split; auto.
      * simpl in H. unfold append_parse, bind_parse, return_parse in H.
        destruct_enc. inversion H. destruct f; inversion H8. subst.
        simpl.

        eassert (G := IHl _ _ H2 H4 _ _ _ _ _ _ E bf0 H0).
        destruct G. split_and. exists x. split; auto.
                
        rewrite <- append_unit_eq_nothing in H6.
        { simpl in H6.
          unfold append_serialize in *.  simpl in *.
          rewrite H6. encode_eq. }
        { apply seq_latter_non_inter. auto. }
    + destruct (eqb_dec default s0). 
      * generalize dependent pf_a. subst s0. simpl. 

        assert (eqb_dec default default = left eq_refl).
        { assert (default = default).
          - apply eq_refl.
          - destruct (eqb_dec default default).
            + f_equal.  apply proof_irrelevance.
            + destruct (n H).
        } 

        rewrite H. intros. 
        
        unfold append_parse, bind_parse, return_parse in H5.
        
        repeat destruct_enc. unfold dft_parse, return_parse in E. 
        inversion E. 
        inversion H5.  apply flg_add_to_same in H13. split_and.
        subst. clear H10. clear H6. clear E. clear H5.  
                
        eassert (G := IHl _ _ H2 H4 _ _ _ _ _ _ E0 _ H0). 
        destruct G. split_and. exists x0. split; auto.

        rewrite <- append_unit_eq_nothing in H6.
        { unfold append_serialize in *.
          unfold dft_serialize. simpl. unfold put_fixed_item.
          simpl.
          rewrite H. 
          destruct_enc. simpl in E.  rewrite E.  
          destruct_enc. simpl in E1. inversion H6.  subst. rewrite E1.  encode_eq. }
        { apply seq_latter_non_inter. auto. }
      * generalize dependent pf_a. simpl.

        assert (eqb_dec default s0 = right n).
        { destruct (eqb_dec default s0).
          + destruct (n e).
          + f_equal.  apply proof_irrelevance.
        }

        rewrite H. intros. 

        inversion pf_a. destruct pf. 
        assert (append_parse (fst par)
                  (seq_parse_latter l (snd par) (seq_type_to_bit_list l l1) H7) bf pos =
                  Some (exist
                          (fun z : A * seq_type l => P (fst z) /\ seq_cond l (snd z))
                          (s0, l1) (conj p s1), pos', SameVer)).
        { unfold append_parse, dft_parse, bind_parse, return_parse in *.
          repeat (destruct_enc). 
          inversion H5. apply flg_add_to_same in H11. split_and. subst. 
          clear H5.

          destruct (eqb_dec default x1).
          { unfold fail_parse in E. inversion E. }
          inversion E. subst. clear E. 
          destruct par. simpl in *. 

          assert (H7 = (eq_add_S (length (seq_type_to_bit_list l l1)) (bit_list_len l) pf_a)).
          { apply proof_irrelevance. } 
          subst. rewrite E0. decode_eq. }

        eassert (G := append_inj_dep _ _ _ _ _ H1
                        (seq_latter_non_inter _ _ H2)
                        H3
                        (IHl _ _ H2 H4) (s0, _) bf pos pos' (conj p s1) H7 H6
                        bf0 H0).

        destruct G. split_and. simpl in *.  exists x. split; auto.

        unfold append_serialize, dft_serialize in *. simpl.
        rewrite H.
        auto.
Qed.

Require Import Lia. 

Lemma seq_inj_same  (l : list seq_elem) :
  forall (ser : seq_serial_prod l)
         (par : seq_parse_prod l)
         (ser_non_inter : seq_cond_prod l ser encode_non_inter)
         (prod_inj : seq_cond_both_prod l ser par
                        format_correct_inj_same),
    format_correct_inj_same _ _ (seq_serialize l ser)
      (seq_parse l par).
Proof.
  intros. unfold format_correct_inj_same.  intros.
  unfold seq_parse, bind_parse in H.
  destruct_enc.
  unfold seq_serialize, prepend_serialize. 

  (* Here, we must add something *)
  simpl.
  eassert (Ex :=  seq_type_to_bit_list_valid_inj l par _ _ _ _ _ _ _ _ H).
  rewrite Ex.

  (* NTS E renders f to be SameVer *)
  eassert (G' :=  BoolList.bool_list_SameVer _ _ _ _ _ _ _ E).
  subst. 
  
  assert (G := T_Correct _ _ (BoolList.list_bool_format (bit_list_len l))).
  assert (BI := fmt_inj_same G).
  eassert (G' := BI _ _ _ _ _ E _ H0).
  destruct G'.  split_and. 
  unfold append_serialize, fst.
  
  eassert (G1 := seq_latter_inj_same l ser par ser_non_inter prod_inj
                   _ _ _ _ _ _  H). 
  
  eassert (LE := same_len_after_enc _ (fmt_enc_ni G) H2). 
  assert (BA.len x = BA.len bf). { Lia.lia. }
  destruct (G1 x H1). split_and.
  simpl. unfold BoolList.bool_list_serialize.  rewrite H2. 
  rewrite H5. exists x0. split.
  - encode_eq.
  - eapply format_correct_inj_helper.
    + apply H3.
    + auto.
    + eapply  seq_latter_non_inter. eauto.
      apply H5.
Qed.

(*  *)
Lemma seq_to_len_latter_correct  (l : list seq_elem) :
  forall (ser : seq_serial_prod l)
         (par : seq_parse_prod l)
         (tl : seq_to_len_prod l)
         (ser_non_inter : seq_cond_prod l ser encode_non_inter)
         (tl_c : seq_cond_tl_prod l ser par tl format_to_len_correct),
    format_to_len_correct_dep (seq_serialize_latter l ser)
      (fun bl pf_bl flg => seq_parse_latter l par bl pf_bl)
      (seq_to_len_latter l tl)
      (seq_type_to_bit_list l).
Proof.
  induction l.
  - intros. simpl in *.
    unfold seq_to_len_latter.  simpl. split.
    + apply unit_format_correct.
    + intros. exists 0. auto. 
  - intros.  split.
    + destruct a eqn:Ea; destruct ser, tl;
        unfold format_to_len_correct; simpl; intros. 
      * intros. unfold append_serialize in H.  repeat destruct_enc.
        inversion H. subst. clear H.
        simpl. unfold add_opt.
        simpl in tl_c. 
        eassert (G1 := proj1 (proj1 tl_c) _ _ _ _ _ _ E).
        simpl in G1. destruct b.  simpl in *.
        rewrite G1.

        eassert (G2 := proj1 (IHl _ _ _ (proj2 ser_non_inter)
                         (proj2 tl_c)) _ _ _ _ _ _  E0).
        rewrite G2.
        f_equal.
        
        (* non-inter *)
        eassert (N1 :=  (proj1 ser_non_inter) _ _ _ _ _ _ E).  
        eassert (N2 := seq_latter_non_inter _ _  (proj2 ser_non_inter) _ _ _ _ _ _ E0).
        split_and. unfold BProp.le_pos in *.
        lia.
      * destruct b. simpl in s0.  destruct s0 eqn:Es;
          unfold append_serialize, opt_serialize in H;  simpl in *;
          repeat destruct_enc;
          inversion H;  subst; clear H. 
        (* Same proof as before *)
        { eassert (G1 := proj1 (proj1 tl_c) _ _ _ _ _ _ E).
          eassert (G2 := proj1 (IHl _ _ _ (proj2 ser_non_inter)
                           (proj2 tl_c)) _ _ _ _ _ _  E0).
          unfold add_opt.
          rewrite G1, G2. f_equal.
        
          eassert (N1 :=  (proj1 ser_non_inter) _ _ _ _ _ _ E).  
          eassert (N2 := seq_latter_non_inter _ _  (proj2 ser_non_inter) _ _ _ _ _ _ E0).
          split_and. unfold BProp.le_pos in *.
          lia.
        } 
        
        { destruct t.
          destruct (put_unit_pos_no_change _ _ _ _ E). subst. 
        

          eassert (G2 := proj1 (IHl _ _ _ (proj2 ser_non_inter)
                                  (proj2 tl_c)) _ _ _ _ _ _  E0). 
          rewrite G2.  auto.
        } 
      * simpl in b.  destruct b. destruct (eqb_dec default s0) eqn:Es;
          unfold append_serialize, dft_serialize in H;  simpl in *;
          repeat destruct_enc;
          inversion H;  subst; clear H.
        {  destruct (eqb_dec s0 s0) eqn:Es0.
           { unfold put_fixed_item in E.  destruct_enc. inversion E.
             subst.  destruct t. 
             destruct (put_unit_pos_no_change _ _ _ _ E1). subst. 
             eassert (G2 := proj1 (IHl _ _ _ (proj2 ser_non_inter)
                                     (proj2 tl_c)) _ _ _ _ _ _  E0).
             rewrite G2. auto.  }
           { (* Absurd case *)
             assert (s0 = s0). { reflexivity. }
             destruct (n H). } 
        }
        { destruct_match_dec_new. 
          eassert (G1 := proj1 (proj1 tl_c) _ _ _ _ _ _ E).
          eassert (G2 := proj1 (IHl _ _ _ (proj2 ser_non_inter)
                                  (proj2 tl_c)) _ _ _ _ _ _  E0). 
          
          unfold add_opt.
          rewrite G1, G2. f_equal.
          
          eassert (N1 :=  (proj1 ser_non_inter) _ _ _ _ _ _ E).  
          eassert (N2 := seq_latter_non_inter _ _  (proj2 ser_non_inter) _ _ _ _ _ _ E0).
          split_and. unfold BProp.le_pos in *.
          lia.
        }
    + intros.
      destruct a; destruct tl; simpl in H. unfold append_parse, bind_parse, return_parse in H; repeat destruct_enc.
      * inversion H; subst; clear H. simpl.
        eassert (G1 := proj2 (proj1 tl_c) _ _ _ _ _ _ E).
        eassert (G2 := proj2 (IHl _ _ _ (proj2 ser_non_inter)
                                (proj2 tl_c)) _ _ _ _ _ _ _ _ E0).
        destruct_ex. simpl in *.  rewrite H0, H. 
        simpl. eauto. 
      * destruct b. destruct s eqn:Es; unfold append_parse, opt_parse, bind_parse, return_parse in *; repeat destruct_enc. 
        {  inversion H. subst. clear H.
           inversion E. subst. clear E. 
           eassert (G1 := proj2 (proj1 tl_c) _ _ _ _ _ _ E1).
           eassert (G2 := proj2 (IHl _ _ _ (proj2 ser_non_inter)
                                   (proj2 tl_c)) _ _ _ _ _ _ _ _ E0).
           destruct_ex. simpl in *. rewrite H0, H. simpl. eauto.
        }
        { simpl. inversion H. subst.
          eassert (G2 := proj2 (IHl _ _ _ (proj2 ser_non_inter)
                                  (proj2 tl_c)) _ _ _ _ _ _ _ _ E).
          destruct G2. exists x. simpl in H0.  rewrite H0. auto.   }
      * destruct b. generalize dependent pf_a. simpl.
        unfold append_parse, dft_parse, bind_parse, return_parse.
        destruct (eqb_dec default s).
        { intros. destruct_enc. inversion H. 
          
          generalize dependent s0.
          rewrite H2. intros.
          
          assert (G2 := proj2 (IHl _ _ _ (proj2 ser_non_inter)
                                 (proj2 tl_c)) l1 bf pos p s0
                          (eq_add_S (length (seq_type_to_bit_list l l1)) (bit_list_len l) pf_a) f f E).

          destruct G2.  exists x0. simpl. simpl in H0. rewrite H0. auto. 
        }
        { intros.
          repeat destruct_enc. destruct (eqb_dec default x1).
          { unfold fail_parse in E. inversion E. } 
          inversion E. 
          inversion H.  subst. clear H. clear E.
          
          destruct par. simpl in *.

          eassert (G1 := proj2 (proj1 tl_c) _ _ _ _ _ _ E1).
           eassert (G2 := proj2 (IHl _ _ _ (proj2 ser_non_inter)
                                   (proj2 tl_c)) _ _ _ _ _ _ _ _ E0).

           destruct_ex. rewrite H0, H. simpl. eauto. 
        }
        Unshelve. apply SameVer.
        apply SameVer.
        apply SameVer.
        apply SameVer.
Qed.

Lemma list_to_len_1 : forall n bl,
    length bl = n -> 
    ListFormat.list_to_len (fun _ : bool => Some 1) n bl = Some n.
Proof.
  intro n. induction n; intros. 
  - simpl.  destruct bl; auto.
    simpl in H. inversion H.
  - simpl.  destruct bl; simpl in H; inversion H. 
    subst.  rewrite IHn; auto.
Qed.

Lemma seq_to_len_correct  (l : list seq_elem) :
  forall (ser : seq_serial_prod l)
         (par : seq_parse_prod l)
         (tl : seq_to_len_prod l)
         (ser_non_inter : seq_cond_prod l ser encode_non_inter)
         (tl_c : seq_cond_tl_prod l ser par tl format_to_len_correct),
    format_to_len_correct _ _ (seq_serialize l ser) (seq_parse l par)
      (seq_to_len l tl).
Proof.
  intros.
  split. 
  - unfold seq_serialize, prepend_serialize, append_serialize, fst, seq_to_len, add_opt.

    unfold format_to_len_correct in tl_c. intros.
    
    repeat destruct_enc. inversion E. inversion H.
    subst. clear E. clear H.

    eassert (G := proj1 (seq_to_len_latter_correct _ _ _ _ ser_non_inter tl_c) _ _ _ _ _ _ E1).
    simpl in G. rewrite G.
    
    eassert (G1 := proj1 (fmt_len_c (T_Correct _ _ ((BoolList.list_bool_format  (bit_list_len l)))))
                     _ _ _ _ _ _ E0).  simpl in G1. 
    
    rewrite list_to_len_1 in G1; auto.  inversion G1. 
    rewrite H0.  f_equal.

    (* Just need non-inter *)
    eassert (N1 := (fmt_enc_ni (T_Correct _ _ ((BoolList.list_bool_format (bit_list_len l))))) _ _ _ _ _ _ E0).
    
    eassert (N2 := seq_latter_non_inter _ _ ser_non_inter _
                     _ _ _ _ _ E1).
    
    split_and. unfold BProp.le_pos in *.
    lia.

  - intros. unfold seq_parse, bind_parse in H. unfold seq_to_len.
    destruct_enc.

    eassert (G1 := proj2 (fmt_len_c (T_Correct _ _ ((BoolList.list_bool_format  (bit_list_len l)))))
                     _ _ _ _ _ _ E).
    eassert (K := seq_type_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ H).
    subst. 
    eassert (G2 := proj2 (seq_to_len_latter_correct _ _ _ _ ser_non_inter tl_c) a bf p pos' pf
                    e flg flg H).
    destruct_ex.
    
    simpl in H1.  rewrite list_to_len_1 in H1; auto.
    rewrite H1.  rewrite H0.  simpl. eauto. 
Qed.

Opaque Nat.pow.

Lemma match_eq {A} (a : option A) :
  (match a with
   | Some a' => Some a'
   | None => None
   end) = a.
  destruct a; auto.
Qed.

Lemma seq_latter_inj_diff
  (l : list seq_elem) :
  forall (ser : seq_serial_prod l)
         (par : seq_parse_prod l)
         (tl : seq_to_len_prod l)
         (ser_non_inter : seq_cond_prod l ser encode_non_inter)
         (gl_crt : seq_cond_tl_prod l ser par tl format_to_len_correct)
         (prod_inj : seq_cond_tl_prod l ser par tl format_correct_inj_diff),
    format_correct_inj_diff_dep (seq_serialize_latter l ser)
      (fun (a : list bool)
         (pf_a : length a = bit_list_len l) (_ : Flg) =>
         seq_parse_latter l par a pf_a)
      (seq_to_len_latter l tl)
      (seq_type_to_bit_list l).
Proof.
  induction l;  unfold format_correct_inj_diff_dep; intros. 
  - simpl. simpl in H. 
    eapply (unit_format_inj_diff).
    apply H. 
  - destruct a.
    + destruct ser, par, tl. simpl in *. destruct b. 
      eassert (K := IHl _ _ _  (proj2 ser_non_inter) (proj2 gl_crt)
                      (proj2 prod_inj)).
      eassert (G := append_inj_diff_dep _ _ _ _ _ _ _ (proj1 ser_non_inter)
                      (proj1 gl_crt)
                      (seq_to_len_latter_correct   _ _ _ _ (proj2 ser_non_inter) (proj2 gl_crt))
                      (proj1 prod_inj) K).
      eapply G. 
      * apply flg.
      * simpl.  rewrite H.  encode_eq.

    + destruct b. simpl in s.  destruct s eqn:Es.
      * simpl in *. destruct pf. 

        assert (append_parse (fst par)
                  (seq_parse_latter l (snd par) (seq_type_to_bit_list l l0)
                     (eq_add_S (length (seq_type_to_bit_list l l0))
                        (bit_list_len l) pf_a)) bf pos =
                  Some (exist _ (a, l0) (conj p s0), pos', flg')).
        { unfold append_parse, bind_parse, return_parse in *.
          repeat destruct_enc. inversion H. inversion E. subst. 
          destruct par. simpl in *.
          
          subst. rewrite E0. inversion H5. subst. decode_eq. }

        eassert (G :=  append_inj_diff_dep _ _ _ _ _ _ _ (proj1 ser_non_inter)
                         (proj1 gl_crt)
                         (seq_to_len_latter_correct   _ _ _ _ (proj2 ser_non_inter) (proj2 gl_crt))
                         (proj1 prod_inj)
                         (IHl _ _ _  (proj2 ser_non_inter) (proj2 gl_crt)
                            (proj2 prod_inj))
                         (a, l0)  bf pos pos' _ _ _ _ H0).
                        
        apply G.
      * simpl in H. unfold append_parse, return_parse, bind_parse in H.
        simpl in H. destruct_enc. inversion H. subst.
        
        eassert ( G := IHl _ _  _  (proj2 ser_non_inter) (proj2 gl_crt)
                         (proj2 prod_inj) _ _ _ _ _ _ _ _  E).
        destruct G.  exists x. intros. apply H0 in H1.
        destruct H1.
        { left. simpl. rewrite match_eq. auto. 
        }
        right. 
        destruct_ex. split_and. 
        
        rewrite <- append_unit_eq_nothing in H2.  
        { simpl in H2. unfold append_serialize in H2. 

          simpl. unfold append_serialize. simpl in *.
          rewrite H2.  exists x0. exists x1.
          split.
          - encode_eq.
          - lia. }
        { apply seq_latter_non_inter.  simpl in ser_non_inter. apply ser_non_inter. }
    + destruct b. generalize dependent pf_a. simpl. 

      destruct (eqb_dec default s) eqn:Es.
      * simpl. intros.
        simpl in H. unfold append_parse, bind_parse, return_parse in H.
        destruct_enc. inversion H. 
        generalize dependent s0. rewrite H2, H3. 
        intros. 
        eassert (G := IHl _ _ _  (proj2 ser_non_inter) (proj2 gl_crt)
                         (proj2 prod_inj) _ _ _ _ _ _ _ _ E). 
        destruct G. exists x0. intros.  apply H0 in H5.
        destruct H5.
        { left.  auto. rewrite match_eq. auto. } 
        
        destruct_ex. split_and. right. 

        rewrite <- append_unit_eq_nothing in H6.
        { unfold append_serialize in *.
          unfold dft_serialize. simpl. rewrite Es. unfold put_fixed_item.
          simpl.  destruct_enc.
          simpl in *. rewrite E0.  destruct_enc.
          inversion H6. exists x1. exists x2. 
          split.
          - encode_eq.
          - lia. 
        }
        { apply seq_latter_non_inter. simpl in ser_non_inter. apply ser_non_inter. }
      * simpl. intros. 
        inversion pf_a. destruct pf.
        
        assert
          (append_parse (fst par)
             (seq_parse_latter l (snd par) (seq_type_to_bit_list l l0)
                (eq_add_S (length (seq_type_to_bit_list l l0))
                   (bit_list_len l) pf_a)) bf pos =
             Some (exist
                     (fun z : A * seq_type l => P (fst z) /\ seq_cond l (snd z))
                     (s, l0) (conj p s0), pos', flg')).
        { unfold append_parse, dft_parse, bind_parse, return_parse in *.
          repeat (destruct_enc).
          destruct (eqb_dec default x1).
          { unfold fail_parse in E. inversion E. } inversion E. 
          inversion H. subst. 
          destruct par. simpl in *. 
          rewrite E0. clear H. decode_eq. }

        eassert (G := append_inj_diff_dep _ _ _ _ _ _ _ (proj1 ser_non_inter)
                         (proj1 gl_crt)
                         (seq_to_len_latter_correct   _ _ _ _ (proj2 ser_non_inter) (proj2 gl_crt))
                         (proj1 prod_inj)
                         (IHl _ _ _  (proj2 ser_non_inter) (proj2 gl_crt)
                            (proj2 prod_inj))
                        (s, l0) bf pos pos' _ _ _ _ H0). 

        simpl in G.
        unfold append_serialize, dft_serialize in *. simpl.  rewrite Es.
        auto.
        Unshelve.
        apply SameVer. apply SameVer. apply SameVer. apply SameVer.
Qed.

Lemma seq_inj_diff  (l : list seq_elem) :
  forall (ser : seq_serial_prod l)
    (par : seq_parse_prod l)
    (tl : seq_to_len_prod l)
    (ser_non_inter : seq_cond_prod l ser encode_non_inter)
    (gl_crt : seq_cond_tl_prod l ser par tl format_to_len_correct)
         (prod_inj : seq_cond_tl_prod l ser par tl
                       format_correct_inj_diff),
    format_correct_inj_diff _ _
      (seq_serialize l ser)
      (seq_parse l par)
      (seq_to_len l tl).
Proof.
  intros. unfold format_correct_inj_diff.  intros.
  unfold seq_parse, bind_parse in H.
  destruct_enc.
  unfold seq_serialize, prepend_serialize. 

  assert (G := T_Correct _ _ (BoolList.list_bool_format (bit_list_len l))).
  assert (BI := fmt_inj_diff G). 
  eassert (G' := BI _ _ _ _ _ _ E).
  destruct G'.  
  unfold append_serialize, fst. 

  eassert (Ex :=  seq_type_to_bit_list_valid_inj l par _ _ _ _ _ _ _ _ H).
  subst. 
  
  eassert (G1 := seq_latter_inj_diff l ser par tl ser_non_inter gl_crt prod_inj 
                   a bf p pos' _ _ _ flg H). 

  destruct G1. 
  exists (x0 + x). intros. 
  assert (L1 : BA.to_nat pos0 +  x0 <= BA.len bf0). { lia. } 
  apply H0 in L1.
  unfold seq_to_len.
  
  eassert (K1 := proj2 (fmt_len_c G) _ _ _ _ _ _ E).
  eassert (K2 := proj2 (seq_to_len_latter_correct  _ _ _ _ ser_non_inter gl_crt)
                   _ _ _ _ _ _ _ _ H).
  
  destruct_ex. split_and. 
  simpl in H4. rewrite list_to_len_1 in H4. 
  rewrite H4, H3. simpl.

  destruct L1.
  { left. simpl in H5. rewrite list_to_len_1 in H5. inversion H4.  subst.
    assert (bit_list_len l <= bit_list_len l + x1). { lia. }
    apply get_byte_len_mono in H6. lia.  auto.  }
  
  destruct_ex. split_and.
  eassert (LE := same_len_after_enc _ (fmt_enc_ni G) H6).
  assert (L2 : BA.to_nat x4 + x <= BA.len x3). { lia. }
  apply H1 in L2.

  destruct L2.
  { rewrite H3 in H5. left. assert (x1 <= x2 + x1). { lia. }
    apply get_byte_len_mono in H8. lia. } 

  destruct_ex. split_and.  right.
  unfold BoolList.bool_list_serialize.  rewrite H6.
  rewrite H8.  

  exists x5. exists x6. split; try encode_eq. lia. auto. 
  Unshelve. apply SameVer. apply SameVer. 
Qed.

Definition fmt_to_seq_prod (l : list seq_elem) (fmts : seq_format_prod l)
  (X : forall A : Set, (A -> Prop) -> Type)
  (T_X : forall (T : Set) (T_Cond : T -> Prop),
      T_Format T T_Cond -> X T T_Cond)
  (X_unit : X unit (fun _ : unit => True))
      : list_to_prod l (fun t => X (seq_elem_to_set t) (seq_elem_to_cond t))  (Nor unit (fun _ => True)).
  induction l.
  - apply X_unit.
  - destruct fmts.
    apply (T_X _ _ s, IHl l0).
Defined.

Definition fmt_to_seq_prod_no_cond (l : list seq_elem) (fmts : seq_format_prod l)
  (X : forall A : Set, Type)
  (T_X : forall (T : Set) (T_Cond : T -> Prop), T_Format T T_Cond -> X T)
  (X_unit : X unit)
  : list_to_prod l (fun t => X (seq_elem_to_set t)) (Nor unit (fun _ => True)).
  induction l.
  - apply X_unit.
  - destruct fmts.
    apply (T_X _ _ s, IHl l0). 
Defined.

Lemma seq_enc_non_inter
  (l : list seq_elem) (ser : seq_serial_prod l)
  (non_inter_prod : seq_cond_prod l ser encode_non_inter) :
  encode_non_inter _ _  (seq_serialize l ser).
Proof.
  unfold encode_non_inter.
  intros. unfold seq_serialize in *.
  assert (Tb := 
              (T_Correct _ _
                    (BoolList.list_bool_format (bit_list_len l)))).
    

  eapply prepend_non_inter.
  - eapply (fmt_enc_ni).
    apply Tb.
  - apply seq_latter_non_inter.
    apply non_inter_prod.
  - apply H.
Qed. 
    
Lemma seq_enc_consist:
  forall l ser
    (en_consist_prod : seq_cond_prod l ser encode_consistent)
    (non_inter_prod : seq_cond_prod l ser encode_non_inter), 
    encode_consistent _ _ (seq_serialize l ser).
Proof.
  intros. unfold encode_consistent.
  unfold seq_serialize.
  intros.
  assert (Eb := fmt_enc_consist
                 (T_Correct _ _
                    (BoolList.list_bool_format (bit_list_len l)))).

  eapply prepend_consistent.
  - apply Eb.
  - apply seq_latter_encode_consist.
    + apply non_inter_prod.
    + apply en_consist_prod.
  - apply seq_latter_non_inter.
    apply non_inter_prod.

  - apply H.
  - apply H0.
Qed.

Lemma seq_dec_consist : 
  forall l (par : seq_parse_prod l)
(*  (bl : list bool)  (pf_bl : length bl = bit_list_len l) *)
  (decode_consist_prod : seq_cond_de_prod l par decode_consistent),
  decode_consistent _ _ (seq_parse l par).
Proof.
  intros. unfold seq_parse.
  eapply bind_parse_consist.
  -   assert (Eb := fmt_dec_consist
                 (T_Correct _ _
                    (BoolList.list_bool_format (bit_list_len l)))).
      apply Eb.
  - intros.
    apply seq_latter_decode_consist.
    apply decode_consist_prod.
Qed. 
  
Lemma seq_fmt_enc_ni_prod (l : list seq_elem) (fmts : seq_format_prod l) :
  seq_cond_prod l (fmt_to_seq_prod l fmts Serialize T_Serial put_unit) encode_non_inter.
Proof.
  generalize dependent fmts. induction l; intros fmts.
  - exact I.
  - destruct a; destruct fmts as [s fmts']; simpl; split.
    all: first [ exact (fmt_enc_ni (T_Correct _ _ s)) | apply IHl ].
Qed.

Lemma seq_fmt_enc_consist_prod (l : list seq_elem) (fmts : seq_format_prod l) :
  seq_cond_prod l (fmt_to_seq_prod l fmts Serialize T_Serial put_unit) encode_consistent.
Proof.
  generalize dependent fmts. induction l; intros fmts.
  - exact I.
  - destruct a; destruct fmts as [s fmts']; simpl; split.
    all: first [ exact (fmt_enc_consist (T_Correct _ _ s)) | apply IHl ].
Qed.

Lemma seq_fmt_dec_consist_prod (l : list seq_elem) (fmts : seq_format_prod l) :
  seq_cond_de_prod l (fmt_to_seq_prod l fmts Parse T_Parse read_unit) decode_consistent.
Proof.
  generalize dependent fmts. induction l; intros fmts.
  - exact I.
  - destruct a; destruct fmts as [s fmts']; simpl; split.
    all: first [ exact (fmt_dec_consist (T_Correct _ _ s)) | apply IHl ].
Qed.

Lemma seq_fmt_surj_prod (l : list seq_elem) (fmts : seq_format_prod l) :
  seq_cond_both_prod l
    (fmt_to_seq_prod l fmts Serialize T_Serial put_unit)
    (fmt_to_seq_prod l fmts Parse T_Parse read_unit)
    format_correct_surj.
Proof.
  generalize dependent fmts. induction l; intros fmts.
  - exact I.
  - destruct a; destruct fmts as [s fmts']; simpl; split.
    all: first [ exact (fmt_surj (T_Correct _ _ s)) | apply IHl ].
Qed.

Lemma seq_fmt_inj_same_prod (l : list seq_elem) (fmts : seq_format_prod l) :
  seq_cond_both_prod l
    (fmt_to_seq_prod l fmts Serialize T_Serial put_unit)
    (fmt_to_seq_prod l fmts Parse T_Parse read_unit)
    format_correct_inj_same.
Proof.
  generalize dependent fmts. induction l; intros fmts.
  - exact I.
  - destruct a; destruct fmts as [s fmts']; simpl; split.
    all: first [ exact (fmt_inj_same (T_Correct _ _ s)) | apply IHl ].
Qed.

Lemma seq_fmt_len_correct_prod (l : list seq_elem) (fmts : seq_format_prod l) :
  seq_cond_tl_prod l
    (fmt_to_seq_prod l fmts Serialize T_Serial put_unit)
    (fmt_to_seq_prod l fmts Parse T_Parse read_unit)
    (fmt_to_seq_prod_no_cond l fmts (fun X => X -> option nat) T_to_len (fun _ => Some 0))
    format_to_len_correct.
Proof.
  generalize dependent fmts. induction l; intros fmts.
  - exact I.
  - destruct a; destruct fmts as [s fmts']; simpl; split.
    all: first [ exact (fmt_len_c (T_Correct _ _ s)) | apply IHl ].
Qed.

Lemma seq_fmt_inj_diff_prod (l : list seq_elem) (fmts : seq_format_prod l) :
  seq_cond_tl_prod l
    (fmt_to_seq_prod l fmts Serialize T_Serial put_unit)
    (fmt_to_seq_prod l fmts Parse T_Parse read_unit)
    (fmt_to_seq_prod_no_cond l fmts (fun X => X -> option nat) T_to_len (fun _ => Some 0))
    format_correct_inj_diff.
Proof.
  generalize dependent fmts. induction l; intros fmts.
  - exact I.
  - destruct a; destruct fmts as [s fmts']; simpl; split.
    all: first [ exact (fmt_inj_diff (T_Correct _ _ s)) | apply IHl ].
Qed.

Lemma seq_format_correct :
  forall (l : list seq_elem)
         (fmts : seq_format_prod l),
    format_correct
      (seq_serialize l (fmt_to_seq_prod l fmts Serialize T_Serial put_unit))
      (seq_parse l (fmt_to_seq_prod l fmts Parse T_Parse read_unit))
      (seq_to_len l (fmt_to_seq_prod_no_cond l fmts (fun X => X -> option nat)
                       T_to_len (fun _ => Some 0))).
Proof.
  intros. unfold format_correct.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - apply seq_enc_consist.
    + apply seq_fmt_enc_consist_prod.
    + apply seq_fmt_enc_ni_prod.
  - apply seq_dec_consist.
    apply seq_fmt_dec_consist_prod.
  - apply seq_enc_non_inter.
    apply seq_fmt_enc_ni_prod.
  - apply seq_surj.
    + apply seq_fmt_enc_ni_prod.
    + apply seq_fmt_dec_consist_prod.
    + apply seq_fmt_surj_prod.
  - apply seq_inj_same.
    + apply seq_fmt_enc_ni_prod.
    + apply seq_fmt_inj_same_prod.
  - apply seq_inj_diff.
    + apply seq_fmt_enc_ni_prod.
    + apply seq_fmt_len_correct_prod.
    + apply seq_fmt_inj_diff_prod.
  - apply seq_to_len_correct.
    + apply seq_fmt_enc_ni_prod.
    + apply seq_fmt_len_correct_prod.
Qed.
