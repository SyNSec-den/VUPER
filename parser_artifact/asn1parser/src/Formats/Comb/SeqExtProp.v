Require Import
  ASN1Parser.Array.BitRep
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombProp
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Array.ByteBuffer
  ASN1Parser.Array.ByteBufferProp.

Require Import
  ASN1Parser.Formats.Term.Unit
  ASN1Parser.Formats.Term.BoolList
  ASN1Parser.Formats.Comb.SeqProd 
  ASN1Parser.Formats.Comb.Seq
  ASN1Parser.Formats.Comb.HelperComb
  ASN1Parser.Formats.Comb.HelperProp
  ASN1Parser.Formats.Comb.SeqExt
  ASN1Parser.Formats.Comb.OpenType
  ASN1Parser.Formats.Comb.OpenTypeProp.

Require Import ASN1Parser.tact
  Lia
  Coq.Logic.ProofIrrelevance.

Lemma  ext_serialize_latter_non_inter  (ext : list typ)
  (ser : get_serial_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  : encode_non_inter (seq_ext_type ext) (seq_ext_cond ext)
      (ext_serialize_latter ext ser len_prod).
Proof.
  induction ext.
  - simpl.  unfold seq_ext_type. simpl.
    apply put_unit_non_inter.
  - simpl.
    destruct a, ser, ser_non_inter.
    apply append_non_inter.
    + apply opt_non_inter.
      apply open_type_non_inter.
      auto. 
    + apply IHext. 
      auto.
Qed.

Lemma ext_serialize_non_inter_partial (ext : list typ)
  (ser : get_serial_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  :  encode_non_inter _ _ 
       (prepend_serialize (fun z : seq_ext_type ext => ext_to_bit_list ext z)
          (bool_list_serialize (length2 ext))
          (ext_serialize_latter ext ser len_prod)).
Proof.
  apply prepend_non_inter. 
  - eapply fmt_enc_ni.
    apply T_Correct. 
  - apply ext_serialize_latter_non_inter. auto.
Qed.

Lemma ext_serialize_non_inter (ext : list typ)
  (ser : get_serial_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  : encode_non_inter _ _  (ext_serialize ext ser len_prod).
Proof.
  unfold ext_serialize.
  apply prepend_non_inter.
  - eapply fmt_enc_ni. apply T_Correct. 
  - apply ext_serialize_non_inter_partial; auto. 
Qed.

Lemma ext_serialize_latter_consist (ext : list typ)
  (ser : get_serial_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (ser_consist : get_cond_prod ext ser encode_consistent)
  : encode_consistent (seq_ext_type ext) (seq_ext_cond ext)
     (ext_serialize_latter ext ser len_prod).
Proof.
  induction ext.
  - simpl. unfold seq_ext_type. simpl.
    apply put_unit_consist.
  - simpl. destruct a, ser, ser_non_inter, ser_consist.
    apply append_encode_consist.
    + apply opt_encode_consist.
      apply open_type_encode_consist; auto.
    + apply IHext; auto.
    + apply ext_serialize_latter_non_inter. auto.
Qed.

Lemma ext_serialize_consistent (ext : list typ)
  (ser : get_serial_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (ser_consist : get_cond_prod ext ser encode_consistent)
  : encode_consistent _ _  (ext_serialize ext ser len_prod).
Proof.
  unfold ext_serialize.
  apply prepend_consistent.
  - eapply fmt_enc_consist. apply T_Correct. 
  - apply prepend_consistent.
    + eapply fmt_enc_consist. apply T_Correct. 
    + apply ext_serialize_latter_consist; auto.
    + apply ext_serialize_latter_non_inter. auto.
  - apply  ext_serialize_non_inter_partial. auto. 
Qed.

Lemma to_parse_none_consist (ext' : list typ)
  : decode_consistent _ _  (to_parse_none ext') .
Proof.
  induction ext'.
  - simpl. unfold seq_ext_type. simpl. unfold to_parse_none. simpl.
    apply bind_parse_consist.
    + apply read_unit_consist.
    + intros. apply return_parse_consist. 
  - simpl. unfold seq_ext_type, to_parse_none. simpl. apply bind_parse_consist.
    + apply read_unit_consist.
    + intros. 
      apply return_parse_consist.
Qed.

Lemma ext_parse_le_consist (ext : list typ) :
  forall (par : get_parse_prod ext)
         (par_consist : get_cond_de_prod ext par decode_consistent)
         (bl : list bool) pf,
    decode_consistent (seq_ext_type ext) (seq_ext_cond ext)
      (to_parse_latter_le ext par bl pf).
Proof.
  induction ext; intros. 
  - simpl. apply read_unit_consist. 
  - destruct bl.
    + simpl. unfold to_parse_none. apply bind_parse_consist.
      * apply read_unit_consist. 
      * intros. apply return_parse_consist.
    + simpl. destruct a, par, par_consist. 
      apply append_parse_consist.
      * apply opt_decode_consist, open_type_decode_consist.
        auto.
      * simpl. apply IHext. auto.
Qed.

Lemma ext_parse_eq_consist (ext : list typ) :
  forall (par : get_parse_prod ext)
         (par_consist : get_cond_de_prod ext par decode_consistent)
         (bl : list bool) pf,
    decode_consistent (seq_ext_type ext) (seq_ext_cond ext)
      (to_parse_latter_eq ext par bl pf).
Proof.
  induction ext; intros.
  - simpl.  apply read_unit_consist.
  - destruct bl.
    + simpl in pf. inversion pf.
    + simpl.  destruct a, par, par_consist. 
      apply append_parse_consist.
      * apply opt_decode_consist, open_type_decode_consist.
        auto.
      * apply IHext. auto.
Qed.

Lemma skip_n_byte_decode_consist :
  forall n, decode_consistent _ _ (skip_n_bytes n).
Proof.
  intro n. induction n.
  - simpl. apply read_unit_consist.
  - simpl. apply bind_parse_consist; auto.
    intros. unfold skip_1_byte.
    apply bind_parse_consist; auto.
    + eapply fmt_dec_consist. apply BPP.basic_n_bit_format_correct. unfold INT_MAX_LEN. lia. 
    + intros.  apply read_unit_consist.
Qed.

Lemma open_type_skip_decode_consist : 
  decode_consistent _ _ (open_type_skip_parse).
Proof.
  unfold open_type_skip_parse. 
  apply bind_parse_consist.
  - eapply fmt_dec_consist. apply T_Correct. 
  - intros.  apply bind_parse_consist.
    + apply skip_n_byte_decode_consist.
    + intros.  apply read_unit_consist. 
Qed.

Lemma to_parse_skip_decode_consist : 
  forall n bl, decode_consistent _ _ (to_parse_skip n bl).
Proof.
  intro.  induction n.
  - simpl. intros.   apply read_unit_consist.
  - simpl. intros. destruct bl eqn:eb.
    + unfold decode_consistent. intros. unfold fail_parse in H.
      inversion H.
    + destruct b eqn:Eb.
      * apply bind_parse_consist.
        { apply open_type_skip_decode_consist. }
        { intros. apply IHn. }
      * apply IHn. 
Qed.
  
Lemma ext_parse_ge_consist (ext : list typ) :
  forall (par : get_parse_prod ext)
         (par_consist : get_cond_de_prod ext par decode_consistent)
         (bl : list bool) pf,
    decode_consistent (seq_ext_type ext) (seq_ext_cond ext)
      (to_parse_latter_ge ext par bl pf).
Proof.
  intros. unfold to_parse_latter_ge.
  apply bind_parse_consist.
  - apply ext_parse_eq_consist. auto.
  - intros. apply bind_parse_consist.
    + apply to_parse_skip_decode_consist.
    + intros. apply return_parse_consist.
Qed.      

Lemma ext_parse_consist
  (ext : list typ)
  (par : get_parse_prod ext)
  (par_consist : get_cond_de_prod ext par decode_consistent)
  : decode_consistent _ _ (ext_parse ext par).
Proof.
  unfold ext_parse.
  apply bind_parse_consist.
  - eapply fmt_dec_consist. apply T_Correct. 
  - intros. apply bind_parse_consist.
    + eapply fmt_dec_consist. apply T_Correct. 
    + intros.
      destruct (lt_eq_lt_dec_new (length a0) (length2 ext)).
      { apply ext_parse_le_consist. auto. }
      { apply ext_parse_eq_consist. auto. }
      { apply ext_parse_ge_consist. auto. }
Qed.

(*Definition get_cond_len_prod (l : list typ)
  (ser : get_serial_prod l)
  (len_prod : get_to_len_prod l)
  : Prop.
  induction l.
  - apply True.
  - apply (get_len_correct (fst ser) (fst len_prod) /\ IHl (snd ser) (snd len_prod)).
Defined. *)

Lemma length_eq_length2 {A : Type} :
  forall l : list A, length2 l = length l.
Proof.
  induction l; simpl; auto.
Qed.

Lemma seq_ext_latter_surj
  (ext : list typ)
  (ser : get_serial_prod ext)
  (par : get_parse_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (len_correct : get_cond_tl_prod ext ser par len_prod format_to_len_correct)
  (par_consist : get_cond_de_prod ext par decode_consistent)
  (prod_surj : get_cond_both_prod ext ser par format_correct_surj)
  : format_correct_surj_dep (ext_serialize_latter ext ser len_prod)
      (fun (a : list bool) (pf_a : length a = length2 ext) (_ : Flg) =>
         to_parse_latter_eq ext par a pf_a)
      (fun z : seq_ext_type ext => ext_to_bit_list ext z).
Proof.
  induction ext.
  - simpl. unfold format_correct_surj_dep.
    intros. eapply unit_format_surj.
    apply H.
  - destruct a. simpl in *. 
    unfold format_correct_surj_dep.
    intros.
    eassert (G1 := open_type_surj _ _ _ (proj1 prod_surj)
                     (proj1 len_correct)
                     (proj1 ser_non_inter)
                     (proj1 par_consist)).
    eassert (G2 := IHext _ _ _ (proj2 ser_non_inter)
                     (proj2 len_correct)
                     (proj2 par_consist)
                     (proj2 prod_surj)).
    
    destruct b. destruct e eqn:E1.
    + (* Here, since we have a layer of OpenType  *)
      eassert (G :=
                 append_surj_dep _
                   (OpenType.open_typ_serialize (fst ser) (fst len_prod))
                   (ext_serialize_latter ext (snd ser) (snd len_prod))
                   (OpenType.open_typ_parse (fst par))
                   _
                   (open_type_decode_consist _ (proj1 par_consist))
                   (ext_serialize_latter_non_inter _ _ _
                      (proj2 ser_non_inter))
                   G1 G2).
      clear G1. clear G2.
      (* Very similar to our proofs in Sequence, the option case *)
      simpl in pf. simpl in pf_a. inversion pf_a. 
      eassert (G' := G (t, l) bf bf' pos pos' pf H1 H). clear G. 
      simpl in G'. unfold append_parse, bind_parse, return_parse in G'.
      repeat (destruct_enc). inversion G'.
      destruct (flg_add_to_same _ _ H5). subst.
      unfold opt_parse, append_parse, bind_parse, return_parse. simpl. 
      rewrite E.  
      
      assert ( (eq_add_S (length (ext_to_bit_list ext l)) (length2 ext) pf_a) = H1).
      { apply proof_irrelevance. }
      subst. rewrite E0. decode_eq.

    + clear G1.
      unfold append_serialize, opt_serialize in H. simpl in H.
      repeat destruct_enc.
      destruct t. apply put_unit_pos_no_change in E. 
      split_and; subst. 

      simpl in pf_a. inversion pf_a. 
      eassert (G := G2 _ _ _ _ _ _ H1 E0).
      simpl in G. inversion H. subst. 
      simpl. unfold append_parse, bind_parse, return_parse.

      assert ( (eq_add_S (length (ext_to_bit_list ext l)) (length2 ext) pf_a) = H1).
      { apply proof_irrelevance. }
      subst. rewrite G. decode_eq.
Qed.

Lemma seq_ext_surj
  (ext : list typ)
  (ser : get_serial_prod ext)
  (par : get_parse_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (len_correct : get_cond_tl_prod ext ser par len_prod format_to_len_correct)
  (par_consist : get_cond_de_prod ext par decode_consistent)
  (prod_surj : get_cond_both_prod ext ser par format_correct_surj)
  : format_correct_surj _ _ (ext_serialize ext ser len_prod) (ext_parse ext par).
Proof.
  unfold ext_serialize, ext_parse, format_correct_surj. 
  apply prepend_surj_dep. 
  - eapply fmt_dec_consist. apply T_Correct.
  - apply  ext_serialize_non_inter_partial; auto.
  - eapply fmt_surj.  apply T_Correct. 
  - (* Here, we can observe that surj_dep is essentially
       equivalent to simple surjection. 
     *)
    
    unfold format_correct_surj_dep. intros.
    eapply prepend_surj_dep.
    + eapply fmt_dec_consist. apply T_Correct.
    + apply  ext_serialize_latter_non_inter.
      apply ser_non_inter.
    + eapply fmt_surj.  apply T_Correct. 
    + shelve.
    + apply H.
      Unshelve. 

      unfold format_correct_surj_dep. intros. 
      
      assert (lt_eq_lt_dec_new (length (ext_to_bit_list (ext) b0))
                (length2 (ext)) = middle3 _ _ _ pf_a0).
      { rewrite pf_a0. unfold lt_eq_lt_dec_new. 
        
        destruct (Compare_dec.le_lt_dec (length2 (ext)) (length2 (ext))).
        - destruct ( lt_le_eq_dec (length2 (ext)) (length2 (ext))).
          + lia.
          + f_equal. apply proof_irrelevance.
        - lia.  }

      rewrite H1.
      
      eapply seq_ext_latter_surj; eauto.
Qed.

Lemma to_parse_le_Diff
  (ext : list typ)
  (par : get_parse_prod ext)
  : forall bl pf_bl x pf_x bf pos pos' flg, 
    to_parse_latter_le ext par bl pf_bl bf pos =
      Some (exist _ x pf_x , pos', flg) ->
  flg = DiffVer.
Proof.
  induction ext; intros. 
  - (* This case is impossible, because length bl < length ext *)
    simpl in pf_bl. lia.
  - destruct bl.
    + simpl in H. 
      unfold to_parse_none, bind_parse, return_parse in H.
      destruct_enc. inversion H. subst. auto.
    + simpl in H. unfold append_parse, bind_parse, return_parse in H.
      repeat destruct_enc. inversion H. subst.

      apply IHext in E0. subst.
      destruct f; simpl; auto.
Qed.

Lemma to_parse_ge_Diff
  (ext : list typ)
  (par : get_parse_prod ext)
  : forall bl pf_bl x pf_x bf pos pos' flg, 
    to_parse_latter_ge ext par bl pf_bl bf pos =
      Some (exist _ x pf_x , pos', flg) ->
    flg = DiffVer.
Proof.
  intros. unfold to_parse_latter_ge, bind_parse, return_parse in H.
  repeat destruct_enc. inversion H. auto.
Qed.

Require Import ASN1Parser.Formats.Comb.SeqProp.

Lemma seq_ext_latter_inj_same
  (ext : list typ)
  (ser : get_serial_prod ext)
  (par : get_parse_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (len_correct : get_cond_tl_prod ext ser par len_prod format_to_len_correct)
  (prod_inj : get_cond_both_prod ext ser par format_correct_inj_same)
  : format_correct_inj_dep  (ext_serialize_latter ext ser len_prod)
      (fun (a : list bool) (pf_a : length a = length2 ext) (_ : Flg) =>
         to_parse_latter_eq ext par a pf_a)
      (fun z : seq_ext_type ext => ext_to_bit_list ext z).
Proof.
  induction ext; simpl; unfold format_correct_inj_dep; intros.
  - apply unit_format_inj. auto.  auto.  
  - destruct b, e.
    + destruct pf. simpl in o, s. 
      assert (append_parse
                (OpenType.open_typ_parse (fst par))
                (to_parse_latter_eq ext (snd par)
                   (ext_to_bit_list ext (snd (Some t, l)))
                   (eq_add_S (length (ext_to_bit_list ext (snd (Some t, l))))
                      (length2 ext) pf_a)) bf pos =
                Some
                  (exist
                     (fun g  =>
                        (typ_cond a) (fst g) /\ seq_ext_cond ext (snd g))
                     (t, l) (conj o s), pos', SameVer)).
      
      { unfold append_parse, bind_parse, return_parse in H.
        repeat destruct_enc. inversion H. destruct (flg_add_to_same _ _ H5).
        subst. clear H. clear H5. simpl.
        unfold opt_parse in E. simpl in E. 

        unfold append_parse, bind_parse, return_parse in *.
        destruct_enc.  inversion E.  subst.
        simpl in E0.  rewrite E0.  simpl. decode_eq. }

      destruct a. simpl in *. destruct ser, len_prod. 
      eassert (G :=
                 append_inj_dep _ _ _ _ _
                   (open_type_non_inter _ _  (proj1 ser_non_inter))
                   (ext_serialize_latter_non_inter ext l0 l1 (proj2 ser_non_inter))
                   (open_type_inj_same _ _ _ (proj1 prod_inj) (proj1 len_correct) (proj1 ser_non_inter))
                   (IHext _ _ _ (proj2 ser_non_inter) (proj2 len_correct) (proj2 prod_inj))

                   (t, l) bf pos pos' _ _ H1).

      apply G in H0.  clear G. 
      simpl.  unfold opt_serialize, append_serialize in *. simpl.
      apply H0.
    + unfold opt_parse, append_parse, bind_parse, return_parse in H. simpl in H.
      destruct_enc. inversion H. subst.  clear H. destruct f; inversion H4.

      destruct a. simpl in *. 
      assert (G := (IHext _ _ _ (proj2 ser_non_inter) (proj2 len_correct) (proj2 prod_inj))). 
      apply G in E.
      apply E in H0. destruct H0. 
      rewrite <- append_unit_eq_nothing in H. 
      unfold append_serialize, opt_serialize in *.  simpl.
      exists x. 
      simpl in H. split_and.
      split.
      * rewrite H0.  encode_eq.
      * auto.
      * apply ext_serialize_latter_non_inter. apply (proj2 ser_non_inter).
Qed.

    
Lemma ext_type_to_bit_list_valid_inj (ext : list typ) :
  forall
    (par : get_parse_prod ext)
    (a : seq_ext_type ext) pf x pf_l bf pos pos' flg,
    to_parse_latter_eq ext par x pf_l bf pos = Some (exist _ a pf, pos', flg) -> 
    ext_to_bit_list ext a = x. 
Proof.
  induction ext; intros. 
  - simpl.  simpl in H.
    destruct x; auto.  simpl in pf_l. inversion pf_l. 
  - simpl. destruct x.
    + simpl in pf_l. inversion pf_l.
    + simpl in H.  unfold append_parse, opt_parse, bind_parse, return_parse in H.
      destruct b eqn:Eb.
      * repeat destruct_enc. inversion H. inversion E. subst.
        f_equal. eapply IHext. apply E0.
      * destruct_enc.  inversion H.  subst. f_equal.
        eapply IHext. apply E.
Qed.

Lemma seq_ext_inj_same
  (ext : list typ)
  (ser : get_serial_prod ext)
  (par : get_parse_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (len_correct : get_cond_tl_prod ext ser par len_prod format_to_len_correct)
  (prod_inj : get_cond_both_prod ext ser par format_correct_inj_same)
  : format_correct_inj_same _ _  (ext_serialize ext ser len_prod)
      (ext_parse ext par).
Proof.
  (* Again, we only actually need to consider
     to_parse_latter_eq. 
   *)
  intros. unfold format_correct_inj_same. intros.
  unfold ext_parse, bind_parse, return_parse in H.
  
  repeat destruct_enc.

  (* Here, NTS to_parse_latter_le or ge renders DiffVer *)
  destruct ( lt_eq_lt_dec_new (length x0) (length2 ext)).
  - apply to_parse_le_Diff in H. inversion H.
  - unfold ext_serialize, prepend_serialize, append_serialize. 
    eassert (BS := bool_list_SameVer x _ _ _ _ _ _ E0).
    eassert (ES := LengthDet.small_det_SameVer _ _ _ _ _ _ E). subst. 
    unfold fst, snd.

    eassert (EE := fmt_inj_same (T_Correct _ _ LengthDet.normally_small_len_det_format)
                     _ _ _ _ _ E _ H0).
    destruct EE.  unfold LengthDet.small_enc.   destruct H1.
    rewrite <- pf0. rewrite H1.

    (* bool list *)
    eassert (BE := fmt_inj_same (T_Correct _ _ (list_bool_format (length x0)))
                     _ _ _ _ _ E0 x).
    unfold bool_list_serialize. 
    
    (* Need to show bool list is the same as x *)
    eassert (Ex := ext_type_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ H). subst.

    eassert (EE1 := same_len_after_enc _
                      (fmt_enc_ni (T_Correct _ _ LengthDet.normally_small_len_det_format)) H1).
    assert (BA.len x = BA.len bf). { lia. }
    apply BE in H3. destruct H3.  destruct H3.
    rewrite H3.

    eassert (BE1 := same_len_after_enc _
                      (fmt_enc_ni (T_Correct _ _
                                     (list_bool_format (length (ext_to_bit_list ext a))))) H3).

    assert (BA.len x0 = BA.len bf). { lia. } 
    eassert (TE1 := seq_ext_latter_inj_same _ _ _ _ ser_non_inter len_correct prod_inj
                      _ _ _ _ _ _  H x0 H5).
    destruct TE1. destruct H6.
    rewrite H6.
    exists x1.  split.
    + encode_eq.
    + eapply format_correct_inj_helper.
      { apply H2. }
      { eapply format_correct_inj_helper.
        - apply H4.
        - apply H7. 
        - eapply ext_serialize_latter_non_inter.
          eauto.  apply H6. }
      { eapply EQ.equiv_b_trans.
        - eapply (fmt_enc_ni (T_Correct _ _
                                (list_bool_format (length (ext_to_bit_list ext a))))).
          apply H3.
        - apply EQ.equiv_b_implies_valid_pair in H4.
          unfold EQ.valid_pos_pair in H4.  
          eapply EQ.equiv_b_same_pos. 
          + eapply ext_serialize_latter_non_inter. eauto.
            apply H6.
          + apply BProp.le_pos_refl.
          + unfold BProp.le_pos.  lia.
          + apply BProp.pos_zero_le_all.
      }
  - apply to_parse_ge_Diff in H. inversion H.
Qed.



Lemma seq_ext_to_len_latter_eq_correct  (ext : list typ) :
  forall (ser : get_serial_prod ext)
    (par : get_parse_prod ext)
    (tl : get_to_len_prod ext)
    (ser_non_inter : get_cond_prod ext ser encode_non_inter)
    (tl_c : get_cond_tl_prod ext ser par tl format_to_len_correct),
    format_to_len_correct_dep (ext_serialize_latter ext ser tl)
      (fun (a : list bool) (pf_a : length a = length2 ext) (_ : Flg) =>
         to_parse_latter_eq ext par a pf_a)
      (seq_ext_to_len_latter ext tl)
      (fun z : seq_ext_type ext => ext_to_bit_list ext z).
Proof. 
  induction ext.
  - intros. simpl. unfold seq_ext_to_len_latter.  simpl.
    split. 
    + eapply unit_format_correct.
    + intros. eauto.
      
  - intros. split.
    + destruct a.  simpl in *. 
      unfold format_to_len_correct. intros. destruct b. 
      destruct ser, tl. 
      unfold append_serialize, opt_serialize in H.
      destruct e eqn:Ee. 
      * simpl in *. repeat destruct_enc. inversion H. subst. 
        clear H. 

        eassert (G1 := proj1 (open_type_to_len_correct _ _ _ (proj1 ser_non_inter) (proj1 tl_c))
                         _ _ _ _ _ _ E).
        eassert (G2 := proj1 (IHext _ _ _ (proj2 ser_non_inter) (proj2 tl_c))
                         _ _ _ _ _ _ E0).
        rewrite G1, G2.
        simpl. f_equal.

        eassert (LE1 := open_type_non_inter _ o (proj1 ser_non_inter)
                          _ _ _ _ _ _ E).
        eassert (LE2 := ext_serialize_latter_non_inter _ _ _  (proj2 ser_non_inter)
                          _ _ _ _ _ _ E0).
        split_and.  unfold BProp.le_pos in *.
        lia.

      * simpl in *. repeat destruct_enc. inversion H. subst.
        clear H. 
        destruct t.
        apply put_unit_pos_no_change in E. split_and. subst.
        

        eassert (G := proj1 (IHext _ _ _ H6 H4) _ _ _ _ _ _ E0).
        rewrite G. auto.


    + intros. destruct b. simpl in H.
      unfold append_parse, opt_parse, bind_parse, return_parse in H.
      repeat destruct_enc. inversion H. subst. clear H. 
      destruct a. destruct e eqn:Ee.
      * simpl in E. destruct_enc. inversion E. subst. clear E.
        destruct tl, ser, par. simpl in *. 

        eassert (G1 := proj2 (open_type_to_len_correct _ _ _ (proj1 ser_non_inter) (proj1 tl_c))
                                 _ _ _ _ _ _ E1).
        eassert (G2 := proj2 (IHext _ _ _ (proj2 ser_non_inter) (proj2 tl_c))
                         _ _ _ _ _ _ _ _ E0).
        destruct_ex. rewrite H0, H.  simpl. eauto.
      * simpl in E. inversion E. subst. clear E.
        destruct tl, ser, par. simpl in *.  
        eassert (G2 := proj2 (IHext _ _ _ (proj2 ser_non_inter) (proj2 tl_c))
                         _ _ _ _ _ _ _ _ E0).  
        destruct G2.  exists x.  rewrite H.  auto. 
        Unshelve. apply SameVer. apply SameVer. 
Qed.

Opaque Nat.pow.
Lemma small_len_to_len_eq_some a (pf_a : 1 <= a < Nat.pow 2 14) :
  exists n, 
  (T_to_len nat
     (fun n0 : nat => 1 <= n0 < Nat.pow 2 14)
     LengthDet.normally_small_len_det_format
     a = Some n).
Proof.
  simpl.
  destruct a.
  - lia.
  - simpl.
    destruct (Nat.leb a 63); simpl; eauto. 
Qed.

Definition to_len_half_dep {A B : Set} {Pa : A -> Prop} {Pb : B -> Prop}
  (decode : forall a : A, Pa a -> Flg -> Parse B Pb)
  (to_len : B -> option nat) (f : B -> A) :=
  (forall (b : B) (bf : BA.Buffer) (pos pos' : BA.Pos)
          (pf : Pb b) (pf_a : Pa (f b)) (flg flg' : Flg),
      decode (f b) pf_a flg bf pos =
        Some (exist Pb b pf, pos', flg') ->
      exists n : nat, to_len b = Some n).

Lemma read_unit_pos_no_change : forall bf pos pos' flg, 
    read_unit bf pos = Some (exist _ tt I, pos', flg) ->
    pos = pos' /\ flg = SameVer.
Proof.
  intros. unfold read_unit in H.
  destruct_match_dec_new.
  inversion H. auto.
Qed.

(* if we run to-parse-none, we should get all none  *)
Lemma to_parse_none_all_none (ext : list typ) :
  forall bf pos pos' a pf_a flg, 
  to_parse_none ext bf pos = Some (exist _ a pf_a, pos', flg) 
  ->  a = ext_all_none ext /\ pos = pos'. 
Proof.
  induction ext; intros.
  - simpl in *. destruct a. destruct pf_a.
    unfold to_parse_none, bind_parse, return_parse in H.
    destruct_enc. inversion H.  subst.
    destruct x.  destruct t.
    apply read_unit_pos_no_change in E. 
    split_and. auto. 
    
  - destruct a0.  simpl in H.  unfold to_parse_none, bind_parse, return_parse in H.
    destruct_enc.  inversion H. subst. clear H. 
    destruct x, t. apply read_unit_pos_no_change in E.  split_and. subst.
    
    split; auto. 
Qed.

Lemma seq_ext_len_all_none_eq_0 ext l0 : seq_ext_to_len_latter ext l0 (ext_all_none ext) = Some 0.
Proof.
  induction ext.
  - simpl; auto.
  - destruct l0. simpl. rewrite IHext. auto.
Qed.

Definition to_parse_le_to_len ext (ser : get_serial_prod ext) par tl
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (tl_c : get_cond_tl_prod ext ser par tl format_to_len_correct)  :
  forall x0 pf0 bf p0 pos' a pf flg,
  
  to_parse_latter_le ext par x0 pf0 bf p0 =
    Some (exist (seq_ext_cond ext) a pf, pos', flg)
  -> 
    exists n, seq_ext_to_len_latter ext tl a = Some n.
Proof.
  induction ext.
  - simpl.  intros. eauto.
  - destruct a0.  simpl.  destruct x0. 
    + (* x0 as nil or not *)
      intros. destruct a, tl. 
      apply to_parse_none_all_none in H. split_and.
      simpl in H0. inversion H0.  subst.  clear H0.
      simpl.
      
      rewrite seq_ext_len_all_none_eq_0.  eauto.
    + intros. destruct a, tl. unfold append_parse, opt_parse, bind_parse, return_parse in H.
      repeat destruct_enc. inversion H. subst. clear H. destruct e eqn:Ee.
      * destruct b.
        { destruct_enc.  inversion E.  subst.  clear E.
          eassert (G1 := proj2 (open_type_to_len_correct _ _ _ (proj1 ser_non_inter) (proj1 tl_c))
                           _ _ _ _ _ _ E1). 
          eassert (G2 := (IHext _ _ _ (proj2 ser_non_inter) (proj2 tl_c))
                           _ _ _ _ _ _ _ _ E0).
          destruct_ex. simpl in *.  rewrite H0, H.
          simpl. eauto.
        }
        { inversion E. }
      * destruct b.
        { destruct_enc. inversion E. }
        { inversion E. subst. clear E. 
          eassert (K := IHext  _ _ _ (proj2 ser_non_inter) (proj2 tl_c) _ _ _ _ _ _ _ _ E0). 
          destruct K. exists x. simpl. simpl in H.
          rewrite H.  auto. 
        }
Qed.

Definition to_parse_ge_to_len ext (ser : get_serial_prod ext) par tl
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (tl_c : get_cond_tl_prod ext ser par tl format_to_len_correct)  :
  forall x0 pf0 bf p0 pos' a pf flg,
  
  to_parse_latter_ge ext par x0 pf0 bf p0 =
    Some (exist (seq_ext_cond ext) a pf, pos', flg)
  -> 
    exists n, seq_ext_to_len_latter ext tl a = Some n.
Proof.
  intros. 
  unfold to_parse_latter_ge, bind_parse, return_parse in H.
  repeat destruct_enc.  inversion H.  subst.  clear H.

  eassert (K := ext_type_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ E).
  
  assert (length (ext_to_bit_list ext a) = length2 ext).
  { rewrite <- ext_to_bit_list_len. rewrite length_eq_length2. auto. } 
  assert (Gx :  to_parse_latter_eq ext par (ext_to_bit_list ext a)
               H bf p0 =
                  Some (exist (seq_ext_cond ext) a s, p, f)).
  { generalize dependent H.
    rewrite K. intros.
    
    assert ((List.firstn_length_le x0
         (PeanoNat.Nat.lt_le_incl (length2 ext) 
            (length x0) pf0)) = H).
    { apply proof_irrelevance. }
    rewrite <- H0.
    rewrite E.  auto. } 

  eassert (G :=  seq_ext_to_len_latter_eq_correct _ _ _ _ ser_non_inter tl_c).
  eapply G.
  apply SameVer.
  apply Gx.
Qed.
  
Lemma seq_ext_to_len_correct  (ext : list typ)
  (ext_len : 1 <= length2 ext < Nat.pow 2 14):
  forall (ser : get_serial_prod ext)
         (par : get_parse_prod ext)
         (tl : get_to_len_prod ext)
         (ser_non_inter : get_cond_prod ext ser encode_non_inter)
         (tl_c : get_cond_tl_prod ext ser par tl format_to_len_correct),
    format_to_len_correct  _ _ (ext_serialize ext ser tl)
                          (ext_parse ext par)
                          (seq_ext_to_len ext tl).
Proof.
  intros. unfold format_to_len_correct. split.
  - intros. unfold ext_serialize, prepend_serialize, append_serialize in H.
    repeat destruct_enc. inversion E1. inversion E2. inversion E. inversion H.
    subst. clear E1. clear E2. clear E. clear H.

    unfold fst, snd in *.

    unfold seq_ext_to_len.

    eassert (G1 := proj1 (fmt_len_c (T_Correct _ _ LengthDet.normally_small_len_det_format))
                     _ _ _ _ _ _ E0).
    eassert (G2 := proj1 (fmt_len_c (T_Correct _ _ (list_bool_format (length2 ext))))
                     _ _ _ _ _ _ E3).
    simpl in G2.
    rewrite list_to_len_1 in G2; auto. 
    
    eassert (G3 := proj1 (seq_ext_to_len_latter_eq_correct _ _ _ _ ser_non_inter tl_c)
                     _ _ _ _ _ _  E4).
    
    rewrite G1, G2, G3. simpl.  f_equal.
    
    eassert (LE1 := fmt_enc_ni (T_Correct _ _ LengthDet.normally_small_len_det_format)
                      _ _ _ _ _ _ E0). 
    eassert (LE2 := fmt_enc_ni (T_Correct _ _  (list_bool_format (length2 ext)))
                      _ _ _ _ _ _ E3).
    eassert (LE3 := ext_serialize_latter_non_inter _ _ tl ser_non_inter
                      _ _ _ _ _ _ E4).
    
    split_and. unfold BProp.le_pos in *. 
    lia.
  - intros.
    unfold ext_parse, bind_parse in H.
    repeat destruct_enc.
    destruct (lt_eq_lt_dec_new (length x0) (length2 ext)).
    + unfold seq_ext_to_len.
      eassert (K' := small_len_to_len_eq_some (length2 ext) (ext_len)).
      destruct K'.  rewrite H0. simpl. 
      eassert (K2 := to_parse_le_to_len _ _ _ _ ser_non_inter tl_c
                       _ _ _ _ _ _ _ _  H).
      destruct_ex. rewrite H1.  eauto. 

    + eassert (G1 := proj2 (fmt_len_c (T_Correct _ _ LengthDet.normally_small_len_det_format))
                       _ _ _ _ _ _ E). 
      subst.
      eassert (G2 := proj2 (fmt_len_c (T_Correct _ _ (list_bool_format (length x0))))
                       _ _ _ _ _ _ E0).

      unfold seq_ext_to_len. rewrite <- pf0.
      eassert (K := ext_type_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ H).  subst. 
      
      eassert (G3 :=  proj2 (seq_ext_to_len_latter_eq_correct _ _ _ _ ser_non_inter tl_c)
                        a bf p0 pos' _ _ _ _  H).
      destruct_ex. rewrite H1, H0.
      simpl.  eauto.
      
    + unfold seq_ext_to_len.
      eassert (K' := small_len_to_len_eq_some (length2 ext) (ext_len)).
      destruct K'.  rewrite H0. simpl.
      eassert (K2 := to_parse_ge_to_len _ _ _ _ ser_non_inter tl_c
                       _ _ _ _ _ _ _ _  H).
      destruct_ex. rewrite H1.  eauto.
      Unshelve. apply SameVer.
Qed.

(* This only covers to-parse-latter-eq. 
   However, we might have to consider other cases as well
 *)
Lemma seq_ext_latter_eq_inj_diff
  (ext : list typ)
  (ser : get_serial_prod ext)
  (par : get_parse_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (len_correct : get_cond_tl_prod ext ser par len_prod format_to_len_correct)
  (prod_inj : get_cond_tl_prod ext ser par len_prod format_correct_inj_diff)
  : format_correct_inj_diff_dep  (ext_serialize_latter ext ser len_prod)
      (fun (a : list bool) (pf_a : length a = length2 ext) (_ : Flg) =>
         to_parse_latter_eq ext par a pf_a)
      (seq_ext_to_len_latter ext len_prod)
      (fun z : seq_ext_type ext => ext_to_bit_list ext z).
Proof.
  induction ext.
  - simpl in *. unfold format_correct_inj_diff_dep.  intros.
    eapply unit_format_inj_diff.
    apply H.
  - unfold format_correct_inj_diff_dep. intros.
    destruct b, e. 

    + destruct pf. simpl in o, s. 
      assert (append_parse
                (OpenType.open_typ_parse (fst par))
                (to_parse_latter_eq ext (snd par)
                   (ext_to_bit_list ext (snd (Some t, l)))
                   (eq_add_S (length (ext_to_bit_list ext (snd (Some t, l))))
                      (length2 ext) pf_a)) bf pos =
                Some
                  (exist
                     (fun g  =>
                        (typ_cond a) (fst g) /\ seq_ext_cond ext (snd g))
                     (t, l) (conj o s), pos', flg')).
      
      { simpl in H. unfold append_parse, bind_parse, return_parse in H.
        repeat destruct_enc. inversion H. 
        subst. clear H. simpl. inversion E. subst. clear E.

        unfold append_parse, bind_parse, return_parse in *. 
        rewrite E1. rewrite E0.  
        decode_eq. }

      destruct a. simpl in *. destruct ser, len_prod.

      eassert (G :=
                 append_inj_diff_dep _ _ _ _ _ _ _
                   (open_type_non_inter _ _  (proj1 ser_non_inter))
                   (open_type_to_len_correct _ _ _ (proj1 ser_non_inter) (proj1 len_correct))
                   (seq_ext_to_len_latter_eq_correct _ _ _ _ (proj2 ser_non_inter)
                       (proj2 len_correct))
                   (open_type_inj_diff _ _ _ (proj1 prod_inj) (proj1 len_correct) (proj1 ser_non_inter))
                   (IHext _ _ _ (proj2 ser_non_inter) (proj2 len_correct) (proj2 prod_inj))
                   (t, l) bf pos _ _ _ _ _ H0).
      apply G. 

    + simpl in *.
      unfold opt_parse, append_parse, bind_parse, return_parse in H. simpl in H. 
      destruct_enc. inversion H. subst. clear H.
      
      simpl in *. 
      assert (G := (IHext _ _ _ (proj2 ser_non_inter) (proj2 len_correct) (proj2 prod_inj))).

      apply G in E.
      unfold append_serialize, opt_serialize in *.  simpl.
      destruct E.  exists x.  intros.
      apply H in H0.  destruct H0.
      { left. destruct len_prod. simpl in H0. 
        intro. destruct (seq_ext_to_len_latter ext l0 l).
        destruct (H0 H1).
        destruct (H0 H1).
      } 

      right. destruct_ex. split_and.  exists x0. exists x1.  
           
      rewrite <- append_unit_eq_nothing in H1.
      unfold append_serialize in H1.  simpl in H1.  rewrite H1.
      split. 
      * encode_eq.
      * lia. 
      * apply ext_serialize_latter_non_inter. 
        auto.
      *  apply SameVer.
         Unshelve.
      apply SameVer.
Qed.

Lemma ext_serialize_all_none (ext : list typ)
  (ser : get_serial_prod ext)
  (tl : get_to_len_prod ext) :
  forall bf bf' pos pos' pf_a, 
    ext_serialize_latter ext ser tl bf pos (ext_all_none ext) = Some (bf', pos', pf_a) ->
    bf = bf' /\ pos = pos'.
Proof.
  induction ext.
  - simpl.  intros.  apply put_unit_pos_no_change. destruct pf_a.  auto.
  - intros. simpl in H.

    unfold append_serialize in H. simpl in H.
    repeat destruct_enc. inversion H. subst. clear H.
    destruct t. 
    apply put_unit_pos_no_change in E.  destruct E. subst.

    eapply IHext.
    apply E0.
Qed.

Lemma unit_valid_enc :
  forall pos bf a,
    BA.to_nat pos <= BA.len bf ->
    put_unit bf pos a = Some (bf, pos, I).
Proof. 
  intros. 
  unfold put_unit.
  destruct_if_goal; try lia. 
Qed.


Lemma ext_serialize_none_valid_enc (ext : list typ)
  (ser : get_serial_prod ext)
  (tl : get_to_len_prod ext) :
  forall bf pos pf_a,
    BA.to_nat pos <= BA.len bf -> 
    ext_serialize_latter ext ser tl bf pos (ext_all_none ext) = Some (bf, pos, pf_a).
Proof.
  induction ext.
  - simpl.  intros. destruct pf_a.   apply unit_valid_enc.  auto.
  - intros.  simpl. 

    unfold append_serialize. simpl.
    eassert (G1 := unit_valid_enc pos bf tt H).
    rewrite G1. 
    destruct pf_a. 
    erewrite IHext.
    + encode_eq.
    + auto. 
      Unshelve.
      apply ext_all_none_pf. 
Qed.


Ltac solve_monotone :=
  match goal with
  | [ H : ~ get_byte_len ?z < ?a |- ~ get_byte_len ?y < ?a ] =>
      let H' := fresh "H'" in 
      assert (H' : z <= y) ; try lia; (* Prove x <= x + y *)
      apply get_byte_len_mono in H'; lia
  end.


Lemma seq_ext_latter_le_inj_diff
  (ext : list typ)
  (ser : get_serial_prod ext)
  (par : get_parse_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (len_correct : get_cond_tl_prod ext ser par len_prod format_to_len_correct)
  (prod_inj : get_cond_tl_prod ext ser par len_prod format_correct_inj_diff)
  : forall (bl : list bool) pf_bl,
    format_correct_inj_diff  _ _  (ext_serialize_latter ext ser len_prod)
      (to_parse_latter_le ext par bl pf_bl)
      (seq_ext_to_len_latter ext len_prod).
Proof.
  induction ext.
  - intros. simpl in pf_bl. lia.
  - intros. 
    unfold format_correct_inj_diff. intros. 
    simpl. simpl in H. destruct bl eqn:Ebl.
    + eassert (X1 := to_parse_none_all_none _ _ _ _ _ _ _ H).
      unfold to_parse_none, bind_parse, return_parse in H.
      destruct_enc. inversion H.  subst.  clear H.

      unfold append_serialize, opt_serialize. simpl.

      exists (BA.to_nat pos). intros.
      rewrite unit_valid_enc; auto; try lia. 

       split_and. subst.
      erewrite ext_serialize_none_valid_enc; auto; try lia.
      right. 
      exists bf0, pos0.
      split.
      * encode_eq.
      * lia. 
      
    + unfold append_parse, opt_parse, bind_parse, return_parse in H.
      destruct a. destruct ser, par, len_prod.  simpl in *. 
      destruct b eqn:Eb.
      * repeat destruct_enc. inversion H. subst. clear H.
        inversion E. subst. clear E. 

        unfold append_serialize, opt_serialize. simpl. 
        eassert (G1 := IHext _ _ _ (proj2 ser_non_inter) (proj2 len_correct) (proj2 prod_inj) _
                         (Arith_base.lt_S_n_stt _ _ pf_bl)
                         _ _ _ _ _ _ E0).
        eassert (G2 := open_type_inj_diff _ _ _  (proj1 prod_inj)  (proj1 len_correct) (proj1 ser_non_inter)
                         _ _ _ _ _ _ E1).

        destruct_ex. 
        exists (x + x2). intros.

        eassert (K1 := proj2 (open_type_to_len_correct _ _ _ (proj1 ser_non_inter)  (proj1 len_correct))
                         _ _ _ _ _ _ E1).
        eassert (K2 := to_parse_le_to_len _ _ _ _ (proj2 ser_non_inter)  (proj2 len_correct)
                         _ _ _ _ _ _ _ _ E0). 
        destruct_ex.
        rewrite H3, H2. 
        
        assert (BA.to_nat pos0 + x <= BA.len bf0).  { lia. }
        
        apply H in H4. destruct H4.
        { left. rewrite H3 in H4.  simpl. solve_monotone. }


        destruct_ex. destruct H4. 
        eassert (NI1 := same_len_after_enc _ (open_type_non_inter _ o (proj1 ser_non_inter)) H4).

        assert (BA.to_nat x6 + x2 <= BA.len x5).  { lia. }
        apply H0 in H6. destruct H6.
        { left. rewrite H2 in H6. simpl. solve_monotone. } 

        right. destruct_ex. destruct H6. 
        rewrite H4, H6. 
        
        exists x7, x8.
        split.
        {  encode_eq. }
        { lia. } 

      * destruct_enc. inversion H. subst. clear H.

        eassert (G1 := IHext _ _ _ (proj2 ser_non_inter) (proj2 len_correct) (proj2 prod_inj) _
                         (Arith_base.lt_S_n_stt _ _ pf_bl)
                         _ _ _ _ _ _ E).
        
        unfold append_serialize, opt_serialize.  simpl.
        destruct G1. 
        
        exists x0.  intros.  apply H in H0. destruct H0.
        { left.  auto. intro. destruct (seq_ext_to_len_latter ext l2 x).
          auto. auto. 
        } 
        right.
        destruct_ex. destruct H0. 
        
        rewrite <- append_unit_eq_nothing in H0.
        unfold append_serialize in H0. simpl in H0.
        rewrite H0. exists x1, x2. split.
        { encode_eq. }
        { lia. }

        apply ext_serialize_latter_non_inter.  apply (proj2 ser_non_inter).

        Unshelve.
        apply ext_all_none_pf. 
Qed.

Lemma seq_ext_latter_ge_inj_diff
  (ext : list typ)
  (ser : get_serial_prod ext)
  (par : get_parse_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (len_correct : get_cond_tl_prod ext ser par len_prod format_to_len_correct)
  (prod_inj : get_cond_tl_prod ext ser par len_prod format_correct_inj_diff)
  : forall (bl : list bool) pf_bl,
    format_correct_inj_diff  _ _  (ext_serialize_latter ext ser len_prod)
      (to_parse_latter_ge ext par bl pf_bl)
      (seq_ext_to_len_latter ext len_prod).
Proof.
  intros.  unfold to_parse_latter_ge.
  unfold format_correct_inj_diff.
  intros. unfold bind_parse, return_parse in H. repeat destruct_enc.
  inversion H.  subst. clear H. 

    eassert (K := ext_type_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ E).
  
  assert (length (ext_to_bit_list ext a) = length2 ext).
  { rewrite <- ext_to_bit_list_len. rewrite length_eq_length2. auto. } 
  assert (Gx :  to_parse_latter_eq ext par (ext_to_bit_list ext a)
               H bf pos =
                  Some (exist (seq_ext_cond ext) a s, p, f)).
  { generalize dependent H.
    rewrite K. intros.
    
    assert ((List.firstn_length_le bl
         (PeanoNat.Nat.lt_le_incl (length2 ext) 
            (length bl) pf_bl)) = H).
    { apply proof_irrelevance. }
    rewrite <- H0.
    rewrite E.  auto. } 

  eassert (G0 := seq_ext_latter_eq_inj_diff _ _ _ _ ser_non_inter len_correct prod_inj
                   a _ _ _ _ _ _ _  Gx).
  assert (pf = s). { apply proof_irrelevance. } rewrite H0. auto. 
  Unshelve.
  apply SameVer.
Qed.
  
Lemma ext_none_length ext :
  length (ext_to_bit_list ext (ext_all_none ext)) = length ext.
Proof.
  induction ext; simpl; auto. 
Qed.

(* This lemma does not make sense.  *)
Lemma ext_type_le_to_bit_list_valid_inj  :
  forall (ext : list typ) (par : get_parse_prod ext) (a : seq_ext_type ext)
         (pf : seq_ext_cond ext a) (x : list bool) (pf_l : length x < length2 ext)
         (bf : BA.Buffer) (pos pos' : BA.Pos) (flg : Flg),
    to_parse_latter_le ext par x pf_l bf pos =
      Some (exist (seq_ext_cond ext) a pf, pos', flg) ->
    length (ext_to_bit_list ext a) = length2 ext.
Proof.
  induction ext; intros. 
  - simpl.  simpl in H.
    destruct x; auto. 
  - simpl. 
    destruct x. 
    + simpl in *. 
      
      eassert (G := to_parse_none_all_none _ _ _ _ _ _ _ H). destruct G.
      subst.
      rewrite length_eq_length2. simpl. rewrite ext_none_length. auto. 
      
    + simpl in H.  unfold append_parse, opt_parse, bind_parse, return_parse in H.
      destruct b eqn:Eb.
      * repeat destruct_enc. inversion H. inversion E. subst.
        f_equal. eapply IHext. apply E0.
      * destruct_enc.  inversion H.  subst. f_equal.
        eapply IHext. apply E.
Qed.

Lemma ext_type_ge_to_bit_list_valid_inj  :
  forall (ext : list typ) (par : get_parse_prod ext) (a : seq_ext_type ext)
         (pf : seq_ext_cond ext a) (x : list bool) (pf_l : length x > length2 ext)
         (bf : BA.Buffer) (pos pos' : BA.Pos) (flg : Flg),
    to_parse_latter_ge ext par x pf_l bf pos =
      Some (exist (seq_ext_cond ext) a pf, pos', flg) ->
    length (ext_to_bit_list ext a) = length2 ext.
Proof.
  intros.  unfold to_parse_latter_ge in H.
  unfold bind_parse, return_parse in H.
  repeat destruct_enc.
  inversion H.  subst.  clear H.

  apply ext_type_to_bit_list_valid_inj in E.
  rewrite E.
  rewrite List.firstn_length_le; lia.
Qed.


Require Import ASN1Parser.Formats.ValidEncProp.
Lemma seq_ext_inj_diff
  (ext : list typ)
  (len_ext : 1 <= length2 ext < Nat.pow 2 14)
  (ser : get_serial_prod ext)
  (par : get_parse_prod ext)
  (len_prod : get_to_len_prod ext)
  (ser_non_inter : get_cond_prod ext ser encode_non_inter)
  (len_correct : get_cond_tl_prod ext ser par len_prod format_to_len_correct)
  (prod_inj : get_cond_tl_prod ext ser par len_prod format_correct_inj_diff)
  : format_correct_inj_diff _ _  (ext_serialize ext ser len_prod)
      (ext_parse ext par)
      (seq_ext_to_len ext len_prod).
Proof.
  intros. unfold format_correct_inj_diff. intros.
  unfold ext_parse, bind_parse, return_parse in H.

  repeat destruct_enc.

  destruct ( lt_eq_lt_dec_new (length x0) (length2 ext)).
  - 

    (* Here, the problem is the encoding should go thorugh, even through
         I don't have a parse function before. I should still be able to 
         say, there exists some minimum length which I can encode it to. 

         Similar to the 'SameVer' property.
     *)

    destruct small_det_valid_enc.
    unfold ext_serialize. 
    destruct (bool_list_valid_enc (length2 ext)). 
    
    (* eassert (Ex := ext_type_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ H). *)

    eassert (G1 := seq_ext_latter_le_inj_diff _ _ _ _ ser_non_inter len_correct prod_inj
                     x0 pf0
                     _ _ _ _ _ _ H).
    destruct G1. 
    
    exists (x1 + x2 + x3). 
    intros. 
    unfold ext_serialize, prepend_serialize, append_serialize, fst, snd.
    
    assert (BA.to_nat pos0 + x1 <= BA.len bf0). { lia. }

    eassert (S1 := H0 pos0 bf0  (length2 ext) len_ext H4). 
    
    destruct_ex. split_and. 
    rewrite H6. 
    eassert (S1_H := ext_type_le_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ H).
    (* NTS length does not change *)
    eassert (L1 := same_len_after_enc _
                     (fmt_enc_ni (T_Correct _ _  LengthDet.normally_small_len_det_format))
                     H6). 
    
    assert ( BA.to_nat x5 + x2 <= BA.len x4). { lia. }
    eassert (S2 := H1 _ _   (ext_to_bit_list ext a) S1_H H11).

    destruct_ex. split_and. 
    rewrite H13.  

    eassert (L2 := same_len_after_enc _
                     (fmt_enc_ni (T_Correct _ _ (list_bool_format (length2 ext))))
                     H13). 
    
    assert (BA.to_nat x7 + x3 <= BA.len x6). { lia. } 
    eassert (S3 := H2 _ _ H12).
    destruct S3. 
    { left. unfold seq_ext_to_len.
      eassert (K2 := to_parse_le_to_len _ _ _ _ ser_non_inter  len_correct
                       _ _ _ _ _ _ _ _ H).
      destruct K2. rewrite H16 in *.
      eassert (K1 := small_len_to_len_eq_some (length2 ext) (conj H9 H10)).
      destruct K1. rewrite H17. simpl.
      solve_monotone. 
    } 

    right.
    destruct_ex. split_and.
    rewrite H16.  exists x8, x9.
    split. 
    + encode_eq.
    + lia. 
      

  - eassert (EE := fmt_inj_diff (T_Correct _ _ LengthDet.normally_small_len_det_format)
                     _ _ _ _ _ _ E).

    eassert (Ex := ext_type_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ H).

    unfold bool_list_parse in E0. subst. 
    eassert (EB := fmt_inj_diff (T_Correct _ _ (list_bool_format  (length (ext_to_bit_list ext a))))
                     _ _ _ _ _ _ E0).
    
    eassert (ET := seq_ext_latter_eq_inj_diff _ _ _ _ ser_non_inter len_correct
                     prod_inj _ _ _ _ _ _ _ _ H).

    destruct EE, EB, ET.
    exists (x + x0 + x1).
    intros.
    unfold ext_serialize, prepend_serialize, append_serialize.  

    eassert (K1 := small_len_to_len_eq_some (length2 ext) len_ext).
    eassert (K2 := proj2 (seq_ext_to_len_latter_eq_correct _ _ _ _ ser_non_inter  len_correct)
                     _ _ _ _ _ _ _ _ H). 
    destruct_ex. 
    unfold seq_ext_to_len. rewrite H5, H4. 
    
    assert (BA.to_nat pos0 + x <= BA.len bf0). { lia. }
    apply H0 in H6. destruct H6.
    { left. rewrite <- pf0 in H5.  rewrite H5 in H6. simpl.
      solve_monotone. } 

    unfold fst, snd, LengthDet.small_enc.
    rewrite <- pf0. 
    destruct_ex. destruct H6. 
    eassert (EE1 := same_len_after_enc _
                      (fmt_enc_ni (T_Correct _ _ LengthDet.normally_small_len_det_format)) H6).
    assert (BA.to_nat x5 + x0 <= BA.len x4). { lia. }

    apply H1 in H8. destruct H8.
    { left. simpl.
      eassert (K3 := proj2 (fmt_len_c (T_Correct _ _ (list_bool_format (length (ext_to_bit_list ext a)))))
                       _ _ _ _ _ _ E0).
      destruct K3.  rewrite H9 in H8.
      simpl in H9. 
      rewrite list_to_len_1 in H9.  inversion H9.
      solve_monotone. auto. } 
    
    destruct_ex. destruct H8. 
    unfold bool_list_serialize.
    rewrite H6, H8. 
    
    eassert (BE1 := same_len_after_enc _
                      (fmt_enc_ni (T_Correct _ _
                                     (list_bool_format (length (ext_to_bit_list ext a))))) H8).
    assert (BA.to_nat x7 + x1 <= BA.len x6). { lia. }
    
    apply H2 in H10.  destruct H10.
    { left. rewrite H4 in H10. simpl. solve_monotone. } 
    right. destruct_ex. destruct H10. 
    rewrite H10.  exists x8, x9.
    split. encode_eq. lia. 


  - 
    destruct small_det_valid_enc.
    unfold ext_serialize. 
    destruct (bool_list_valid_enc (length2 ext)). 
    
    (* eassert (Ex := ext_type_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ H). *)

    eassert (G1 := seq_ext_latter_ge_inj_diff _ _ _ _ ser_non_inter len_correct prod_inj
                     x0 pf0
                     _ _ _ _ _ _ H).
    destruct G1.

    exists (x1 + x2 + x3).
    intros.
    unfold ext_serialize, prepend_serialize, append_serialize.
    
    assert (BA.to_nat pos0 + x1 <= BA.len bf0). { lia. }

    eassert (S1 := H0 pos0 bf0  (length2 ext) len_ext H4). 
    destruct_ex. split_and. simpl. 
    rewrite H6.  
    eassert (S1_H := ext_type_ge_to_bit_list_valid_inj _ _ _ _ _ _ _ _ _ _ H).
    (* NTS length does not change *)
    eassert (L1 := same_len_after_enc _
                     (fmt_enc_ni (T_Correct _ _  LengthDet.normally_small_len_det_format))
                     H6). 
    
    assert ( BA.to_nat x5 + x2 <= BA.len x4). { lia. }
    eassert (S2 := H1 _ _   (ext_to_bit_list ext a) S1_H H11).

    destruct_ex. split_and. 
    rewrite H13.  

    eassert (L2 := same_len_after_enc _
                     (fmt_enc_ni (T_Correct _ _ (list_bool_format (length2 ext))))
                     H13). 
    
    assert (BA.to_nat x7 + x3 <= BA.len x6). { lia. } 
    eassert (S3 := H2 _ _ H12).
    destruct S3. 
    { left. unfold seq_ext_to_len.
      eassert (K2 := to_parse_ge_to_len _ _ _ _ ser_non_inter  len_correct
                       _ _ _ _ _ _ _ _ H).
      destruct K2. rewrite H16 in *.
      eassert (K1 := small_len_to_len_eq_some (length2 ext) (conj H9 H10)).
      destruct K1. rewrite H17. simpl.
      solve_monotone. 
    }
    right.
    destruct_ex. split_and.
    rewrite H16.  exists x8, x9.
    split. 
    + encode_eq.
    + lia.
      Unshelve. apply SameVer. apply SameVer.
Qed.
