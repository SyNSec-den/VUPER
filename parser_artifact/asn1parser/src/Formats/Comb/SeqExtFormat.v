Require Import
  ASN1Parser.Array.BitRep
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.Comb.SeqProd
  ASN1Parser.Formats.Comb.SeqExt
  ASN1Parser.Formats.Comb.Seq
  ASN1Parser.Formats.Comb.SeqProp
  ASN1Parser.Formats.Comb.SeqExtProp
  ASN1Parser.Formats.Comb.HelperProp
  ASN1Parser.Formats.Comb.HelperComb
  ASN1Parser.Formats.CombProp
  ASN1Parser.Formats.Term.Unit
  ASN1Parser.Formats.Term.Boolean
  ASN1Parser.tact.

Require Import ProofIrrelevance.
Require Import Lia.

(* ------------------------------------------------------------------ *)
(* Helper lemmas: derive condition products from format product types  *)
(* ------------------------------------------------------------------ *)

(* seq helpers: seq_format_prod -> seq_cond_prod *)

Lemma seq_fmt_cond_enc_ni (l : list seq_elem) (fmt : seq_format_prod l) :
  seq_cond_prod l (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) encode_non_inter.
Proof.
  induction l; simpl; auto.
  destruct fmt as [s fmts'].
  destruct a; simpl;
    exact (conj (fmt_enc_ni (T_Correct _ _ s)) (IHl fmts')).
Qed.

Lemma seq_fmt_cond_enc_consist (l : list seq_elem) (fmt : seq_format_prod l) :
  seq_cond_prod l (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) encode_consistent.
Proof.
  induction l; simpl; auto.
  destruct fmt as [s fmts'].
  destruct a; simpl;
    exact (conj (fmt_enc_consist (T_Correct _ _ s)) (IHl fmts')).
Qed.

Lemma seq_fmt_cond_dec_consist (l : list seq_elem) (fmt : seq_format_prod l) :
  seq_cond_de_prod l (fmt_to_seq_prod l fmt Parse T_Parse read_unit) decode_consistent.
Proof.
  induction l; simpl; auto.
  destruct fmt as [s fmts'].
  destruct a; simpl;
    exact (conj (fmt_dec_consist (T_Correct _ _ s)) (IHl fmts')).
Qed.

Lemma seq_fmt_cond_surj (l : list seq_elem) (fmt : seq_format_prod l) :
  seq_cond_both_prod l
    (fmt_to_seq_prod l fmt Serialize T_Serial put_unit)
    (fmt_to_seq_prod l fmt Parse T_Parse read_unit)
    format_correct_surj.
Proof.
  induction l; simpl; auto.
  destruct fmt as [s fmts'].
  destruct a; simpl;
    exact (conj (fmt_surj (T_Correct _ _ s)) (IHl fmts')).
Qed.

Lemma seq_fmt_cond_inj_same (l : list seq_elem) (fmt : seq_format_prod l) :
  seq_cond_both_prod l
    (fmt_to_seq_prod l fmt Serialize T_Serial put_unit)
    (fmt_to_seq_prod l fmt Parse T_Parse read_unit)
    format_correct_inj_same.
Proof.
  induction l; simpl; auto.
  destruct fmt as [s fmts'].
  destruct a; simpl;
    exact (conj (fmt_inj_same (T_Correct _ _ s)) (IHl fmts')).
Qed.

Lemma seq_fmt_cond_len_c (l : list seq_elem) (fmt : seq_format_prod l) :
  seq_cond_tl_prod l
    (fmt_to_seq_prod l fmt Serialize T_Serial put_unit)
    (fmt_to_seq_prod l fmt Parse T_Parse read_unit)
    (fmt_to_seq_prod_no_cond l fmt (fun X => X -> option nat) T_to_len unit_to_len)
    format_to_len_correct.
Proof.
  induction l; simpl; auto.
  destruct fmt as [s fmts'].
  destruct a; simpl;
    exact (conj (fmt_len_c (T_Correct _ _ s)) (IHl fmts')).
Qed.

Lemma seq_fmt_cond_inj_diff (l : list seq_elem) (fmt : seq_format_prod l) :
  seq_cond_tl_prod l
    (fmt_to_seq_prod l fmt Serialize T_Serial put_unit)
    (fmt_to_seq_prod l fmt Parse T_Parse read_unit)
    (fmt_to_seq_prod_no_cond l fmt (fun X => X -> option nat) T_to_len unit_to_len)
    format_correct_inj_diff.
Proof.
  induction l; simpl; auto.
  destruct fmt as [s fmts'].
  destruct a; simpl;
    exact (conj (fmt_inj_diff (T_Correct _ _ s)) (IHl fmts')).
Qed.

(* ext helpers: get_formats -> get_cond_prod *)

Lemma ext_fmt_cond_enc_ni (ext : list typ) (fmt_ext : get_formats ext) :
  get_cond_prod ext (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit) encode_non_inter.
Proof.
  induction ext; simpl; auto.
  destruct fmt_ext as [t fmts'].
  destruct a; simpl;
    exact (conj (fmt_enc_ni (T_Correct _ _ t)) (IHext fmts')).
Qed.

Lemma ext_fmt_cond_enc_consist (ext : list typ) (fmt_ext : get_formats ext) :
  get_cond_prod ext (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit) encode_consistent.
Proof.
  induction ext; simpl; auto.
  destruct fmt_ext as [t fmts'].
  destruct a; simpl;
    exact (conj (fmt_enc_consist (T_Correct _ _ t)) (IHext fmts')).
Qed.

Lemma ext_fmt_cond_dec_consist (ext : list typ) (fmt_ext : get_formats ext) :
  get_cond_de_prod ext (fmt_to_prod ext fmt_ext Parse T_Parse read_unit) decode_consistent.
Proof.
  induction ext; simpl; auto.
  destruct fmt_ext as [t fmts'].
  destruct a; simpl;
    exact (conj (fmt_dec_consist (T_Correct _ _ t)) (IHext fmts')).
Qed.

Lemma ext_fmt_cond_surj (ext : list typ) (fmt_ext : get_formats ext) :
  get_cond_both_prod ext
    (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
    (fmt_to_prod ext fmt_ext Parse T_Parse read_unit)
    format_correct_surj.
Proof.
  induction ext; simpl; auto.
  destruct fmt_ext as [t fmts'].
  destruct a; simpl;
    exact (conj (fmt_surj (T_Correct _ _ t)) (IHext fmts')).
Qed.

Lemma ext_fmt_cond_inj_same (ext : list typ) (fmt_ext : get_formats ext) :
  get_cond_both_prod ext
    (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
    (fmt_to_prod ext fmt_ext Parse T_Parse read_unit)
    format_correct_inj_same.
Proof.
  induction ext; simpl; auto.
  destruct fmt_ext as [t fmts'].
  destruct a; simpl;
    exact (conj (fmt_inj_same (T_Correct _ _ t)) (IHext fmts')).
Qed.

Lemma ext_fmt_cond_len_c (ext : list typ) (fmt_ext : get_formats ext) :
  get_cond_tl_prod ext
    (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
    (fmt_to_prod ext fmt_ext Parse T_Parse read_unit)
    (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len)
    format_to_len_correct.
Proof.
  induction ext; simpl; auto.
  destruct fmt_ext as [t fmts'].
  destruct a; simpl;
    exact (conj (fmt_len_c (T_Correct _ _ t)) (IHext fmts')).
Qed.

Lemma ext_fmt_cond_inj_diff (ext : list typ) (fmt_ext : get_formats ext) :
  get_cond_tl_prod ext
    (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
    (fmt_to_prod ext fmt_ext Parse T_Parse read_unit)
    (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len)
    format_correct_inj_diff.
Proof.
  induction ext; simpl; auto.
  destruct fmt_ext as [t fmts'].
  destruct a; simpl;
    exact (conj (fmt_inj_diff (T_Correct _ _ t)) (IHext fmts')).
Qed.

(* ------------------------------------------------------------------ *)
(* Sub-lemma 1: encode_non_inter for seq_ext_serialize                 *)
(* ------------------------------------------------------------------ *)

Lemma seq_ext_full_enc_ni
  (l : list seq_elem) (fmt : seq_format_prod l)
  (ext : list typ) (fmt_ext : get_formats ext)
  : encode_non_inter _ _
      (seq_ext_serialize l
         (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) ext
         (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
         (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len)).
Proof.
  set (ser := fmt_to_seq_prod l fmt Serialize T_Serial put_unit).
  set (ser_ext := fmt_to_prod ext fmt_ext Serialize T_Serial put_unit).
  set (len_prod := fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len).
  (* Non-inter for seq_serialize l ser *)
  pose proof (prepend_non_inter (seq_type_to_bit_list l)
    (BoolList.bool_list_serialize (bit_list_len l))
    (seq_serialize_latter l ser)
    (fmt_enc_ni (T_Correct _ _ (BoolList.list_bool_format (bit_list_len l))))
    (seq_latter_non_inter l ser (seq_fmt_cond_enc_ni l fmt))) as SeqNi.
  (* Non-inter for ext_serialize ext ser_ext len_prod *)
  pose proof (ext_serialize_non_inter ext ser_ext len_prod
    (ext_fmt_cond_enc_ni ext fmt_ext)) as ExtNi.
  (* Main proof *)
  unfold encode_non_inter. intros a bf bf' pos pos' pf H.
  unfold seq_ext_serialize in H.
  destruct (check_all_none_dec ext (snd a)) as [pf_none|pf_not].
  - (* All-none case: bool_enc false + seq_serialize *)
    repeat destruct_enc. inversion H. subst. clear H.
    eapply append_non_inter_proof_helper.
    + exact (fmt_enc_ni (T_Correct _ _ bool_format) _ _ _ _ _ _ E).
    + exact (SeqNi _ _ _ _ _ _ E0).
  - (* Not-all-none case: bool_enc true + seq_serialize + ext_serialize *)
    repeat destruct_enc. inversion H. subst. clear H.
    eapply append_non_inter_proof_helper.
    + eapply append_non_inter_proof_helper.
      * exact (fmt_enc_ni (T_Correct _ _ bool_format) _ _ _ _ _ _ E).
      * exact (SeqNi _ _ _ _ _ _ E0).
    + exact (ExtNi _ _ _ _ _ _ E1).
Qed.

(* ------------------------------------------------------------------ *)
(* Sub-lemma 2: encode_consistent for seq_ext_serialize               *)
(* ------------------------------------------------------------------ *)

Lemma seq_ext_full_enc_consist
  (l : list seq_elem) (fmt : seq_format_prod l)
  (ext : list typ) (fmt_ext : get_formats ext)
  : encode_consistent _ _
      (seq_ext_serialize l
         (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) ext
         (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
         (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len)).
Proof.
  set (ser := fmt_to_seq_prod l fmt Serialize T_Serial put_unit).
  set (ser_ext := fmt_to_prod ext fmt_ext Serialize T_Serial put_unit).
  set (len_prod := fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len).
  pose proof (prepend_consistent (seq_type_to_bit_list l)
    (BoolList.bool_list_serialize (bit_list_len l))
    (seq_serialize_latter l ser)
    (fmt_enc_consist (T_Correct _ _ (BoolList.list_bool_format (bit_list_len l))))
    (seq_latter_encode_consist l ser (seq_fmt_cond_enc_ni l fmt) (seq_fmt_cond_enc_consist l fmt))
    (seq_latter_non_inter l ser (seq_fmt_cond_enc_ni l fmt))) as SeqConsist.
  pose proof (ext_serialize_consistent ext ser_ext len_prod
    (ext_fmt_cond_enc_ni ext fmt_ext)
    (ext_fmt_cond_enc_consist ext fmt_ext)) as ExtConsist.
  pose proof (prepend_non_inter (seq_type_to_bit_list l)
    (BoolList.bool_list_serialize (bit_list_len l))
    (seq_serialize_latter l ser)
    (fmt_enc_ni (T_Correct _ _ (BoolList.list_bool_format (bit_list_len l))))
    (seq_latter_non_inter l ser (seq_fmt_cond_enc_ni l fmt))) as SeqNi.
  pose proof (ext_serialize_non_inter ext ser_ext len_prod
    (ext_fmt_cond_enc_ni ext fmt_ext)) as ExtNi.
  unfold encode_consistent. intros a bf bf' pos pos' bf0 bf0' pos0 pos0' pf H1 H2.
  unfold seq_ext_serialize in H1, H2.
  destruct (check_all_none_dec ext (snd a)) as [pf_none|pf_not].
  - (* All-none: bool_enc false + seq_serialize *)
    (* After repeat destruct_enc: H2 gives E,E0; H1 gives E1,E2 *)
    repeat destruct_enc. inversion H1; inversion H2; subst.
    (* Normalize proof terms so both seq encodings share the same proof *)
    rewrite (proof_irrelevance _ s s0) in E0.
    rewrite (proof_irrelevance _ t t0) in E.
    eassert (G_bool := fmt_enc_consist (T_Correct _ _ bool_format)
               false bf b1 pos p1 bf0 b pos0 p t0 E1 E).
    eassert (NI_seq1 := SeqNi _ _ _ _ _ _ E2). split_and.
    eassert (NI_seq2 := SeqNi _ _ _ _ _ _ E0). split_and.
    eassert (G_seq := SeqConsist _ _ _ _ _ _ _ _ _ _ E2 E0).
    eapply (encode_consist_proof_helper b1 bf' b bf0' pos p1 pos' pos0 p pos0').
    + exact G_seq.
    + exact H.
    + exact H6.
    + exact G_bool.
  - (* Not-all-none: bool_enc true + seq_serialize + ext_serialize *)
    (* After repeat destruct_enc: H2 gives E(bool),E0(seq),E1(ext); H1 gives E2(bool),E3(seq),E4(ext) *)
    repeat destruct_enc. inversion H1; inversion H2; subst.
    (* Normalize proof terms *)
    rewrite (proof_irrelevance _ t0 t) in E2.
    rewrite (proof_irrelevance _ s1 s) in E3.
    rewrite (proof_irrelevance _ s2 s0) in E4.
    eassert (G_bool := fmt_enc_consist (T_Correct _ _ bool_format)
               true bf b2 pos p2 bf0 b pos0 p t E2 E).
    eassert (NI_seq1 := SeqNi _ _ _ _ _ _ E3).
    destruct NI_seq1 as [NI_s1_1 _].
    eassert (NI_seq2 := SeqNi _ _ _ _ _ _ E0).
    destruct NI_seq2 as [NI_s2_1 _].
    eassert (G_seq := SeqConsist _ _ _ _ _ _ _ _ _ _ E3 E0).
    eassert (NI_ext1 := ExtNi _ _ _ _ _ _ E4).
    destruct NI_ext1 as [NI_e1_1 _].
    eassert (NI_ext2 := ExtNi _ _ _ _ _ _ E1).
    destruct NI_ext2 as [NI_e2_1 _].
    eassert (G_ext := ExtConsist _ _ _ _ _ _ _ _ _ _ E4 E1).
    eassert (G_bs := encode_consist_proof_helper b2 b3 b b0 pos p2 p3 pos0 p p0
               G_seq NI_s1_1 NI_s2_1 G_bool).
    eapply (encode_consist_proof_helper b3 bf' b0 bf0' pos p3 pos' pos0 p0 pos0').
    + exact G_ext.
    + exact NI_e1_1.
    + exact NI_e2_1.
    + exact G_bs.
Qed.

(* ------------------------------------------------------------------ *)
(* Sub-lemma 3: decode_consistent for seq_ext_parse                   *)
(* ------------------------------------------------------------------ *)

Lemma seq_ext_full_dec_consist
  (l : list seq_elem) (fmt : seq_format_prod l)
  (ext : list typ) (fmt_ext : get_formats ext)
  : decode_consistent _ _
      (seq_ext_parse l
         (fmt_to_seq_prod l fmt Parse T_Parse read_unit) ext
         (fmt_to_prod ext fmt_ext Parse T_Parse read_unit)).
Proof.
  set (par := fmt_to_seq_prod l fmt Parse T_Parse read_unit).
  set (par_ext := fmt_to_prod ext fmt_ext Parse T_Parse read_unit).
  pose proof (bind_parse_consist
    (BoolList.bool_list_parse (bit_list_len l))
    (fun bl pf_bl _ => seq_parse_latter l par bl pf_bl)
    (fmt_dec_consist (T_Correct _ _ (BoolList.list_bool_format (bit_list_len l))))
    (fun bl pf_bl _ => seq_latter_decode_consist l par bl pf_bl
                         (seq_fmt_cond_dec_consist l fmt))) as SeqDecConsist.
  pose proof (ext_parse_consist ext par_ext
    (ext_fmt_cond_dec_consist ext fmt_ext)) as ExtDecConsist.
  unfold seq_ext_parse.
  apply bind_parse_consist.
  - eapply fmt_dec_consist. apply T_Correct.
  - intros b _ _. destruct b.
    + apply bind_parse_consist.
      * exact SeqDecConsist.
      * intros sa pf_sa flg1. apply bind_parse_consist.
        -- exact ExtDecConsist.
        -- intros se pf_se flg2.
           destruct (check_all_none_dec ext se).
           ++ apply fail_decode_consist.
           ++ apply return_parse_consist.
    + apply bind_parse_consist.
      * exact SeqDecConsist.
      * intros sa pf_sa flg1. apply return_parse_consist.
Qed.

(* ------------------------------------------------------------------ *)
(* Helper: check_all_none implies equal to ext_all_none               *)
(* ------------------------------------------------------------------ *)

Lemma check_all_none_unique (ext : list typ) (s : seq_ext_type ext) :
  check_all_none ext s -> s = ext_all_none ext.
Proof.
  induction ext; intros H.
  - destruct s. reflexivity.
  - destruct s as [e rest].
    destruct e as [v|].
    + simpl in H. destruct H.
    + simpl in H. rewrite (IHext _ H). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Sub-lemma 4: format_correct_surj                                   *)
(* ------------------------------------------------------------------ *)

Lemma seq_ext_full_surj
  (l : list seq_elem) (fmt : seq_format_prod l)
  (ext : list typ) (fmt_ext : get_formats ext)
  : format_correct_surj _ _
      (seq_ext_serialize l
         (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) ext
         (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
         (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len))
      (seq_ext_parse l
         (fmt_to_seq_prod l fmt Parse T_Parse read_unit) ext
         (fmt_to_prod ext fmt_ext Parse T_Parse read_unit)).
Proof.
  set (ser := fmt_to_seq_prod l fmt Serialize T_Serial put_unit).
  set (par := fmt_to_seq_prod l fmt Parse T_Parse read_unit).
  set (ser_ext := fmt_to_prod ext fmt_ext Serialize T_Serial put_unit).
  set (par_ext := fmt_to_prod ext fmt_ext Parse T_Parse read_unit).
  set (len_prod := fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len).
  pose proof (seq_fmt_cond_enc_ni l fmt) as SeqNiC.
  pose proof (seq_fmt_cond_dec_consist l fmt) as SeqDecC.
  pose proof (seq_fmt_cond_surj l fmt) as SeqSurjC.
  pose proof (ext_fmt_cond_enc_ni ext fmt_ext) as ExtNiC.
  pose proof (ext_fmt_cond_dec_consist ext fmt_ext) as ExtDecC.
  pose proof (ext_fmt_cond_len_c ext fmt_ext) as ExtLenC.
  pose proof (ext_fmt_cond_surj ext fmt_ext) as ExtSurjC.
  pose proof (seq_enc_non_inter l ser SeqNiC) as AllSeqNi.
  pose proof (seq_surj l ser par SeqNiC SeqDecC SeqSurjC) as AllSeqSurj.
  pose proof (seq_dec_consist l par SeqDecC) as AllSeqDec.
  pose proof (ext_serialize_non_inter ext ser_ext len_prod ExtNiC) as AllExtNi.
  pose proof (seq_ext_surj ext ser_ext par_ext len_prod ExtNiC ExtLenC ExtDecC ExtSurjC) as AllExtSurj.
  unfold format_correct_surj.
  intros [a_seq a_ext] bf bf' pos pos' pf H.
  unfold seq_ext_serialize in H.
  simpl fst in H. simpl snd in H.
  destruct (check_all_none_dec ext a_ext) as [pf_none|pf_not].
  - (* All-none: bool false + seq *)
    repeat destruct_enc. inversion H. subst. clear H.
    eassert (HBoolSurj := fmt_surj (T_Correct _ _ bool_format) false bf _ pos _ _ E).
    eassert (HSeqNiR := AllSeqNi a_seq _ bf' _ _ _ E0).
    destruct HSeqNiR as [HSeqEq0 HSeqNiR'].
    destruct HSeqNiR' as [_ HSeqLe].
    eassert (HBoolNiR := fmt_enc_ni (T_Correct _ _ bool_format) false bf _ pos _ _ E).
    destruct HBoolNiR as [_ HBoolNiR'].
    destruct HBoolNiR' as [_ HBoolLe].
    eassert (HBoolParse : T_Parse _ _ bool_format bf' pos = Some (exist _ false _ , _, SameVer)).
    { apply (proj2 (fmt_dec_consist (T_Correct _ _ bool_format) false _ pos _ _ SameVer HBoolSurj)).
      apply equiv_b_le_zero. exact HBoolLe. exact HSeqEq0. }
    eassert (HSeqSurj := AllSeqSurj a_seq _ bf' _ _ _ E0).
    assert (Hext : a_ext = ext_all_none ext) by exact (check_all_none_unique ext a_ext pf_none).
    subst a_ext.
    unfold seq_ext_parse, bind_parse, return_parse.
    rewrite HBoolParse. simpl.
    rewrite HSeqSurj. simpl.
    decode_eq.
  - (* Not-all-none: bool true + seq + ext *)
    repeat destruct_enc. inversion H. subst. clear H.
    eassert (HBoolSurj := fmt_surj (T_Correct _ _ bool_format) true bf _ pos _ _ E).
    eassert (HSeqNiR := AllSeqNi a_seq _ _ _ _ _ E0).
    destruct HSeqNiR as [HSeqEq0 HSeqNiR'].
    destruct HSeqNiR' as [_ HSeqLe].
    eassert (HExtNiR := AllExtNi a_ext _ bf' _ _ _ E1).
    destruct HExtNiR as [HExtEq0 HExtNiR'].
    destruct HExtNiR' as [_ HExtLe].
    eassert (HBoolNiR := fmt_enc_ni (T_Correct _ _ bool_format) true bf _ pos _ _ E).
    destruct HBoolNiR as [_ HBoolNiR'].
    destruct HBoolNiR' as [_ HBoolLe].
    eassert (Hb0_bf'_p : EQ.equiv_b _ bf' BProp.pos_zero _ BProp.pos_zero _).
    { eapply EQ.equiv_b_le; [exact HExtEq0|
        apply BProp.pos_zero_le_all|
        apply BProp.pos_zero_le_all|
        exact HSeqLe|
        exact HSeqLe|
        apply BProp.pos_zero_le_all|
        apply BProp.pos_zero_le_all|
        reflexivity|
        reflexivity]. }
    eassert (Hb_bf'_0p : EQ.equiv_b _ bf' BProp.pos_zero _ BProp.pos_zero _).
    { eapply EQ.equiv_b_trans. exact HSeqEq0. exact Hb0_bf'_p. }
    eassert (HBoolParse : T_Parse _ _ bool_format bf' pos = Some (exist _ true _, _, SameVer)).
    { apply (proj2 (fmt_dec_consist (T_Correct _ _ bool_format) true _ pos _ _ SameVer HBoolSurj)).
      apply equiv_b_le_zero. exact HBoolLe. exact Hb_bf'_0p. }
    eassert (HSeqSurj := AllSeqSurj a_seq _ _ _ _ _ E0).
    eassert (HSeqParse : seq_parse l par bf' _ = Some (exist _ a_seq _, _, SameVer)).
    { apply (proj2 (AllSeqDec a_seq _ _ _ _ SameVer HSeqSurj)).
      apply equiv_b_le_zero. exact HSeqLe. exact HExtEq0. }
    eassert (HExtSurj := AllExtSurj a_ext _ bf' _ _ _ E1).
    unfold seq_ext_parse, bind_parse, return_parse.
    rewrite HBoolParse. simpl.
    rewrite HSeqParse. simpl.
    rewrite HExtSurj. simpl.
    destruct (check_all_none_dec ext a_ext) as [pf_none|pf_not2].
    + contradiction.
    + decode_eq.
Qed.

(* ------------------------------------------------------------------ *)
(* Sub-lemma 5: format_correct_inj_same                               *)
(* ------------------------------------------------------------------ *)

Lemma seq_ext_full_inj_same
  (l : list seq_elem) (fmt : seq_format_prod l)
  (ext : list typ) (fmt_ext : get_formats ext)
  : format_correct_inj_same _ _
      (seq_ext_serialize l
         (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) ext
         (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
         (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len))
      (seq_ext_parse l
         (fmt_to_seq_prod l fmt Parse T_Parse read_unit) ext
         (fmt_to_prod ext fmt_ext Parse T_Parse read_unit)).
Proof.
  set (ser := fmt_to_seq_prod l fmt Serialize T_Serial put_unit).
  set (par := fmt_to_seq_prod l fmt Parse T_Parse read_unit).
  set (ser_ext := fmt_to_prod ext fmt_ext Serialize T_Serial put_unit).
  set (par_ext := fmt_to_prod ext fmt_ext Parse T_Parse read_unit).
  set (len_prod := fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len).
  pose proof (seq_fmt_cond_enc_ni l fmt) as SeqNiC.
  pose proof (seq_fmt_cond_inj_same l fmt) as SeqInjC.
  pose proof (ext_fmt_cond_enc_ni ext fmt_ext) as ExtNiC.
  pose proof (ext_fmt_cond_len_c ext fmt_ext) as ExtLenC.
  pose proof (ext_fmt_cond_inj_same ext fmt_ext) as ExtInjC.
  pose proof (seq_enc_non_inter l ser SeqNiC) as AllSeqNi.
  pose proof (seq_inj_same l ser par SeqNiC SeqInjC) as AllSeqInj.
  pose proof (seq_ext_inj_same ext ser_ext par_ext len_prod ExtNiC ExtLenC ExtInjC) as AllExtInj.
  pose proof (ext_serialize_non_inter ext ser_ext len_prod ExtNiC) as AllExtNi.
  unfold format_correct_inj_same.
  intros [a_seq a_ext] bf pos pos' pf H bf0 H_len.
  unfold seq_ext_parse, bind_parse in H.
  destruct (T_Parse _ _ bool_format bf pos) as [H_bool_r|] eqn:EBool; [|discriminate].
  destruct H_bool_r as [H_bool_sp flg_b].
  destruct H_bool_sp as [H_bool_sig p1].
  destruct H_bool_sig as [b pf_b].
  eassert (Hbsv := bool_parse_SameVer bf pos p1 b pf_b flg_b EBool). subst flg_b.
  destruct b.
  - (* b = true: bool true + seq + ext + not-all-none check *)
    destruct (seq_parse l par bf p1) as [H_seq_r|] eqn:ESeq; [|discriminate].
    destruct H_seq_r as [H_seq_sp flg_seq].
    destruct H_seq_sp as [H_seq_sig p2].
    destruct H_seq_sig as [a_seq' pf_sa].
    destruct (ext_parse ext par_ext bf p2) as [H_ext_r|] eqn:EExt; [|discriminate].
    destruct H_ext_r as [H_ext_sp flg_ext].
    destruct H_ext_sp as [H_ext_sig p3].
    destruct H_ext_sig as [a_ext' pf_se].
    destruct (check_all_none_dec ext a_ext') as [|pf_not]; [discriminate|].
    unfold return_parse in H.
    inversion H. subst. clear H.
    match goal with
    | H_flg : flg_add flg_seq flg_ext = SameVer |- _ =>
        destruct (flg_add_to_same flg_seq flg_ext H_flg); subst
    end.
    (* bool inj; after subst, a_seq'→a_seq, a_ext'→a_ext, p3→pos' *)
    eassert (HBoolInj := fmt_inj_same (T_Correct _ _ bool_format)
               true bf pos p1 pf_b EBool bf0 H_len).
    destruct HBoolInj as [bf1 HBool12].
    destruct HBool12 as [HBool1 HBoolEq].
    eassert (HBoolLen : BA.len bf0 = BA.len bf1).
    { exact (same_len_after_enc _ (fmt_enc_ni (T_Correct _ _ bool_format)) HBool1). }
    assert (H_len1 : BA.len bf1 = BA.len bf) by lia.
    (* seq inj *)
    eassert (HSeqInj := AllSeqInj a_seq bf p1 p2 pf_sa ESeq bf1 H_len1).
    destruct HSeqInj as [bf2 HSeq12].
    destruct HSeq12 as [HSeq1 HSeqEq].
    eassert (HSeqLen : BA.len bf1 = BA.len bf2).
    { exact (same_len_after_enc _ AllSeqNi HSeq1). }
    assert (H_len2 : BA.len bf2 = BA.len bf) by lia.
    (* ext inj *)
    eassert (HExtInj := AllExtInj a_ext bf p2 pos' pf_se EExt bf2 H_len2).
    destruct HExtInj as [bf3 HExt12].
    destruct HExt12 as [HExt1 HExtEq].
    (* non-inter for combining equiv_b *)
    eassert (HNiSeq := AllSeqNi a_seq bf1 bf2 p1 p2 pf_sa HSeq1).
    destruct HNiSeq as [HNiSeqBef HNiSeqRest].
    eassert (HNiExt := AllExtNi a_ext bf2 bf3 p2 pos' pf_se HExt1).
    destruct HNiExt as [HNiExtBef HNiExtRest].
    exists bf3. split.
    + unfold seq_ext_serialize, bool_enc. simpl fst. simpl snd.
      destruct (check_all_none_dec ext a_ext) as [pf_all|pf_not2].
      * contradiction.
      * rewrite HBool1. rewrite HSeq1. rewrite HExt1. encode_eq.
    + eapply format_correct_inj_helper.
      { eapply format_correct_inj_helper.
        { exact HBoolEq. }
        { exact HSeqEq. }
        { exact HNiSeqBef. } }
      { exact HExtEq. }
      { exact HNiExtBef. }
  - (* b = false: bool false + seq only, returns all-none ext *)
    destruct (seq_parse l par bf p1) as [H_seq_r|] eqn:ESeq; [|discriminate].
    destruct H_seq_r as [H_seq_sp flg_seq].
    destruct H_seq_sp as [H_seq_sig p2].
    destruct H_seq_sig as [a_seq' pf_sa].
    unfold return_parse in H.
    inversion H. subst. clear H.
    (* bool inj; after subst, a_seq'→a_seq, p2→pos', a_ext→ext_all_none ext *)
    eassert (HBoolInj := fmt_inj_same (T_Correct _ _ bool_format)
               false bf pos p1 pf_b EBool bf0 H_len).
    destruct HBoolInj as [bf1 HBool12].
    destruct HBool12 as [HBool1 HBoolEq].
    eassert (HBoolLen : BA.len bf0 = BA.len bf1).
    { exact (same_len_after_enc _ (fmt_enc_ni (T_Correct _ _ bool_format)) HBool1). }
    assert (H_len1 : BA.len bf1 = BA.len bf) by lia.
    (* seq inj *)
    eassert (HSeqInj := AllSeqInj a_seq bf p1 pos' pf_sa ESeq bf1 H_len1).
    destruct HSeqInj as [bf2 HSeq12].
    destruct HSeq12 as [HSeq1 HSeqEq].
    eassert (HNiSeq := AllSeqNi a_seq bf1 bf2 p1 pos' pf_sa HSeq1).
    destruct HNiSeq as [HNiSeqBef HNiSeqRest].
    exists bf2. split.
    + unfold seq_ext_serialize, bool_enc. simpl fst. simpl snd.
      destruct (check_all_none_dec ext (ext_all_none ext)) as [pf_all|pf_not].
      * rewrite HBool1. rewrite HSeq1. encode_eq.
      * exfalso. apply pf_not. exact (ext_all_none_is_all_none ext).
    + eapply format_correct_inj_helper.
      { exact HBoolEq. }
      { exact HSeqEq. }
      { exact HNiSeqBef. }
Qed.

(* ------------------------------------------------------------------ *)
(* Sub-lemma 6: format_correct_inj_diff                               *)
(* ------------------------------------------------------------------ *)

Lemma seq_ext_full_inj_diff
  (l : list seq_elem) (fmt : seq_format_prod l)
  (ext : list typ) (fmt_ext : get_formats ext)
  (len_ext : length2 ext < Nat.pow 2 14)
  : format_correct_inj_diff _ _
      (seq_ext_serialize l
         (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) ext
         (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
         (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len))
      (seq_ext_parse l
         (fmt_to_seq_prod l fmt Parse T_Parse read_unit) ext
         (fmt_to_prod ext fmt_ext Parse T_Parse read_unit))
      (seq_ext_to_len0 l
         (fmt_to_seq_prod_no_cond l fmt (fun X => X -> option nat) T_to_len unit_to_len) ext
         (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len)).
Proof.
  unfold format_correct_inj_diff.
  intros [a_seq a_ext] bf pos pos' pf flg H.
  set (ser     := fmt_to_seq_prod l fmt Serialize T_Serial put_unit).
  set (par     := fmt_to_seq_prod l fmt Parse T_Parse read_unit).
  set (ser_ext := fmt_to_prod ext fmt_ext Serialize T_Serial put_unit).
  set (par_ext := fmt_to_prod ext fmt_ext Parse T_Parse read_unit).
  set (tl      := fmt_to_seq_prod_no_cond l fmt (fun X => X -> option nat) T_to_len unit_to_len).
  set (tl_ext  := fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len).
  pose proof (seq_fmt_cond_enc_ni   l fmt)       as SeqNiC.
  pose proof (seq_fmt_cond_len_c    l fmt)       as SeqLenC.
  pose proof (seq_fmt_cond_inj_diff l fmt)       as SeqInjC.
  pose proof (ext_fmt_cond_enc_ni   ext fmt_ext) as ExtNiC.
  pose proof (ext_fmt_cond_len_c    ext fmt_ext) as ExtLenC.
  pose proof (ext_fmt_cond_inj_diff ext fmt_ext) as ExtInjC.
  pose proof (seq_inj_diff l ser par tl SeqNiC SeqLenC SeqInjC) as AllSeqInjDiff.
  pose proof (seq_to_len_correct l ser par tl SeqNiC SeqLenC)   as AllSeqLen.
  pose proof (seq_enc_non_inter l ser SeqNiC)                                               as AllSeqNi.
  unfold seq_ext_parse, bind_parse in H.
  destruct (T_Parse _ _ bool_format bf pos) as [H_bool_r|] eqn:EBool; [|discriminate].
  destruct H_bool_r as [H_bool_sp flg_b].
  destruct H_bool_sp as [H_bool_sig p1].
  destruct H_bool_sig as [b pf_b].
  eassert (BoolInjApp := fmt_inj_diff (T_Correct _ _ bool_format) b bf pos p1 pf_b flg_b EBool).
  destruct BoolInjApp as [min_b H_bool_inj].
  destruct b.
  - (* b = true: seq + ext + not-all-none check *)
    fold par in H.
    destruct (seq_parse l par bf p1) as [H_seq_r|] eqn:ESeq; [|discriminate].
    destruct H_seq_r as [H_seq_sp flg_seq].
    destruct H_seq_sp as [H_seq_sig p2].
    destruct H_seq_sig as [a_seq' pf_sa].
    fold par_ext in H.
    destruct (ext_parse ext par_ext bf p2) as [H_ext_r|] eqn:EExt; [|discriminate].
    destruct H_ext_r as [H_ext_sp flg_ext].
    destruct H_ext_sp as [H_ext_sig p3].
    destruct H_ext_sig as [a_ext' pf_se].
    destruct (check_all_none_dec ext a_ext') as [|pf_not]; [discriminate|].
    unfold return_parse in H. inversion H. subst. clear H.
    (* after subst: a_seq'→a_seq, a_ext'→a_ext, p3→pos' *)
    (* Handle ext = [] case: pf_not : ~ check_all_none [] a_ext = ~ True → contradiction *)
    destruct (Compare_dec.zerop (length2 ext)) as [Hlen0 | Hlen_pos].
    { destruct ext; [| discriminate].
      exfalso. apply pf_not. exact I. }
    assert (H1le : 1 <= length2 ext) by lia.
    eassert (G_ns_ex := proj2 AllSeqLen a_seq bf p1 p2 pf_sa flg_seq ESeq).
    destruct G_ns_ex as [n_s G_ns].
    eassert (G_ne_ex := proj2 (seq_ext_to_len_correct ext (conj H1le len_ext) ser_ext par_ext tl_ext ExtNiC ExtLenC) a_ext bf p2 pos' pf_se flg_ext EExt).
    destruct G_ne_ex as [n_e G_ne].
    eassert (SeqInj := AllSeqInjDiff a_seq bf p1 p2 pf_sa flg_seq ESeq).
    destruct SeqInj as [min_s H_seq_inj].
    eassert (ExtInj := (seq_ext_inj_diff ext (conj H1le len_ext) ser_ext par_ext tl_ext ExtNiC ExtLenC ExtInjC) a_ext bf p2 pos' pf_se flg_ext EExt).
    destruct ExtInj as [min_e H_ext_inj].
    exists (min_b + min_s + min_e).
    intros pos0 bf0 Hlen.
    unfold seq_ext_to_len0. simpl fst. simpl snd.
    destruct (check_all_none_dec ext a_ext) as [pf_none|pf_not2]. { contradiction. }
    rewrite G_ns, G_ne. simpl.
    (* bool inj *)
    assert (L1 : BA.to_nat pos0 + min_b <= BA.len bf0). { lia. }
    apply H_bool_inj in L1. 
    destruct L1 as [H_not_b | (bf1 & p1' & HBool1 & HBool1len)].
    { exfalso. apply H_not_b.
      assert (Hb : T_to_len _ _ bool_format true = Some 1) by reflexivity.
      rewrite Hb. simpl. unfold get_byte_len. simpl. lia. }
    eassert (HBoolLen : BA.len bf0 = BA.len bf1).
    { exact (same_len_after_enc _ (fmt_enc_ni (T_Correct _ _ bool_format)) HBool1). }
    (* seq inj *)
    assert (L2 : BA.to_nat p1' + min_s <= BA.len bf1). { lia. }
    apply H_seq_inj in L2.
    destruct L2 as [H_not_s | (bf2 & p2' & HSeq1 & HSeq1len)].
    { left. rewrite G_ns in H_not_s. simpl in H_not_s. solve_monotone. }
    eassert (HSeqLen : BA.len bf1 = BA.len bf2).
    { exact (same_len_after_enc _ AllSeqNi HSeq1). }
    (* ext inj *)
    assert (L3 : BA.to_nat p2' + min_e <= BA.len bf2). { lia. }
    apply H_ext_inj in L3.
    destruct L3 as [H_not_e | (bf3 & p3' & HExt1 & HExt1len)].
    { left. rewrite G_ne in H_not_e. simpl in H_not_e. solve_monotone. }
    (* combine *)
    right. exists bf3. exists p3'.
    split.
    + unfold seq_ext_serialize, bool_enc. simpl fst. simpl snd.
      destruct (check_all_none_dec ext a_ext) as [|pf_not3]. { contradiction. }
      rewrite HBool1. rewrite HSeq1. rewrite HExt1. encode_eq.
    + lia.
  - (* b = false: seq only, returns all-none ext *)
    fold par in H.
    destruct (seq_parse l par bf p1) as [H_seq_r|] eqn:ESeq; [|discriminate].
    destruct H_seq_r as [H_seq_sp flg_seq].
    destruct H_seq_sp as [H_seq_sig p2].
    destruct H_seq_sig as [a_seq' pf_sa].
    unfold return_parse in H. inversion H. subst. clear H.
    (* after subst: a_seq'→a_seq, a_ext→ext_all_none ext, p2→pos', flg_seq→flg *)
    eassert (G_ns_ex := proj2 AllSeqLen a_seq bf p1 pos' pf_sa flg ESeq).
    destruct G_ns_ex as [n_s G_ns].
    eassert (SeqInj := AllSeqInjDiff a_seq bf p1 pos' pf_sa flg ESeq).
    destruct SeqInj as [min_s H_seq_inj].
    exists (min_b + min_s).
    intros pos0 bf0 Hlen.
    unfold seq_ext_to_len0. simpl fst. simpl snd.
    destruct (check_all_none_dec ext (ext_all_none ext)) as [pf_none|pf_not].
    + rewrite G_ns. simpl.
      assert (L1 : BA.to_nat pos0 + min_b <= BA.len bf0). { lia. }
      apply H_bool_inj in L1.
      destruct L1 as [H_not_b | (bf1 & p1' & HBool1 & HBool1len)].
      { exfalso. apply H_not_b.
        assert (Hb : T_to_len _ _ bool_format false = Some 1) by reflexivity.
        rewrite Hb. simpl. unfold get_byte_len. simpl. lia. }
      eassert (HBoolLen : BA.len bf0 = BA.len bf1).
      { exact (same_len_after_enc _ (fmt_enc_ni (T_Correct _ _ bool_format)) HBool1). }
      assert (L2 : BA.to_nat p1' + min_s <= BA.len bf1). { lia. }
      apply H_seq_inj in L2.
      destruct L2 as [H_not_s | (bf2 & p2' & HSeq1 & HSeq1len)].
      { left. rewrite G_ns in H_not_s. simpl in H_not_s. solve_monotone. }
      right. exists bf2. exists p2'.
      split.
      * unfold seq_ext_serialize, bool_enc. simpl fst. simpl snd.
        destruct (check_all_none_dec ext (ext_all_none ext)) as [pf_none'|pf_not'].
        -- rewrite HBool1. rewrite HSeq1. encode_eq.
        -- exfalso. apply pf_not'. exact (ext_all_none_is_all_none ext).
      * lia.
    + exfalso. apply pf_not. exact (ext_all_none_is_all_none ext).
Qed.

(* ------------------------------------------------------------------ *)
(* Sub-lemma 7: format_to_len_correct                                 *)
(* ------------------------------------------------------------------ *)

Lemma seq_ext_full_len_correct
  (l : list seq_elem) (fmt : seq_format_prod l)
  (ext : list typ) (fmt_ext : get_formats ext)
  (len_ext : length2 ext < Nat.pow 2 14)
  : format_to_len_correct _ _
      (seq_ext_serialize l
         (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) ext
         (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
         (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len))
      (seq_ext_parse l
         (fmt_to_seq_prod l fmt Parse T_Parse read_unit) ext
         (fmt_to_prod ext fmt_ext Parse T_Parse read_unit))
      (seq_ext_to_len0 l
         (fmt_to_seq_prod_no_cond l fmt (fun X => X -> option nat) T_to_len unit_to_len) ext
         (fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len)).
Proof.
  set (ser     := fmt_to_seq_prod l fmt Serialize T_Serial put_unit).
  set (par     := fmt_to_seq_prod l fmt Parse T_Parse read_unit).
  set (ser_ext := fmt_to_prod ext fmt_ext Serialize T_Serial put_unit).
  set (par_ext := fmt_to_prod ext fmt_ext Parse T_Parse read_unit).
  set (tl      := fmt_to_seq_prod_no_cond l fmt (fun X => X -> option nat) T_to_len unit_to_len).
  set (tl_ext  := fmt_to_prod_no_cond ext fmt_ext (fun T => T -> option nat) T_to_len unit_to_len).
  pose proof (seq_fmt_cond_enc_ni l fmt)   as SeqNiC.
  pose proof (seq_fmt_cond_len_c  l fmt)   as SeqLenC.
  pose proof (ext_fmt_cond_enc_ni ext fmt_ext)  as ExtNiC.
  pose proof (ext_fmt_cond_len_c  ext fmt_ext)  as ExtLenC.
  pose proof (seq_to_len_correct  l ser par tl SeqNiC SeqLenC) as AllSeqLen.
  pose proof (seq_enc_non_inter   l ser SeqNiC) as AllSeqNi.
  pose proof (ext_serialize_non_inter ext ser_ext tl_ext ExtNiC) as AllExtNi.
  unfold format_to_len_correct. split.
  - (* Part 1: encode → to_len = Some exact *)
    intros [a_seq a_ext] bf bf' pos pos' pf H.
    unfold seq_ext_serialize in H. simpl fst in H. simpl snd in H.
    unfold seq_ext_to_len0. simpl fst. simpl snd.
    destruct (check_all_none_dec ext a_ext) as [pf_none|pf_not].
    + (* all-none: bool(false) + seq *)
      repeat destruct_enc. inversion H. subst. clear H.
      eassert (G_bool := proj1 (fmt_len_c (T_Correct _ _ bool_format)) _ _ _ _ _ _ E).
      eassert (G_seq  := proj1 AllSeqLen _ _ _ _ _ _ E0).
      eassert (NI_bool := fmt_enc_ni (T_Correct _ _ bool_format) _ _ _ _ _ _ E). split_and.
      eassert (NI_seq  := AllSeqNi _ _ _ _ _ _ E0). split_and.
      assert (Hb1 : T_to_len _ _ bool_format false = Some 1) by reflexivity.
      rewrite Hb1 in G_bool. inversion G_bool. clear G_bool.
      rewrite G_seq. simpl. f_equal. unfold BProp.le_pos in *. lia.
    + (* not-all-none: bool(true) + seq + ext *)
      repeat destruct_enc. inversion H. subst. clear H.
      (* ext = [] case: pf_not : ~ True → contradiction *)
      destruct (Compare_dec.zerop (length2 ext)) as [Hlen0 | Hlen_pos].
      { destruct ext; [| discriminate].
        exfalso. apply pf_not. exact I. }
      assert (H1le : 1 <= length2 ext) by lia.
      eassert (AllExtLen_here := seq_ext_to_len_correct ext (conj H1le len_ext) ser_ext par_ext tl_ext ExtNiC ExtLenC).
      eassert (G_bool := proj1 (fmt_len_c (T_Correct _ _ bool_format)) _ _ _ _ _ _ E).
      eassert (G_seq  := proj1 AllSeqLen _ _ _ _ _ _ E0).
      eassert (G_ext  := proj1 AllExtLen_here _ _ _ _ _ _ E1).
      eassert (NI_bool := fmt_enc_ni (T_Correct _ _ bool_format) _ _ _ _ _ _ E). split_and.
      eassert (NI_seq  := AllSeqNi _ _ _ _ _ _ E0). split_and.
      eassert (NI_ext  := AllExtNi _ _ _ _ _ _ E1). split_and.
      assert (Hb1 : T_to_len _ _ bool_format true = Some 1) by reflexivity.
      rewrite Hb1 in G_bool. inversion G_bool. clear G_bool.
      rewrite G_seq, G_ext. simpl. f_equal. unfold BProp.le_pos in *. lia.
  - (* Part 2: decode → ∃n, to_len = Some n *)
    intros [a_seq a_ext] bf pos pos' pf flg H.
    unfold seq_ext_parse, bind_parse in H.
    destruct (T_Parse _ _ bool_format bf pos) as [H_bool_r|] eqn:EBool; [|discriminate].
    destruct H_bool_r as [H_bool_sp flg_b].
    destruct H_bool_sp as [H_bool_sig p1].
    destruct H_bool_sig as [b pf_b].
    unfold seq_ext_to_len0. simpl fst. simpl snd.
    destruct b.
    + (* b = true: seq + ext + not-all-none check *)
      destruct (seq_parse l par bf p1) as [H_seq_r|] eqn:ESeq; [|discriminate].
      destruct H_seq_r as [H_seq_sp flg_seq].
      destruct H_seq_sp as [H_seq_sig p2].
      destruct H_seq_sig as [a_seq' pf_sa].
      destruct (ext_parse ext par_ext bf p2) as [H_ext_r|] eqn:EExt; [|discriminate].
      destruct H_ext_r as [H_ext_sp flg_ext].
      destruct H_ext_sp as [H_ext_sig p3].
      destruct H_ext_sig as [a_ext' pf_se].
      destruct (check_all_none_dec ext a_ext') as [|pf_not]; [discriminate|].
      unfold return_parse in H. inversion H. subst. clear H.
      destruct (check_all_none_dec ext a_ext) as [pf_none|pf_not2].
      { contradiction. }
      (* ext = [] case: pf_not2 : ~ True → contradiction *)
      destruct (Compare_dec.zerop (length2 ext)) as [Hlen0 | Hlen_pos].
      { destruct ext; [| discriminate].
        exfalso. apply pf_not2. exact I. }
      assert (H1le : 1 <= length2 ext) by lia.
      eassert (AllExtLen_here2 := seq_ext_to_len_correct ext (conj H1le len_ext) ser_ext par_ext tl_ext ExtNiC ExtLenC).
      eassert (G_seq := proj2 AllSeqLen _ _ _ _ _ _ ESeq).
      eassert (G_ext := proj2 AllExtLen_here2 _ _ _ _ _ _ EExt).
      destruct G_seq as [n_s G_s]. destruct G_ext as [n_e G_e].
      rewrite G_s, G_e. simpl. eauto.
    + (* b = false: seq only, returns all-none *)
      destruct (seq_parse l par bf p1) as [H_seq_r|] eqn:ESeq; [|discriminate].
      destruct H_seq_r as [H_seq_sp flg_seq].
      destruct H_seq_sp as [H_seq_sig p2].
      destruct H_seq_sig as [a_seq' pf_sa].
      unfold return_parse in H. inversion H. subst. clear H.
      destruct (check_all_none_dec ext (ext_all_none ext)) as [pf_none|pf_not].
      { eassert (G_seq := proj2 AllSeqLen _ _ _ _ _ _ ESeq).
        destruct G_seq as [n_s G_s]. rewrite G_s. simpl. eauto. }
      { exfalso. apply pf_not. exact (ext_all_none_is_all_none ext). }
Qed.

(* ------------------------------------------------------------------ *)
(* Main: seq_ext_format_correct                                        *)
(* ------------------------------------------------------------------ *)

Lemma seq_ext_format_correct
  (l : list seq_elem) (fmt : seq_format_prod l)
  (ext : list typ) (fmt_ext : get_formats ext)
  (len_ext : length2 ext < Nat.pow 2 14)
  : format_correct
      (seq_ext_serialize l
         (fmt_to_seq_prod l fmt Serialize T_Serial put_unit) ext
         (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
         (fmt_to_prod_no_cond ext fmt_ext (fun T : Set => T -> option nat)
            T_to_len unit_to_len))
      (seq_ext_parse l (fmt_to_seq_prod l fmt Parse T_Parse read_unit) ext
         (fmt_to_prod ext fmt_ext Parse T_Parse read_unit))
      (seq_ext_to_len0 l
         (fmt_to_seq_prod_no_cond l fmt (fun X : Set => X -> option nat)
            T_to_len unit_to_len) ext
         (fmt_to_prod_no_cond ext fmt_ext (fun T : Set => T -> option nat)
            T_to_len unit_to_len)).
Proof.
  unfold format_correct.
  exact (conj (seq_ext_full_enc_consist l fmt ext fmt_ext)
         (conj (seq_ext_full_dec_consist l fmt ext fmt_ext)
          (conj (seq_ext_full_enc_ni l fmt ext fmt_ext)
           (conj (seq_ext_full_surj l fmt ext fmt_ext)
            (conj (seq_ext_full_inj_same l fmt ext fmt_ext)
             (conj (seq_ext_full_inj_diff l fmt ext fmt_ext len_ext)
                   (seq_ext_full_len_correct l fmt ext fmt_ext len_ext))))))).
Qed.


Definition seq_ext_format
  (l : list seq_elem)
  (fmt : seq_format_prod l)
  (ext : list typ)
  (fmt_ext : get_formats ext)
  (len_ext : length2 ext < Nat.pow 2 14)
  (*  : T_Format (seq_type l * seq_ext_type ext)
      (fun z => seq_cond l (fst z) /\ (seq_ext_cond ext) (snd z)) *) :=
  mk_format
    _ _
    (seq_ext_serialize
       l
       (fmt_to_seq_prod l fmt Serialize T_Serial put_unit)
       ext
       (fmt_to_prod ext fmt_ext Serialize T_Serial put_unit)
       (fmt_to_prod_no_cond ext fmt_ext _ (T_to_len) unit_to_len))
   (seq_ext_parse
       l
       (fmt_to_seq_prod l fmt Parse T_Parse read_unit)
       ext
       (fmt_to_prod ext fmt_ext Parse T_Parse read_unit))
   (seq_ext_to_len0
      l
      (fmt_to_seq_prod_no_cond l fmt (fun X => X -> option nat)
                       T_to_len unit_to_len)
      ext
      (fmt_to_prod_no_cond ext fmt_ext _ (T_to_len) unit_to_len))
   (seq_ext_format_correct l fmt ext fmt_ext len_ext).



