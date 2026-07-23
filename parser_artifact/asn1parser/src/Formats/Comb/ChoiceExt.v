Require Import
          ASN1Parser.Formats.Comb
          ASN1Parser.Formats.CombFormat
          ASN1Parser.Array.ByteBuffer
          ASN1Parser.Formats.Term.OctetString
          ASN1Parser.Formats.Term.NonNeg
          
          ASN1Parser.Formats.Comb.SeqProd
          ASN1Parser.Formats.Comb.Choice
          ASN1Parser.Formats.Comb.OpenType
          ASN1Parser.Formats.Comb.HelperComb
          ASN1Parser.tact.


(* Here, first encode a normally small integer to indicate
   which extension it is using to indicate which one to choose,
   then encode with OpenType.

   Here, we make it a Option type, to indicate the case when
   it is a new version that the extension is not comprehended.
 *)

(* For choice extension, it could be a choice ext type,
   or it could be an unknown extension, which consists of
   a choice number and a list of byte, which is encoded
   using octet_string_no_cons_format.
 *)
Inductive choice_ext_typ (t : Set) :=
| known_ext (c : t) : choice_ext_typ t
| unknown_ext (n : nat) (ct : list Byte.byte) : choice_ext_typ t.

Arguments known_ext {t} _.
Arguments unknown_ext {t} _ _.

Definition choice_ext_cond {t : Set} (l : nat) (td : t -> Prop)
  (ce : choice_ext_typ t) : Prop :=
  match ce with
  | known_ext c => td c
  | unknown_ext n ct =>
      (* Unknown extensions keep the discriminant and the raw octets. *)
      (l <= n) /\ (length ct < Nat.pow 2 14)
  end.


Definition os_enc := T_Serial _ _ octet_string_no_cons_format.
Definition os_dec := T_Parse _ _  octet_string_no_cons_format. 
Definition os_to_len := T_to_len _ _ octet_string_no_cons_format.

Definition os_typ :=  {{ list Byte.byte | (fun bs : list Byte.byte => length bs < Nat.pow 2 14 )}}.
Definition os_cond :=  (fun bs : list Byte.byte => length bs < Nat.pow 2 14 ). 

Definition get_nth_typ_ce (l : list typ) (n : nat) : typ :=
  (List.nth n l os_typ).

Definition choice_ext (l : list typ) :=
  {n : nat & typ_set (get_nth_typ_ce l n)}.

Definition choice_cond_ext (l : list typ) : choice_ext l -> Prop := 
  fun c =>
    let n := projT1 c in
    typ_cond (get_nth_typ_ce l n) (projT2 c).

(* For choice extension only *)
Definition get_nth_serial_ce (l : list typ) :=
  get_nth_prod l (fun t : typ => Serialize (typ_set t) (typ_cond t)) os_typ.

Definition get_nth_parse_ce (l : list typ) :=
  get_nth_prod l (fun t => Parse (typ_set t) (typ_cond t)) os_typ.

Definition get_nth_to_len_ce (l : list typ) :=
  get_nth_prod l (fun t => (typ_set t) -> option nat) os_typ.

Definition get_format_prodce (l : list typ) :=
  list_to_prod l (fun t => T_Format (typ_set t) (typ_cond t)) os_typ. 

Definition get_serial_prodce (l : list typ) :=
  list_to_prod l (fun t => Serialize (typ_set t) (typ_cond t)) os_typ.

Definition get_parse_prodce (l : list typ) :=
  list_to_prod l (fun t => Parse (typ_set t) (typ_cond t)) os_typ.

Definition get_to_len_prodce (l : list typ) :=
  list_to_prod l (fun t => (typ_set t) -> option nat) os_typ.

Definition choice_ext_serial (ext : list typ)
  (ser : get_serial_prodc ext)
  (tl : get_to_len_prodc ext)
  : Serialize (choice_ext_typ (choice ext))
      (choice_ext_cond (length ext) (choice_cond ext)) :=
  fun bf pos ce =>
    match ce as ce0
          return option (BitRep.BA.Buffer * BitRep.BA.Pos *
                           choice_ext_cond (length ext) (choice_cond ext) ce0) with
    | known_ext c =>
        let n := projT1 c in
        match (T_Serial _ _ small_integer_format) bf pos n with
        | Some (bf', pos', _) =>
            if (Nat.ltb n (length ext)) then
              open_typ_serialize
                (get_nth_serial ext ser n)
                (get_nth_to_len ext tl n)
                bf' pos' (projT2 c)
            else
              None
        | None => None
        end
    | unknown_ext n ct =>
        match (T_Serial _ _ small_integer_format) bf pos n with
        | Some (bf', pos', _) =>
            match Nat.leb (length ext) n as b
                  return (Nat.leb (length ext) n = b ->
                          option (BitRep.BA.Buffer * BitRep.BA.Pos *
                                    choice_ext_cond (length ext) (choice_cond ext)
                                      (unknown_ext n ct))) with
            | true =>
                fun h_le =>
                  match os_enc bf' pos' ct with
                  | Some (bf'', pos'', pf_ct) =>
                      Some (bf'', pos'', conj (proj1 (PeanoNat.Nat.leb_le _ _) h_le) pf_ct)
                  | None => None
                  end
            | false => fun _ => None
            end eq_refl
        | None => None
        end
    end.

(* Given the choice n in advance *)
Definition choice_ext_parse (ext : list typ)
  (par : get_parse_prodc ext)
  : Parse (choice_ext_typ (choice ext))
      (choice_ext_cond (length ext) (choice_cond ext)) :=
  bind_parse
    (T_Parse _ _ small_integer_format)
    (fun n _ _ =>
       match Compare_dec.le_gt_dec (length ext) n with
       | left h_le =>
           bind_parse os_dec
             (fun ct pf_ct flg =>
                return_parse
                  (exist _ (unknown_ext n ct)
                     (conj h_le pf_ct))
                  flg)
       | right h_lt =>
           bind_parse
             (open_typ_parse (get_nth_parse ext par n))
             (fun v pf_v flg =>
                return_parse
                  (exist _ (known_ext (existT (fun n0 => typ_set (get_nth_typ ext n0)) n v))
                     pf_v)
                  flg)
       end).

(* First add the length of small enc *)

Definition choice_ext_to_len (ext : list typ)
  (tl : get_to_len_prodc ext)
  (ce : choice_ext_typ (choice ext)) : option nat :=
  match ce with
  | known_ext c =>
      let n := projT1 c in
      add_opt (T_to_len _ _ small_integer_format n)
        (if (Nat.ltb n (length ext))
         then open_type_to_len (get_nth_to_len ext tl n) (projT2 c)
         else None)
  | unknown_ext n ct =>
      if Nat.leb (length ext) n
      then add_opt (T_to_len _ _ small_integer_format n) (os_to_len ct)
      else None
  end.

Require Import ASN1Parser.Formats.Comb.ChoiceProp.
Require Import ASN1Parser.Formats.Comb.OpenTypeProp.
Require Import ASN1Parser.Formats.CombProp.
Require Import ASN1Parser.Formats.SameVerProp.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.ProofIrrelevance Lia.

Lemma length2_length {A : Type} (l : list A) : length2 l = length l.
Proof. induction l; simpl; auto. Qed.

Lemma small_integer_parse_SameVer : parse_to_SameVer (T_Parse _ _ small_integer_format).
Proof.
  unfold small_integer_format.
  apply restrict_SameVer. apply basic_bit_SameVer.
Qed.

Lemma choice_ext_enc_non_inter (ext : list typ)
  (ser : get_serial_prodc ext)
  (tl : get_to_len_prodc ext)
  (ni_prod : get_cond_prodc ext ser encode_non_inter) :
  encode_non_inter _ _ (choice_ext_serial ext ser tl).
Proof.
  unfold encode_non_inter.
  intros [c | n ct] bf bf' pos pos' pf H.
  - (* known_ext c *)
    unfold choice_ext_serial in H.
    destruct (T_Serial _ _ small_integer_format bf pos (projT1 c))
      as [ [[b p] pf_n] | ] eqn:E1; [| discriminate].
    destruct (Nat.ltb (projT1 c) (length ext)) eqn:Hlt; [| discriminate].
    apply Nat.ltb_lt in Hlt.
    assert (Hlt2 : projT1 c < length2 ext). { rewrite length2_length. exact Hlt. }
    eassert (NI1 := fmt_enc_ni (T_Correct _ _ small_integer_format) _ bf b pos p pf_n E1).
    eassert (ni_n := get_nth_cond_prod ext ser encode_non_inter (projT1 c) Hlt2 ni_prod).
    eassert (NI2 := open_type_non_inter _ _ ni_n _ b bf' p pos' pf H).
    eapply append_non_inter_proof_helper; [apply NI1 | apply NI2].
  - (* unknown_ext n ct *)
    unfold choice_ext_serial in H.
    
    destruct (T_Serial _ _ small_integer_format bf pos n)
      as [ [[b p] pf_n] | ] eqn:E1; [| discriminate]. 
    set (H_leb := Nat.leb_le (length ext) n) in *.
    clearbody H_leb.
    
    
    destruct (Nat.leb (length ext) n) eqn:Hle; [| discriminate].           
    destruct (os_enc b p ct) as [ [[bf'' pos''] pf_ct] | ] eqn:E2; [| discriminate].
    inversion H. subst. clear H.
    eassert (NI1 := fmt_enc_ni (T_Correct _ _ small_integer_format) _ bf b pos p pf_n E1). 
    eassert (NI2 := fmt_enc_ni (T_Correct _ _ octet_string_no_cons_format) _ _ _ _ _ _  E2).
    eapply append_non_inter_proof_helper; [apply NI1 | apply NI2].
Qed. 

Lemma choice_ext_enc_consist (ext : list typ)
  (ser : get_serial_prodc ext)
  (tl : get_to_len_prodc ext)
  (ni_prod : get_cond_prodc ext ser encode_non_inter)
  (ec_prod : get_cond_prodc ext ser encode_consistent) :
  encode_consistent _ _ (choice_ext_serial ext ser tl).
Proof.
  unfold encode_consistent.
  intros [c | n ct] bf bf' pos pos' bf0 bf0' pos0 pos0' pf H H0.
  - (* known_ext c *)
    unfold choice_ext_serial in H, H0.
    destruct (T_Serial _ _ small_integer_format bf pos (projT1 c))
      as [ [[b p] pf_n] | ] eqn:E1; [| discriminate].
    destruct (Nat.ltb (projT1 c) (length ext)) eqn:Hlt; [| discriminate].
    destruct (T_Serial _ _ small_integer_format bf0 pos0 (projT1 c))
      as [ [[b0 p0] pf_n0] | ] eqn:E10; [| discriminate].
    apply Nat.ltb_lt in Hlt.
    assert (Hlt2 : projT1 c < length2 ext). { rewrite length2_length. exact Hlt. }
    
    eassert (EC_si := fmt_enc_consist (T_Correct _ _ small_integer_format)
                        _ bf b pos p bf0 b0 pos0 p0 _ E1).

    eassert (ni_n := get_nth_cond_prod ext ser encode_non_inter (projT1 c) Hlt2 ni_prod).
    eassert (ec_n := get_nth_cond_prod ext ser encode_consistent (projT1 c) Hlt2 ec_prod).
    eassert (EC_ot := open_type_encode_consist _ _ ec_n ni_n _ b bf' p pos' b0 bf0' p0 pos0' pf H H0).
    eassert (NI2 := open_type_non_inter _ _ ni_n _ b bf' p pos' pf H).
    eassert (NI20 := open_type_non_inter _ _ ni_n _ b0 bf0' p0 pos0' pf H0).
    eapply encode_consist_proof_helper.
    + apply EC_ot.
    + exact (proj1 NI2).
    + exact (proj1 NI20).
    + apply EC_si.
      rewrite E10. encode_eq. 
  - (* unknown_ext n ct *)
    unfold choice_ext_serial in H, H0.
    destruct (T_Serial _ _ small_integer_format bf pos n)
      as [ [[b p] pf_n] | ] eqn:E1; [| discriminate].
    set (H_leb := Nat.leb_le (length ext) n) in *.
    clearbody H_leb.
    
    destruct (Nat.leb (length ext) n) eqn:Hle; [| discriminate].
    (*simpl in H, H0.  *)
    destruct (os_enc b p ct) as [ [[bf'' pos''] pf_ct] | ] eqn:E2; [| discriminate].
    destruct (T_Serial _ _ small_integer_format bf0 pos0 n)
      as [ [[b0 p0] pf_n0] | ] eqn:E10; [| discriminate].
    inversion H; subst. clear H. 
    
    (*rewrite E2 in H0. simpl in H0. *)
    destruct (os_enc b0 p0 ct) as [ [[bf0'' pos0''] pf_ct0] | ] eqn:E20; [| discriminate].
    inversion H0. subst. clear H0.
    rewrite (proof_irrelevance _ pf_n0 pf_n) in E10.
    rewrite (proof_irrelevance _ pf_ct0 pf_ct) in E20.
    eassert (EC_si := fmt_enc_consist (T_Correct _ _ small_integer_format)
                        _ bf b pos p bf0 b0 pos0 p0 pf_n E1 E10).  
    eassert (EC_os := fmt_enc_consist (T_Correct _ _ octet_string_no_cons_format)
                        _ b _ p _ b0 _ p0 _ pf_ct E2 E20).
    eassert (NI2 := fmt_enc_ni (T_Correct _ _ octet_string_no_cons_format) _ b _ p _ pf_ct E2).
    eassert (NI20 := fmt_enc_ni (T_Correct _ _ octet_string_no_cons_format) _ b0 _ p0 _  pf_ct E20).
    eapply encode_consist_proof_helper.
    + apply EC_os.
    + exact (proj1 NI2).
    + exact (proj1 NI20).
    + apply EC_si.
Qed.

Lemma choice_ext_dec_consist (ext : list typ)
  (par : get_parse_prodc ext)
  (dc_prod : get_cond_de_prodc ext par decode_consistent) :
  decode_consistent _ _ (choice_ext_parse ext par).
Proof.
  unfold decode_consistent.
  intros. unfold choice_ext_parse in *.
  apply bind_parse_consist.
  - eassert (G := T_Correct _ _ small_integer_format).
    apply fmt_dec_consist in G. auto. 
  - intros n pf_n flg_n.
    destruct (Compare_dec.le_gt_dec (length ext) n).
    + apply bind_parse_consist.
      * eassert (G := T_Correct _ _ octet_string_no_cons_format).
        apply fmt_dec_consist in G. auto. 
      * intros. apply return_parse_consist.
    + apply bind_parse_consist.
      * apply open_type_decode_consist.
        apply get_nth_cond_de_prod.
        { rewrite length2_length. lia.  }
        { exact dc_prod. }
      * intros. apply return_parse_consist.
  - auto.
Qed.

Lemma choice_ext_surj (ext : list typ)
  (ser : get_serial_prodc ext)
  (par : get_parse_prodc ext)
  (tl : get_to_len_prodc ext)
  (ni_prod : get_cond_prodc ext ser encode_non_inter)
  (surj_prod : get_cond_both_prodc ext ser par format_correct_surj)
  (tl_prod : get_cond_tl_prodc ext ser par tl format_to_len_correct)
  (dc_prod : get_cond_de_prodc ext par decode_consistent) :
  format_correct_surj _ _ (choice_ext_serial ext ser tl) (choice_ext_parse ext par).
Proof.
  unfold format_correct_surj.
  intros [c | n ct] bf bf' pos pos' pf H.
  - (* known_ext c *)
    unfold choice_ext_serial in H.
    destruct (T_Serial _ _ small_integer_format bf pos (projT1 c))
      as [ [[b p] pf_n] | ] eqn:E1; [| discriminate].
    destruct (Nat.ltb (projT1 c) (length ext)) eqn:Hlt; [| discriminate].
    apply Nat.ltb_lt in Hlt.
    assert (Hlt2 : projT1 c < length2 ext). { rewrite length2_length. exact Hlt. }
    eassert (G_surj := fmt_surj (T_Correct _ _ small_integer_format) _ bf b pos p pf_n E1).
    eassert (ni_n := get_nth_cond_prod ext ser encode_non_inter (projT1 c) Hlt2 ni_prod).
    eassert (NI2 := open_type_non_inter _ _ ni_n _ b bf' p pos' pf H). 
    eassert (DC_si := fmt_dec_consist (T_Correct _ _ small_integer_format) _ b pos p pf_n SameVer G_surj).
    split_and.
    eassert (equiv_bp : EQ.equiv_b b bf' pos p pos p).
    { apply equiv_b_le_zero.
      - apply H0.
      - apply H2.  }
    eassert (G_si := H1 bf' pos p equiv_bp).
    unfold choice_ext_parse, bind_parse. rewrite G_si.
    destruct (Compare_dec.le_gt_dec (length ext) (projT1 c)) as [h_le | h_lt].
    { lia. }
    eassert (surj_n := get_nth_cond_both_prod ext ser par format_correct_surj (projT1 c) Hlt2 surj_prod).
    eassert (tl_n := get_nth_cond_tl_prod ext ser par tl format_to_len_correct (projT1 c) Hlt2 tl_prod).
    eassert (dc_n := get_nth_cond_de_prod ext par decode_consistent (projT1 c) Hlt2 dc_prod).
    eassert (G_ot := open_type_surj _ _ _ surj_n tl_n ni_n dc_n _ b bf' p pos' pf H).
    unfold bind_parse. rewrite G_ot.
    destruct c. unfold return_parse.  simpl.  decode_eq.
  - (* unknown_ext n ct *)
    unfold choice_ext_serial in H.
    destruct (T_Serial _ _ small_integer_format bf pos n)
      as [ [[b p] pf_n] | ] eqn:E1; [| discriminate].
    set (H_leb := Nat.leb_le (length ext) n) in *.
    clearbody H_leb.
    destruct (Nat.leb (length ext) n) eqn:Hle; [| discriminate].
    
    destruct (os_enc b p ct) as [ [[bf'' pos''] pf_ct] | ] eqn:E2; [| discriminate].
    inversion H. subst. clear H.
    apply PeanoNat.Nat.leb_le in Hle.
    eassert (G_surj := fmt_surj (T_Correct _ _ small_integer_format) _ bf b pos p pf_n E1).
    eassert (NI2 := fmt_enc_ni (T_Correct _ _ octet_string_no_cons_format) _ _ _ _ _  _ E2).
    split_and.
    eassert (DC_si := fmt_dec_consist (T_Correct _ _ small_integer_format) _ b pos p pf_n SameVer G_surj).
    split_and. 
    eassert (equiv_bp : EQ.equiv_b b bf' pos p pos p).
    { apply equiv_b_le_zero. exact H0. exact H. }
    eassert (G_si := H3 bf' pos p equiv_bp).
    unfold choice_ext_parse, bind_parse. rewrite G_si.
    destruct (Compare_dec.le_gt_dec (length ext) n) as [h_le' | h_lt].
    + eassert (G_os := fmt_surj (T_Correct _ _ octet_string_no_cons_format) _ _ _ _ _  _ E2).
      unfold os_dec. rewrite G_os.
      unfold return_parse. decode_eq.
    + lia.
Qed.

Lemma choice_ext_inj_same (ext : list typ)
  (ser : get_serial_prodc ext)
  (par : get_parse_prodc ext)
  (tl : get_to_len_prodc ext)
  (ni_prod : get_cond_prodc ext ser encode_non_inter)
  (inj_prod : get_cond_both_prodc ext ser par format_correct_inj_same)
  (tl_prod : get_cond_tl_prodc ext ser par tl format_to_len_correct) :
  format_correct_inj_same _ _ (choice_ext_serial ext ser tl) (choice_ext_parse ext par).
Proof.
  unfold format_correct_inj_same.
  intros [c | n ct] bf pos pos' pf H bf0 Hlen.
  - (* known_ext c *)
    unfold choice_ext_parse, bind_parse in H.
    destruct (T_Parse _ _ small_integer_format bf pos)
      as [ s | ] eqn:EP1; [| discriminate].
    destruct s as [[ [n0 pf_n0] p0] flg0].
    eassert (SVsi := small_integer_parse_SameVer bf pos p0 n0 pf_n0 flg0 EP1). subst.
    destruct (Compare_dec.le_gt_dec (length ext) n0) as [h_le | h_lt].
    { unfold bind_parse in H.
      destruct (os_dec bf p0) as [ [[ct0 pf_ct0] pos1] _ | ] eqn:EP2; [| discriminate].
      unfold return_parse in H. destruct ct0. inversion H. }
    destruct (open_typ_parse (get_nth_parse ext par n0) bf p0)
      as [ [[v0 pf_v0] pos1] flg1 | ] eqn:EP2; [| discriminate].
    unfold return_parse in H. inversion H. subst. clear H.
    assert (Hn0lt : n0 < length2 ext). { rewrite length2_length. exact h_lt. }
    eassert (inj_n := get_nth_cond_both_prod ext ser par format_correct_inj_same n0 Hn0lt inj_prod).
    eassert (tl_n := get_nth_cond_tl_prod ext ser par tl format_to_len_correct n0 Hn0lt tl_prod).
    eassert (ni_n := get_nth_cond_prod ext ser encode_non_inter n0 Hn0lt ni_prod).
    eassert (G_si := fmt_inj_same (T_Correct _ _ small_integer_format) _ _ _ _ _ EP1 bf0 Hlen).
    destruct G_si as [bf0_si [G_si_enc G_si_equiv]].
    eassert (EL := same_len_after_enc _ (fmt_enc_ni (T_Correct _ _ small_integer_format)) G_si_enc). destruct v0. inversion H1. subst. 
    eassert (G_inj := open_type_inj_same _ _ _ inj_n tl_n ni_n _ _ _ _ _ EP2  bf0_si (eq_trans (eq_sym EL) Hlen)).
    destruct G_inj as [bf0' [G_enc G_equiv]].
    exists bf0'.
    split.
    + unfold choice_ext_serial. unfold projT1.
      rewrite G_si_enc.
      assert (Hlt_b : Nat.ltb n0 (length ext) = true).
      { apply Nat.ltb_lt. exact h_lt. }
      rewrite Hlt_b. unfold projT2. simpl. rewrite  G_enc. encode_eq. 
    + eapply format_correct_inj_helper.
      * apply G_si_equiv.
      * apply G_equiv.
      * split_and.
        eapply open_type_non_inter; [exact ni_n | exact G_enc].
  - (* unknown_ext n ct *)
    unfold choice_ext_parse, bind_parse in H.
    destruct (T_Parse _ _ small_integer_format bf pos)
      as [ s | ] eqn:EP1; [| discriminate].
    destruct s as [[ [n0 pf_n0] p0] flg0].
    eassert (SVsi := small_integer_parse_SameVer bf pos p0 n0 pf_n0 flg0 EP1). subst.
    destruct (Compare_dec.le_gt_dec (length ext) n0) as [h_le | h_lt].
    + unfold bind_parse in H.
      destruct (os_dec bf p0) as [ [[[ct0 pf_ct0] pos1] flg1] _ | ] eqn:EP2; [| discriminate]. 
      unfold return_parse in H. inversion H. subst. clear H.
      eassert (G_si := fmt_inj_same (T_Correct _ _ small_integer_format) _ _ _ _ _ EP1 bf0 Hlen).
      destruct G_si as [bf0_si [G_si_enc G_si_equiv]].
      eassert (EL := same_len_after_enc _ (fmt_enc_ni (T_Correct _ _ small_integer_format)) G_si_enc).
      eassert (G_os_inj := fmt_inj_same (T_Correct _ _ octet_string_no_cons_format) _ _ _ _ _ EP2 bf0_si (eq_trans (eq_sym EL) Hlen)).
      destruct G_os_inj as [bf0' [G_os_enc G_os_equiv]].
      exists bf0'.
      split.
      * unfold choice_ext_serial.
        rewrite G_si_enc.
        apply PeanoNat.Nat.leb_le in h_le.
        
        set (H_leb := Nat.leb_le (length ext) n) in *.
        clearbody H_leb.
        revert H_leb.
        
        rewrite h_le.  intros.  unfold os_enc. rewrite  G_os_enc. encode_eq . 
      * eapply format_correct_inj_helper.
        { apply G_si_equiv. }
        { apply G_os_equiv. }
        { split_and.
          eapply fmt_enc_ni.
          - apply T_Correct.
          - rewrite G_os_enc. f_equal. }
    + (* n0 < length ext but we have unknown_ext n ct - contradiction *)
      unfold bind_parse in H.
      destruct (open_typ_parse (get_nth_parse ext par n0) bf p0)
        as [ [[v0 pf_v0] pos1]   _ | ] eqn:EP2; [| discriminate].
      unfold return_parse in H. destruct v0.  inversion H. 
Qed.

Lemma choice_ext_to_len_correct (ext : list typ)
  (ser : get_serial_prodc ext)
  (par : get_parse_prodc ext)
  (tl : get_to_len_prodc ext)
  (ni_prod : get_cond_prodc ext ser encode_non_inter)
  (tl_prod : get_cond_tl_prodc ext ser par tl format_to_len_correct) :
  format_to_len_correct _ _ (choice_ext_serial ext ser tl) (choice_ext_parse ext par)
    (choice_ext_to_len ext tl).
Proof.
  unfold format_to_len_correct. split.
  - (* encoding gives correct length *)
    intros [c | n ct] bf bf' pos pos' pf H.
    + (* known_ext c *)
      unfold choice_ext_serial in H.
      destruct (T_Serial _ _ small_integer_format bf pos (projT1 c))
        as [ [[b p] pf_n] | ] eqn:E1; [| discriminate].
      destruct (Nat.ltb (projT1 c) (length ext)) eqn:Hlt; [| discriminate].
      apply Nat.ltb_lt in Hlt.
      assert (Hlt2 : projT1 c < length2 ext). { rewrite length2_length. exact Hlt. }
      eassert (tl_n := get_nth_cond_tl_prod ext ser par tl format_to_len_correct (projT1 c) Hlt2 tl_prod).
      eassert (ni_n := get_nth_cond_prod ext ser encode_non_inter (projT1 c) Hlt2 ni_prod). 
      eassert (G_tl := (open_type_to_len_correct _ _ _ ni_n tl_n) ).
      destruct G_tl as [G_tl1 G_tl2]. 
      unfold choice_ext_to_len. simpl.
      eassert (G_si_tl := proj1 (fmt_len_c (T_Correct _ _ small_integer_format)) _ bf b pos p pf_n E1).
      eassert (NI1 := fmt_enc_ni (T_Correct _ _ small_integer_format) _ bf b pos p pf_n E1). split_and.
      eassert (G_tl1' := G_tl1 _ _ _ _ _  _ H). 
      unfold BitRep.BProp.le_pos in H3.
      rewrite <- Nat.ltb_lt in Hlt.       
      rewrite Hlt.  rewrite G_tl1'. simpl in G_si_tl.
      unfold n_nat_to_len in G_si_tl.  inversion G_si_tl. f_equal.
      eassert (NI_inner := open_type_non_inter _ _ ni_n _ b bf' p pos' pf H).
      destruct NI_inner as [_ [_ NI_le]]. unfold BitRep.BProp.le_pos in *. lia.
    + (* unknown_ext n ct *)
      unfold choice_ext_serial in H.
      destruct (T_Serial _ _ small_integer_format bf pos n)
        as [ [[b p] pf_n] | ] eqn:E1; [| discriminate].
      set (H_leb := Nat.leb_le (length ext) n) in *.
      clearbody H_leb.
      
      destruct (Nat.leb (length ext) n) eqn:Hle; [| discriminate].

      destruct (os_enc b p ct) as [ [[bf'' pos''] pf_ct] | ] eqn:E2; [| discriminate].
      inversion H. subst. clear H.
      unfold choice_ext_to_len. rewrite Hle.
      eassert (G_si_tl := proj1 (fmt_len_c (T_Correct _ _ small_integer_format)) _ bf b pos p pf_n E1).
      eassert (NI1 := fmt_enc_ni (T_Correct _ _ small_integer_format) _ bf b pos p pf_n E1). split_and.
      eassert (G_os_tl := proj1 (fmt_len_c (T_Correct _ _ octet_string_no_cons_format)) _ _ _ _ _ _  E2).
      rewrite G_si_tl. simpl. unfold os_to_len.  rewrite G_os_tl. simpl.
      eassert (NI_os := fmt_enc_ni (T_Correct _ _ octet_string_no_cons_format) _ b bf' p pos' pf_ct E2).
      destruct NI_os as [_ [_ NI_le_os]]. unfold BitRep.BProp.le_pos in *. f_equal. lia.
  - (* decoding implies length is Some *)
    intros [c | n ct] bf pos pos' pf flg H.
    + (* known_ext c *)
      unfold choice_ext_parse, bind_parse in H.
      destruct (T_Parse _ _ small_integer_format bf pos)
        as [ [[[n0 pf0] p0] flg0] _ | ] eqn:EP1; [| discriminate]. 
      
      destruct (Compare_dec.le_gt_dec (length ext) n0) as [h_le | h_lt].
      { unfold bind_parse in H. 
        destruct (os_dec bf p0) as [ [[[ct0 pf_ct0] pos1] flg1] _ | ]; [| discriminate].
        unfold return_parse in H. inversion H. }
      unfold bind_parse in H.
      destruct (open_typ_parse (get_nth_parse ext par n0) bf p0)
        as [ [[[v0 pf_v0] pos1] flg1] _ | ] eqn:EP2; [| discriminate].
      unfold return_parse in H. inversion H. subst. clear H.
      assert (Hn0lt : n0 < length2 ext). { rewrite length2_length. exact h_lt. }
      eassert (tl_n := get_nth_cond_tl_prod ext ser par tl format_to_len_correct n0 Hn0lt tl_prod).  
      eassert (G := proj2 (open_type_to_len_correct _ _ _ (get_nth_cond_prod ext ser encode_non_inter n0 Hn0lt ni_prod) tl_n)
                      _ _ _ _ _ _ EP2).
      destruct G as [n_tl G_tl].
      unfold choice_ext_to_len. unfold projT1, add_opt. (* simpl. *)
      eassert (G_si := proj2 (fmt_len_c (T_Correct _ _ small_integer_format))
                         _ _ _ _ _ _  EP1).
      destruct G_si as [n_si G_si].
      unfold gt in h_lt. 
      rewrite <- Nat.ltb_lt in h_lt.  rewrite h_lt.
      rewrite G_si.  unfold projT2. 
      rewrite G_tl.  
      eauto.
    + (* unknown_ext n ct *)
      unfold choice_ext_parse, bind_parse in H.
      destruct (T_Parse _ _ small_integer_format bf pos)
        as [ [[[n0 pf_n0] p0] flg0] _ | ] eqn:EP1; [| discriminate].
      destruct (Compare_dec.le_gt_dec (length ext) n0) as [h_le | h_lt]. 
      *  unfold bind_parse in H.
        destruct (os_dec bf p0) as [[ [[ct0 pf_ct0] pos1] flg1] _ | ] eqn:EP2; [| discriminate].
        unfold return_parse in H. inversion H. subst. clear H.
        unfold choice_ext_to_len. 
        apply Compare_dec.leb_correct in h_le. rewrite h_le.
        eassert (G_os := proj2 (fmt_len_c (T_Correct _ _ octet_string_no_cons_format))
                           _ _ _ _ _ _  EP2).
        destruct G_os as [n_os G_os].
        eassert (G_si := proj2 (fmt_len_c (T_Correct _ _ small_integer_format))
                           _ bf pos p0 pf_n0 flg0 EP1).
        destruct G_si as [n_si G_si].  unfold add_opt.
        rewrite G_si. unfold os_to_len. 
        rewrite G_os. eauto. 
      *  unfold bind_parse in H.
        destruct (open_typ_parse (get_nth_parse ext par n0) bf p0)
          as [[ [[pf_v0] pos1] flg1] _ | ]; [| discriminate].
        unfold return_parse in H. inversion H.
Qed.



Opaque Nat.pow.

Lemma choice_ext_inj_diff (ext : list typ)
  (ser : get_serial_prodc ext)
  (par : get_parse_prodc ext)
  (tl : get_to_len_prodc ext)
  (ni_prod : get_cond_prodc ext ser encode_non_inter)
  (gl_prod : get_cond_tl_prodc ext ser par tl format_to_len_correct)
  (inj_prod : get_cond_tl_prodc ext ser par tl format_correct_inj_diff) :
  format_correct_inj_diff _ _ (choice_ext_serial ext ser tl) (choice_ext_parse ext par)
    (choice_ext_to_len ext tl).
Proof.
  unfold format_correct_inj_diff.
  intros [c | n ct] bf pos pos' pf flg H.
  - (* known_ext c *)
    unfold choice_ext_parse, bind_parse in H.

    destruct (T_Parse _ _ small_integer_format bf pos)
      as [[ [[n0 pf_n0] p0] flg0] _ | ] eqn:EP1; [| discriminate].
    eassert (SVsi := small_integer_parse_SameVer bf pos p0 n0 pf_n0 flg0 EP1). subst.
    destruct (Compare_dec.le_gt_dec (length ext) n0) as [h_le | h_lt].
    { unfold bind_parse in H.
      destruct (os_dec bf p0) as [ [[[ct0 pf_ct0] pos1] flg1] _ | ]; [| discriminate].
      unfold return_parse in H. inversion H. }
    unfold bind_parse in H.
    destruct (open_typ_parse (get_nth_parse ext par n0) bf p0)
      as [ [[[v0 pf_v0] pos1] flg1] _ | ] eqn:EP2; [| discriminate].
    unfold return_parse in H. inversion H. subst. clear H.
    assert (Hn0lt : n0 < length2 ext). { rewrite length2_length. exact h_lt. }
    eassert (G_si_inj := fmt_inj_diff (T_Correct _ _ small_integer_format) _ bf pos p0 pf_n0 SameVer EP1).
    destruct G_si_inj as [min_si G_si_inj].
    eassert (ni_n := get_nth_cond_prod ext ser encode_non_inter n0 Hn0lt ni_prod).
    eassert (gl_n := get_nth_cond_tl_prod ext ser par tl format_to_len_correct n0 Hn0lt gl_prod).
    eassert (inj_n := get_nth_cond_tl_prod ext ser par tl format_correct_inj_diff n0 Hn0lt inj_prod).
    
    eassert (G_ot_inj := open_type_inj_diff _ _ _ inj_n gl_n ni_n _ _ _ _ _ _  EP2). 
    destruct G_ot_inj as [min_ot G_ot_inj].
    exists (min_si + min_ot). intros pos0 bf0 Hlen.
    assert (BitRep.BA.to_nat pos0 + min_si <= BitRep.BA.len bf0). { lia. }
    eassert (G := G_si_inj pos0 bf0 H).
    eassert (K1 := proj2 (fmt_len_c (T_Correct _ _ small_integer_format)) _ bf pos p0 pf_n0 SameVer EP1).
    destruct K1 as [n_si K1].
    eassert (K2 := proj2 (open_type_to_len_correct _ _ _ ni_n gl_n)
                     _ bf p0 _ pf_v0 _ EP2).
    destruct K2 as [n_ot K2].
    unfold choice_ext_to_len. unfold add_opt, projT1, projT2.  unfold gt in h_lt. 
    rewrite <- Nat.ltb_lt in h_lt.  rewrite h_lt.   rewrite K1. 
    rewrite K2.
    destruct G.
    { left. simpl. rewrite K1 in H0.
      assert (n_si <= n_si + n_ot). { lia. }
      apply get_byte_len_mono in H1. simpl. lia. }
    destruct H0 as [bf_si [pos_si [G_enc G_le]]].
    assert (BitRep.BA.to_nat pos_si + min_ot <= BitRep.BA.len bf_si).
    { eassert (G' := same_len_after_enc _
                       (fmt_enc_ni (T_Correct _ _ small_integer_format)) G_enc). lia. }
    eassert (G' := G_ot_inj pos_si bf_si H0).
    destruct G'.
    { left.  rewrite K2 in H1.
      assert (n_ot <= n_si + n_ot). { lia. }      
      apply get_byte_len_mono in H2. simpl. lia. }
    destruct H1 as [bf_ot [pos_ot [G_ot_enc G_ot_le]]].
    right. exists bf_ot. exists pos_ot. split.
    + unfold choice_ext_serial. unfold projT1, projT2. 
      rewrite G_enc. rewrite h_lt. 
      rewrite G_ot_enc. encode_eq.
    + lia.
  - (* unknown_ext n ct *)
    unfold choice_ext_parse, bind_parse in H.
    destruct (T_Parse _ _ small_integer_format bf pos)
      as [ [[[n0 pf_n0] p0] flg0] _ | ] eqn:EP1; [| discriminate].
    eassert (SVsi := small_integer_parse_SameVer bf pos p0 n0 pf_n0 flg0 EP1). subst.
    destruct (Compare_dec.le_gt_dec (length ext) n0) as [h_le | h_lt].
    + unfold bind_parse in H.
      destruct (os_dec bf p0) as [ [[[ct0 pf_ct0] pos1] flg1] _ | ] eqn:EP2; [| discriminate].
      unfold return_parse in H. inversion H. subst. clear H.
      eassert (G_si_inj := fmt_inj_diff (T_Correct _ _ small_integer_format) _ bf pos p0 pf_n0 SameVer EP1).
      destruct G_si_inj as [min_si G_si_inj].
      eassert (G_os_inj := fmt_inj_diff (T_Correct _ _ octet_string_no_cons_format) _ bf p0 _ pf_ct0 _  EP2).
      destruct G_os_inj as [min_os G_os_inj].
      exists (min_si + min_os). intros pos0 bf0 Hlen.
      assert (BitRep.BA.to_nat pos0 + min_si <= BitRep.BA.len bf0). { lia. }
      eassert (G := G_si_inj pos0 bf0 H).
      eassert (K1 := proj2 (fmt_len_c (T_Correct _ _ small_integer_format)) _ bf pos p0 pf_n0 SameVer EP1).
      destruct K1 as [n_si K1].
      eassert (K2 := proj2 (fmt_len_c (T_Correct _ _ octet_string_no_cons_format)) _ bf p0 _ pf_ct0 _  EP2).
      destruct K2 as [n_os K2].
      unfold choice_ext_to_len. 
      apply Compare_dec.leb_correct in h_le. rewrite h_le.
      rewrite K1. (*rewrite K2.*)
      unfold os_to_len.  rewrite K2. 
      destruct G.
      { left. simpl. rewrite K1 in H0.
        assert (n_si <= n_si + n_os). { lia. }
        apply get_byte_len_mono in H1. simpl.
        lia. }
      destruct H0 as [bf_si [pos_si [G_enc G_le]]].
      assert (BitRep.BA.to_nat pos_si + min_os <= BitRep.BA.len bf_si).
      { eassert (G' := same_len_after_enc _
                         (fmt_enc_ni (T_Correct _ _ small_integer_format)) G_enc). lia. }
      
      eassert (G' := G_os_inj pos_si bf_si H0).
      destruct G'.
      { left. rewrite K2 in H1.
        assert (n_os <= n_si + n_os). { lia. }
        apply get_byte_len_mono in H2. simpl. lia. }
      destruct H1 as [bf_os [pos_os [G_os_enc G_os_le]]].
      right. exists bf_os. exists pos_os. split.
      * unfold choice_ext_serial. rewrite G_enc.
        
        set (H_leb := Nat.leb_le (length ext) n) in *.
        clearbody H_leb.

        revert H_leb.
        rewrite h_le.
        simpl. intros. unfold os_enc.  rewrite  G_os_enc. encode_eq. 
      * lia.
    + unfold bind_parse in H.
      destruct (open_typ_parse (get_nth_parse ext par n0) bf p0)
        as [ [[[v0 pf_v0] pos1] flg1] _ | ]; [| discriminate].
      unfold return_parse in H. inversion H.
Qed.

Lemma  choice_ext_format_correct (l : list typ)  (fmts : get_formats l) :
  format_correct
    (choice_ext_serial l (fmt_to_prodc l fmts Serialize T_Serial put_empty)
       (fmt_to_prod_no_condc l fmts (fun T : Set => T -> option nat) T_to_len empty_to_len))
    (choice_ext_parse l (fmt_to_prodc l fmts Parse T_Parse read_empty))
    (choice_ext_to_len l
       (fmt_to_prod_no_condc l fmts (fun T : Set => T -> option nat) T_to_len empty_to_len)).
Proof.
  set (ser := fmt_to_prodc l fmts Serialize T_Serial put_empty).
  set (par := fmt_to_prodc l fmts Parse T_Parse read_empty).
  set (tl := fmt_to_prod_no_condc l fmts _ T_to_len empty_to_len).
  unfold format_correct.
  split. 
  - eapply choice_ext_enc_consist.
    + apply fmts_to_conj_enc_ni.
    + apply fmts_to_conj_enc_consist.
  - split. 
    eapply choice_ext_dec_consist.
    apply fmts_to_conj_dec_consist.
    + split.
      eapply choice_ext_enc_non_inter.
      apply fmts_to_conj_enc_ni.
      * split.  
        { eapply choice_ext_surj.
          + apply fmts_to_conj_enc_ni.
          + apply fmts_to_conj_surj.
          + apply fmts_to_conj_fmt_c.
          + apply fmts_to_conj_dec_consist. }
        { split. 
          { eapply choice_ext_inj_same.
            + apply fmts_to_conj_enc_ni.
            + apply fmts_to_conj_inj_same.
            + apply fmts_to_conj_fmt_c. } 
          { split.
            eapply choice_ext_inj_diff.
            + apply fmts_to_conj_enc_ni.
            + apply fmts_to_conj_fmt_c.
            + apply fmts_to_conj_inj_diff.
            + 

              eapply choice_ext_to_len_correct.
              * apply fmts_to_conj_enc_ni.
              * apply fmts_to_conj_fmt_c. }
        }
Qed. 


Definition choice_ext_format (l : list typ) (fmts : get_formats l) :=
  mk_format
    _ _
   (choice_ext_serial l (fmt_to_prodc l fmts Serialize T_Serial put_empty)
       (fmt_to_prod_no_condc l fmts (fun T : Set => T -> option nat) T_to_len empty_to_len))
    (choice_ext_parse l (fmt_to_prodc l fmts Parse T_Parse read_empty))
    (choice_ext_to_len l
       (fmt_to_prod_no_condc l fmts (fun T : Set => T -> option nat) T_to_len empty_to_len))
    (choice_ext_format_correct l fmts).
                             

(*Definition choice_ext_to_len
  {t : Set} 
  (l : nat)
  (tl_t : t -> option nat)
  (ce : choice_ext_typ t) : option nat :=
  match ce with
  | known_ext _ c => tl_t c
  | unknown_ext _ _ ct =>
      octet_string_to_len ct
  end.
*)
