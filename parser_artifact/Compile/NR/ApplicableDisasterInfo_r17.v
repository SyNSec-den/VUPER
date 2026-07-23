Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_Identity.

Opaque PLMN_Identity__cond PLMN_Identity__Format.

Definition ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Type := list PLMN_Identity__Type.

Lemma ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__helper1 : (0 <= 1 <= maxPLMN)%Z. unfold maxPLMN.
 lia. Qed.
Lemma ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__helper2 : to_bit_sz (Z.to_nat (maxPLMN - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxPLMN - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__cond (z : ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxPLMN)%Z /\ (list_and PLMN_Identity__cond z) .


Inductive ApplicableDisasterInfo_r17__Type : Set :=
  | ApplicableDisasterInfo_r17__noDisasterRoaming_r17 : unit -> ApplicableDisasterInfo_r17__Type
  | ApplicableDisasterInfo_r17__disasterRelatedIndication_r17 : unit -> ApplicableDisasterInfo_r17__Type
  | ApplicableDisasterInfo_r17__commonPLMNs_r17 : unit -> ApplicableDisasterInfo_r17__Type
  | ApplicableDisasterInfo_r17__dedicatedPLMNs_r17 : ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Type -> ApplicableDisasterInfo_r17__Type
.
Definition ApplicableDisasterInfo_r17__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Type ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__cond ::
 nil).
Definition ApplicableDisasterInfo_r17__cond (c : ApplicableDisasterInfo_r17__Type) := 
  match c with
  | ApplicableDisasterInfo_r17__noDisasterRoaming_r17 t => (fun _ => True) t 
  | ApplicableDisasterInfo_r17__disasterRelatedIndication_r17 t => (fun _ => True) t 
  | ApplicableDisasterInfo_r17__commonPLMNs_r17 t => (fun _ => True) t 
  | ApplicableDisasterInfo_r17__dedicatedPLMNs_r17 t => ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__cond t 
  end.

Lemma ApplicableDisasterInfo_r17__len_helper1 : to_bit_sz (length ApplicableDisasterInfo_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma ApplicableDisasterInfo_r17__len_helper2 : 2 <= length2 ApplicableDisasterInfo_r17__list.
 simpl. lia. Qed.

Opaque Byte.to_nat Byte.of_nat.
Opaque bind_parse restrict_parse proj_parse return_parse.
Opaque restrict_serialize proj_serialize sigma_serialize append_serialize proj2_serialize.

Opaque read_n_nat read_unit.
Opaque put_n_nat put_unit. 

Opaque opt_bind opt_serialize dft_serialize prepend_serialize list_serial.
Opaque opt_parse list_parse dft_parse fail_parse append_parse
  bind_parse return_parse.

Opaque Z.to_nat Z.of_nat Z.sub Z.add Z.le Z.lt Z.pow Z.opp Z.ltb.
Opaque Nat.mul Nat.shiftr Nat.shiftl Nat.div Nat.modulo Nat.leb Nat.ltb Nat.add
  Nat.sub Nat.land Nat.lor Nat.eqb  Nat.log2 Nat.pow Nat.even PeanoNat.Nat.lnot.
Opaque Compare_dec.le_dec Compare_dec.le_lt_dec ZArith_dec.Z_le_dec lt_eq_lt_dec_new. 
Opaque sumbool_and1 list_and list_and_cons list_cons_S flg_add. 

Opaque list_to_len.
   Opaque length Compare_dec.le_dec Compare_dec.lt_dec PeanoNat.Nat.eq_dec.
   Opaque bool__Format int__Format octet_string_nc__Format bit_string_nc__Format.

   Opaque ByteIdx_to_nat nat_to_ByteIdx add_opt list_bool_format normally_small_len_det_format
  get_byte_len to_parse_skip  open_typ_serialize open_typ_parse open_type_to_len.
  

Opaque seq_cond seq_ext_cond choice_cond.
Definition ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Format : T_Format ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Type ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__cond := seq_of_format PLMN_Identity__Format 1 maxPLMN ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__helper1 ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__helper2.

Opaque ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__cond ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Format.


Definition ApplicableDisasterInfo_r17__Format_Type := Eval cbn in get_formats ApplicableDisasterInfo_r17__list.
Definition ApplicableDisasterInfo_r17__Format_list : ApplicableDisasterInfo_r17__Format_Type :=
  (unit__Format, (unit__Format, (unit__Format, (ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Format, unit__Format)))).
Definition ApplicableDisasterInfo_r17__list__Format := Eval compute in choice_format ApplicableDisasterInfo_r17__list ApplicableDisasterInfo_r17__len_helper1 ApplicableDisasterInfo_r17__len_helper2  ApplicableDisasterInfo_r17__Format_list.
Definition ApplicableDisasterInfo_r17__F1 (z : ApplicableDisasterInfo_r17__Type) : (choice ApplicableDisasterInfo_r17__list) :=
  match z with
   | ApplicableDisasterInfo_r17__noDisasterRoaming_r17 t => existT _ 0 t
  | ApplicableDisasterInfo_r17__disasterRelatedIndication_r17 t => existT _ 1 t
  | ApplicableDisasterInfo_r17__commonPLMNs_r17 t => existT _ 2 t
  | ApplicableDisasterInfo_r17__dedicatedPLMNs_r17 t => existT _ 3 t
  end.
Definition ApplicableDisasterInfo_r17__g := (fun n => typ_set (get_nth_typ ApplicableDisasterInfo_r17__list n)).
Definition ApplicableDisasterInfo_r17__F2 (y : choice ApplicableDisasterInfo_r17__list) : ApplicableDisasterInfo_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (ApplicableDisasterInfo_r17__g n -> ApplicableDisasterInfo_r17__Type) with
    | 0 => fun (t : unit) => ApplicableDisasterInfo_r17__noDisasterRoaming_r17 t 
    | 1 => fun (t : unit) => ApplicableDisasterInfo_r17__disasterRelatedIndication_r17 t 
    | 2 => fun (t : unit) => ApplicableDisasterInfo_r17__commonPLMNs_r17 t 
    | 3 => fun (t : ApplicableDisasterInfo_r17__dedicatedPLMNs_r17__Type) => ApplicableDisasterInfo_r17__dedicatedPLMNs_r17 t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : ApplicableDisasterInfo_r17__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ ApplicableDisasterInfo_r17__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len ApplicableDisasterInfo_r17__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return ApplicableDisasterInfo_r17__Type with end) n0
           end t0).

Lemma ApplicableDisasterInfo_r17__helper2 :  forall (y : ApplicableDisasterInfo_r17__Type), ApplicableDisasterInfo_r17__cond y -> choice_cond ApplicableDisasterInfo_r17__list (ApplicableDisasterInfo_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma ApplicableDisasterInfo_r17__helper3 :  forall (y : ApplicableDisasterInfo_r17__Type), ApplicableDisasterInfo_r17__F2 (ApplicableDisasterInfo_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma ApplicableDisasterInfo_r17__helper4 : (forall b : choice ApplicableDisasterInfo_r17__list, choice_cond ApplicableDisasterInfo_r17__list b -> ApplicableDisasterInfo_r17__cond (ApplicableDisasterInfo_r17__F2 b) /\ ApplicableDisasterInfo_r17__F1 (ApplicableDisasterInfo_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length ApplicableDisasterInfo_r17__F1 ApplicableDisasterInfo_r17__F2.
Definition ApplicableDisasterInfo_r17__Format : T_Format ApplicableDisasterInfo_r17__Type ApplicableDisasterInfo_r17__cond :=
  (* Eval compute in *) proj2_format ApplicableDisasterInfo_r17__cond ApplicableDisasterInfo_r17__list__Format ApplicableDisasterInfo_r17__F1 ApplicableDisasterInfo_r17__F2 ApplicableDisasterInfo_r17__helper2 ApplicableDisasterInfo_r17__helper3 ApplicableDisasterInfo_r17__helper4.
Opaque ApplicableDisasterInfo_r17__cond ApplicableDisasterInfo_r17__Format.

