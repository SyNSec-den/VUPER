Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SSB_Index.

Opaque SSB_Index__cond SSB_Index__Format.

Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.


Inductive PathlossReferenceRS_Config__Type : Set :=
  | PathlossReferenceRS_Config__ssb_Index : SSB_Index__Type -> PathlossReferenceRS_Config__Type
  | PathlossReferenceRS_Config__csi_RS_Index : NZP_CSI_RS_ResourceId__Type -> PathlossReferenceRS_Config__Type
.
Definition PathlossReferenceRS_Config__list : list typ := (
typ_cons SSB_Index__Type SSB_Index__cond ::
typ_cons NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 nil).
Definition PathlossReferenceRS_Config__cond (c : PathlossReferenceRS_Config__Type) := 
  match c with
  | PathlossReferenceRS_Config__ssb_Index t => SSB_Index__cond t 
  | PathlossReferenceRS_Config__csi_RS_Index t => NZP_CSI_RS_ResourceId__cond t 
  end.

Lemma PathlossReferenceRS_Config__len_helper1 : to_bit_sz (length PathlossReferenceRS_Config__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma PathlossReferenceRS_Config__len_helper2 : 2 <= length2 PathlossReferenceRS_Config__list.
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

Definition PathlossReferenceRS_Config__Format_Type := Eval cbn in get_formats PathlossReferenceRS_Config__list.
Definition PathlossReferenceRS_Config__Format_list : PathlossReferenceRS_Config__Format_Type :=
  (SSB_Index__Format, (NZP_CSI_RS_ResourceId__Format, unit__Format)).
Definition PathlossReferenceRS_Config__list__Format := Eval compute in choice_format PathlossReferenceRS_Config__list PathlossReferenceRS_Config__len_helper1 PathlossReferenceRS_Config__len_helper2  PathlossReferenceRS_Config__Format_list.
Definition PathlossReferenceRS_Config__F1 (z : PathlossReferenceRS_Config__Type) : (choice PathlossReferenceRS_Config__list) :=
  match z with
   | PathlossReferenceRS_Config__ssb_Index t => existT _ 0 t
  | PathlossReferenceRS_Config__csi_RS_Index t => existT _ 1 t
  end.
Definition PathlossReferenceRS_Config__g := (fun n => typ_set (get_nth_typ PathlossReferenceRS_Config__list n)).
Definition PathlossReferenceRS_Config__F2 (y : choice PathlossReferenceRS_Config__list) : PathlossReferenceRS_Config__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (PathlossReferenceRS_Config__g n -> PathlossReferenceRS_Config__Type) with
    | 0 => fun (t : SSB_Index__Type) => PathlossReferenceRS_Config__ssb_Index t 
    | 1 => fun (t : NZP_CSI_RS_ResourceId__Type) => PathlossReferenceRS_Config__csi_RS_Index t 
 | (S (S n0)) => (fun (x' : nat) (t'' : PathlossReferenceRS_Config__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ PathlossReferenceRS_Config__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len PathlossReferenceRS_Config__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return PathlossReferenceRS_Config__Type with end) n0
           end t0).

Lemma PathlossReferenceRS_Config__helper2 :  forall (y : PathlossReferenceRS_Config__Type), PathlossReferenceRS_Config__cond y -> choice_cond PathlossReferenceRS_Config__list (PathlossReferenceRS_Config__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma PathlossReferenceRS_Config__helper3 :  forall (y : PathlossReferenceRS_Config__Type), PathlossReferenceRS_Config__F2 (PathlossReferenceRS_Config__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma PathlossReferenceRS_Config__helper4 : (forall b : choice PathlossReferenceRS_Config__list, choice_cond PathlossReferenceRS_Config__list b -> PathlossReferenceRS_Config__cond (PathlossReferenceRS_Config__F2 b) /\ PathlossReferenceRS_Config__F1 (PathlossReferenceRS_Config__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length PathlossReferenceRS_Config__F1 PathlossReferenceRS_Config__F2.
Definition PathlossReferenceRS_Config__Format : T_Format PathlossReferenceRS_Config__Type PathlossReferenceRS_Config__cond :=
  (* Eval compute in *) proj2_format PathlossReferenceRS_Config__cond PathlossReferenceRS_Config__list__Format PathlossReferenceRS_Config__F1 PathlossReferenceRS_Config__F2 PathlossReferenceRS_Config__helper2 PathlossReferenceRS_Config__helper3 PathlossReferenceRS_Config__helper4.
Opaque PathlossReferenceRS_Config__cond PathlossReferenceRS_Config__Format.

