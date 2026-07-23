Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PLMN_RAN_AreaCellList.

Opaque PLMN_RAN_AreaCellList__cond PLMN_RAN_AreaCellList__Format.

Require Import NR.PLMN_RAN_AreaConfigList.

Opaque PLMN_RAN_AreaConfigList__cond PLMN_RAN_AreaConfigList__Format.


Inductive RAN_NotificationAreaInfo__root__Type : Set :=
  | RAN_NotificationAreaInfo__root__cellList : PLMN_RAN_AreaCellList__Type -> RAN_NotificationAreaInfo__root__Type
  | RAN_NotificationAreaInfo__root__ran_AreaConfigList : PLMN_RAN_AreaConfigList__Type -> RAN_NotificationAreaInfo__root__Type
.
Definition RAN_NotificationAreaInfo__root__list : list typ := (
typ_cons PLMN_RAN_AreaCellList__Type PLMN_RAN_AreaCellList__cond ::
typ_cons PLMN_RAN_AreaConfigList__Type PLMN_RAN_AreaConfigList__cond ::
 nil).
Definition RAN_NotificationAreaInfo__root__cond (c : RAN_NotificationAreaInfo__root__Type) := 
  match c with
  | RAN_NotificationAreaInfo__root__cellList t => PLMN_RAN_AreaCellList__cond t 
  | RAN_NotificationAreaInfo__root__ran_AreaConfigList t => PLMN_RAN_AreaConfigList__cond t 
  end.

Lemma RAN_NotificationAreaInfo__root__len_helper1 : to_bit_sz (length RAN_NotificationAreaInfo__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma RAN_NotificationAreaInfo__root__len_helper2 : 2 <= length2 RAN_NotificationAreaInfo__root__list.
 simpl. lia. Qed.

Definition RAN_NotificationAreaInfo__ext__Type : Set := Empty_set.
Definition RAN_NotificationAreaInfo__ext__cond (c : RAN_NotificationAreaInfo__ext__Type) := True.
Definition RAN_NotificationAreaInfo__Type : Set := RAN_NotificationAreaInfo__root__Type + RAN_NotificationAreaInfo__ext__Type.
Definition RAN_NotificationAreaInfo__cond :=
  sum_cond RAN_NotificationAreaInfo__root__cond RAN_NotificationAreaInfo__ext__cond.

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

Definition RAN_NotificationAreaInfo__root__Format_Type := Eval cbn in get_formats RAN_NotificationAreaInfo__root__list.
Definition RAN_NotificationAreaInfo__root__Format_list : RAN_NotificationAreaInfo__root__Format_Type :=
  (PLMN_RAN_AreaCellList__Format, (PLMN_RAN_AreaConfigList__Format, unit__Format)).
Definition RAN_NotificationAreaInfo__root__list__Format := Eval compute in choice_format RAN_NotificationAreaInfo__root__list RAN_NotificationAreaInfo__root__len_helper1 RAN_NotificationAreaInfo__root__len_helper2  RAN_NotificationAreaInfo__root__Format_list.
Definition RAN_NotificationAreaInfo__root__F1 (z : RAN_NotificationAreaInfo__root__Type) : (choice RAN_NotificationAreaInfo__root__list) :=
  match z with
   | RAN_NotificationAreaInfo__root__cellList t => existT _ 0 t
  | RAN_NotificationAreaInfo__root__ran_AreaConfigList t => existT _ 1 t
  end.
Definition RAN_NotificationAreaInfo__root__g := (fun n => typ_set (get_nth_typ RAN_NotificationAreaInfo__root__list n)).
Definition RAN_NotificationAreaInfo__root__F2 (y : choice RAN_NotificationAreaInfo__root__list) : RAN_NotificationAreaInfo__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (RAN_NotificationAreaInfo__root__g n -> RAN_NotificationAreaInfo__root__Type) with
    | 0 => fun (t : PLMN_RAN_AreaCellList__Type) => RAN_NotificationAreaInfo__root__cellList t 
    | 1 => fun (t : PLMN_RAN_AreaConfigList__Type) => RAN_NotificationAreaInfo__root__ran_AreaConfigList t 
 | (S (S n0)) => (fun (x' : nat) (t'' : RAN_NotificationAreaInfo__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ RAN_NotificationAreaInfo__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len RAN_NotificationAreaInfo__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return RAN_NotificationAreaInfo__root__Type with end) n0
           end t0).

Lemma RAN_NotificationAreaInfo__root__helper2 :  forall (y : RAN_NotificationAreaInfo__root__Type), RAN_NotificationAreaInfo__root__cond y -> choice_cond RAN_NotificationAreaInfo__root__list (RAN_NotificationAreaInfo__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma RAN_NotificationAreaInfo__root__helper3 :  forall (y : RAN_NotificationAreaInfo__root__Type), RAN_NotificationAreaInfo__root__F2 (RAN_NotificationAreaInfo__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma RAN_NotificationAreaInfo__root__helper4 : (forall b : choice RAN_NotificationAreaInfo__root__list, choice_cond RAN_NotificationAreaInfo__root__list b -> RAN_NotificationAreaInfo__root__cond (RAN_NotificationAreaInfo__root__F2 b) /\ RAN_NotificationAreaInfo__root__F1 (RAN_NotificationAreaInfo__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length RAN_NotificationAreaInfo__root__F1 RAN_NotificationAreaInfo__root__F2.
Definition RAN_NotificationAreaInfo__root__Format : T_Format RAN_NotificationAreaInfo__root__Type RAN_NotificationAreaInfo__root__cond :=
  (* Eval compute in *) proj2_format RAN_NotificationAreaInfo__root__cond RAN_NotificationAreaInfo__root__list__Format RAN_NotificationAreaInfo__root__F1 RAN_NotificationAreaInfo__root__F2 RAN_NotificationAreaInfo__root__helper2 RAN_NotificationAreaInfo__root__helper3 RAN_NotificationAreaInfo__root__helper4.
Opaque RAN_NotificationAreaInfo__root__cond RAN_NotificationAreaInfo__root__Format.

Definition RAN_NotificationAreaInfo__ext__Format : T_Format RAN_NotificationAreaInfo__ext__Type RAN_NotificationAreaInfo__ext__cond := empty_format.
Opaque RAN_NotificationAreaInfo__ext__cond RAN_NotificationAreaInfo__ext__Format.

Definition RAN_NotificationAreaInfo__Format : T_Format RAN_NotificationAreaInfo__Type RAN_NotificationAreaInfo__cond := sum_format RAN_NotificationAreaInfo__root__Format RAN_NotificationAreaInfo__ext__Format.
Opaque RAN_NotificationAreaInfo__cond RAN_NotificationAreaInfo__Format.

