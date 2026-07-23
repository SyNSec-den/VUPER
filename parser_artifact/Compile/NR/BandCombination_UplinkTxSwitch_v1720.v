Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.BandCombination_v1720.

Opaque BandCombination_v1720__cond BandCombination_v1720__Format.

Inductive BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Type : Set :=
 | BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__switchedUL
 | BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__dualUL
 | BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__both
.
Definition BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__cond := (fun (_ : BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Type) => True).
Lemma BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__nat__helper.

Definition BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F1 t :=
  match t with
  | BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__switchedUL => 0
  | BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__dualUL => 1
  | BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__both => 2
  end.
Definition BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F2 n :=
  match n with
  | 0 => BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__switchedUL
  | 1 => BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__dualUL
  | 2 => BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__both
  | _ => BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__switchedUL
  end.
Lemma BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F1F2 : forall x : BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Type, (BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F1 x <= 2) /\ BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F2 (BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F1 x) = x. imp_solve. Qed.
Lemma BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F2F1 : forall (y : nat) (H : y <= 2), BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F1 (BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F2 y) = y. enum_solve H y. Qed.

Record BandCombination_UplinkTxSwitch_v1720__Type : Set :=
  make__BandCombination_UplinkTxSwitch_v1720__Type {
    BandCombination_UplinkTxSwitch_v1720__bandCombination_v1720 : option BandCombination_v1720__Type ;
    BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17 : option BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Type ;
}.
Definition BandCombination_UplinkTxSwitch_v1720__list := (
 Opt BandCombination_v1720__Type BandCombination_v1720__cond ::
 Opt BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Type BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__cond ::
 nil).
Definition BandCombination_UplinkTxSwitch_v1720__cond z := 
  opt_cond BandCombination_v1720__cond (BandCombination_UplinkTxSwitch_v1720__bandCombination_v1720 z) /\
  opt_cond BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__cond (BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17 z) /\
  True.


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
Definition BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Format : T_Format BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__nat__Format BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F1 BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F2 BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F1F2 BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__F2F1.

Opaque BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__cond BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Format.


Definition BandCombination_UplinkTxSwitch_v1720__Format_Type := Eval cbn in seq_format_prod BandCombination_UplinkTxSwitch_v1720__list.
Definition BandCombination_UplinkTxSwitch_v1720__Format_list : BandCombination_UplinkTxSwitch_v1720__Format_Type :=
  (BandCombination_v1720__Format, (BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17__Format, unit_format)).
Definition BandCombination_UplinkTxSwitch_v1720__list__Format := (*Eval compute in *) seq_format BandCombination_UplinkTxSwitch_v1720__list BandCombination_UplinkTxSwitch_v1720__Format_list.
Definition BandCombination_UplinkTxSwitch_v1720__F1 z :=
  (BandCombination_UplinkTxSwitch_v1720__bandCombination_v1720 z, (BandCombination_UplinkTxSwitch_v1720__uplinkTxSwitching_OptionSupport2T2T_r17 z, tt)).
Definition BandCombination_UplinkTxSwitch_v1720__F2 (y : seq_type BandCombination_UplinkTxSwitch_v1720__list) :=
  match y with
  | (i0, (i1, _))=>
    make__BandCombination_UplinkTxSwitch_v1720__Type i0 i1
  end.
Lemma BandCombination_UplinkTxSwitch_v1720__F1F2_cond (z : BandCombination_UplinkTxSwitch_v1720__Type)
  : BandCombination_UplinkTxSwitch_v1720__cond z ->
  (seq_cond BandCombination_UplinkTxSwitch_v1720__list (BandCombination_UplinkTxSwitch_v1720__F1 z)).
intro H. unfold BandCombination_UplinkTxSwitch_v1720__cond in H. simpl. auto. Qed.
Lemma BandCombination_UplinkTxSwitch_v1720__F1F2_cond2 (z : BandCombination_UplinkTxSwitch_v1720__Type)
 : BandCombination_UplinkTxSwitch_v1720__F2 (BandCombination_UplinkTxSwitch_v1720__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandCombination_UplinkTxSwitch_v1720__F2F1_cond (y : seq_type BandCombination_UplinkTxSwitch_v1720__list)
  : seq_cond BandCombination_UplinkTxSwitch_v1720__list y ->
 (BandCombination_UplinkTxSwitch_v1720__cond (BandCombination_UplinkTxSwitch_v1720__F2 y)) /\  BandCombination_UplinkTxSwitch_v1720__F1 (BandCombination_UplinkTxSwitch_v1720__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandCombination_UplinkTxSwitch_v1720__cond. simpl in *. auto.
 - simpl. unfold BandCombination_UplinkTxSwitch_v1720__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandCombination_UplinkTxSwitch_v1720__Format : T_Format BandCombination_UplinkTxSwitch_v1720__Type BandCombination_UplinkTxSwitch_v1720__cond :=
        proj2_format  BandCombination_UplinkTxSwitch_v1720__cond BandCombination_UplinkTxSwitch_v1720__list__Format
    BandCombination_UplinkTxSwitch_v1720__F1 BandCombination_UplinkTxSwitch_v1720__F2 BandCombination_UplinkTxSwitch_v1720__F1F2_cond  BandCombination_UplinkTxSwitch_v1720__F1F2_cond2 BandCombination_UplinkTxSwitch_v1720__F2F1_cond.
Opaque BandCombination_UplinkTxSwitch_v1720__cond BandCombination_UplinkTxSwitch_v1720__Format.

