Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueNR.

Opaque ARFCN_ValueNR__cond ARFCN_ValueNR__Format.

Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Require Import NR.SSB_MTC.

Opaque SSB_MTC__cond SSB_MTC__Format.

Record CarrierInfoNR__Type : Set :=
  make__CarrierInfoNR__Type {
    CarrierInfoNR__carrierFreq : ARFCN_ValueNR__Type ;
    CarrierInfoNR__ssbSubcarrierSpacing : SubcarrierSpacing__Type ;
    CarrierInfoNR__smtc : option SSB_MTC__Type ;
}.
Definition CarrierInfoNR__root_list : list seq_elem := (
 Nor ARFCN_ValueNR__Type ARFCN_ValueNR__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt SSB_MTC__Type SSB_MTC__cond ::
 nil).
Definition CarrierInfoNR__ext_list : list typ := (
  nil).
Definition CarrierInfoNR__cond (z : CarrierInfoNR__Type) := 
(  ARFCN_ValueNR__cond (CarrierInfoNR__carrierFreq z) /\
  SubcarrierSpacing__cond (CarrierInfoNR__ssbSubcarrierSpacing z) /\
  opt_cond SSB_MTC__cond (CarrierInfoNR__smtc z) /\
  True) /\ 
(  True).


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

Definition CarrierInfoNR__root_Format_Type := Eval cbn in seq_format_prod CarrierInfoNR__root_list.
Definition CarrierInfoNR__root_Format_list : CarrierInfoNR__root_Format_Type :=
  (ARFCN_ValueNR__Format, (SubcarrierSpacing__Format, (SSB_MTC__Format, unit_format))).

Definition CarrierInfoNR__ext_Format_Type := Eval cbn in get_formats CarrierInfoNR__ext_list.
Definition CarrierInfoNR__ext_Format_list : CarrierInfoNR__ext_Format_Type :=
  unit__Format.

Definition CarrierInfoNR__list_type : Set := (seq_type CarrierInfoNR__root_list) * (seq_ext_type CarrierInfoNR__ext_list).
Definition CarrierInfoNR__list_cond (z : CarrierInfoNR__list_type) : Prop :=
        (seq_cond CarrierInfoNR__root_list (fst z)) /\ (seq_ext_cond CarrierInfoNR__ext_list (snd z)).
Definition CarrierInfoNR__list_format : T_Format CarrierInfoNR__list_type CarrierInfoNR__list_cond :=
 (* Eval compute in *) seq_ext_format CarrierInfoNR__root_list CarrierInfoNR__root_Format_list CarrierInfoNR__ext_list CarrierInfoNR__ext_Format_list.

Opaque CarrierInfoNR__list_format.
Definition CarrierInfoNR__F1 (z : CarrierInfoNR__Type) : CarrierInfoNR__list_type :=
  (((CarrierInfoNR__carrierFreq z, (CarrierInfoNR__ssbSubcarrierSpacing z, (CarrierInfoNR__smtc z, tt)))), (
tt)).
Definition CarrierInfoNR__F2 (y : CarrierInfoNR__list_type) : CarrierInfoNR__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__CarrierInfoNR__Type j0 j1 j2
  end.
Definition CarrierInfoNR__helper1 : (forall a : CarrierInfoNR__Type, CarrierInfoNR__cond a -> CarrierInfoNR__list_cond (CarrierInfoNR__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CarrierInfoNR__helper2 : (forall a : CarrierInfoNR__Type, CarrierInfoNR__F2 (CarrierInfoNR__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CarrierInfoNR__helper3 : (forall b : CarrierInfoNR__list_type, CarrierInfoNR__list_cond b -> CarrierInfoNR__cond (CarrierInfoNR__F2 b) /\ CarrierInfoNR__F1 (CarrierInfoNR__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CarrierInfoNR__cond, CarrierInfoNR__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CarrierInfoNR__Format : T_Format CarrierInfoNR__Type CarrierInfoNR__cond :=
 proj2_format CarrierInfoNR__cond CarrierInfoNR__list_format  CarrierInfoNR__F1 CarrierInfoNR__F2 CarrierInfoNR__helper1 CarrierInfoNR__helper2 CarrierInfoNR__helper3.

Opaque CarrierInfoNR__cond CarrierInfoNR__Format.

