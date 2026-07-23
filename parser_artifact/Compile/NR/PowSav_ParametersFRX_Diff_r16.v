Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Type : Set :=
 | PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__supported
.
Definition PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__cond := (fun (_ : PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Type) => True).
Lemma PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__nat__helper.

Definition PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F1 t :=
  match t with
  | PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__supported => 0
  end.
Definition PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F2 n :=
  match n with
  | 0 => PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__supported
  | _ => PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__supported
  end.
Lemma PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F1F2 : forall x : PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Type, (PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F1 x <= 0) /\ PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F2 (PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F1 x) = x. imp_solve. Qed.
Lemma PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F2F1 : forall (y : nat) (H : y <= 0), PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F1 (PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F2 y) = y. enum_solve H y. Qed.

Inductive PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Type : Set :=
 | PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__supported
.
Definition PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__cond := (fun (_ : PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Type) => True).
Lemma PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__nat__helper.

Definition PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F1 t :=
  match t with
  | PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__supported => 0
  end.
Definition PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F2 n :=
  match n with
  | 0 => PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__supported
  | _ => PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__supported
  end.
Lemma PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F1F2 : forall x : PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Type, (PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F1 x <= 0) /\ PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F2 (PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F1 x) = x. imp_solve. Qed.
Lemma PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F2F1 : forall (y : nat) (H : y <= 0), PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F1 (PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F2 y) = y. enum_solve H y. Qed.

Record PowSav_ParametersFRX_Diff_r16__Type : Set :=
  make__PowSav_ParametersFRX_Diff_r16__Type {
    PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16 : option PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Type ;
    PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16 : option PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Type ;
}.
Definition PowSav_ParametersFRX_Diff_r16__root_list : list seq_elem := (
 Opt PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Type PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__cond ::
 Opt PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Type PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__cond ::
 nil).
Definition PowSav_ParametersFRX_Diff_r16__ext_list : list typ := (
  nil).
Definition PowSav_ParametersFRX_Diff_r16__cond (z : PowSav_ParametersFRX_Diff_r16__Type) := 
(  opt_cond PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__cond (PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16 z) /\
  opt_cond PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__cond (PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16 z) /\
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
Definition PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Format : T_Format PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__nat__Format PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F1 PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F2 PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F1F2 PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__F2F1.

Opaque PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__cond PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Format.

Definition PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Format : T_Format PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__nat__Format PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F1 PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F2 PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F1F2 PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__F2F1.

Opaque PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__cond PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Format.


Definition PowSav_ParametersFRX_Diff_r16__root_Format_Type := Eval cbn in seq_format_prod PowSav_ParametersFRX_Diff_r16__root_list.
Definition PowSav_ParametersFRX_Diff_r16__root_Format_list : PowSav_ParametersFRX_Diff_r16__root_Format_Type :=
  (PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16__Format, (PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16__Format, unit_format)).

Definition PowSav_ParametersFRX_Diff_r16__ext_Format_Type := Eval cbn in get_formats PowSav_ParametersFRX_Diff_r16__ext_list.
Definition PowSav_ParametersFRX_Diff_r16__ext_Format_list : PowSav_ParametersFRX_Diff_r16__ext_Format_Type :=
  unit__Format.

Definition PowSav_ParametersFRX_Diff_r16__list_type : Set := (seq_type PowSav_ParametersFRX_Diff_r16__root_list) * (seq_ext_type PowSav_ParametersFRX_Diff_r16__ext_list).
Definition PowSav_ParametersFRX_Diff_r16__list_cond (z : PowSav_ParametersFRX_Diff_r16__list_type) : Prop :=
        (seq_cond PowSav_ParametersFRX_Diff_r16__root_list (fst z)) /\ (seq_ext_cond PowSav_ParametersFRX_Diff_r16__ext_list (snd z)).
Definition PowSav_ParametersFRX_Diff_r16__list_format : T_Format PowSav_ParametersFRX_Diff_r16__list_type PowSav_ParametersFRX_Diff_r16__list_cond :=
 (* Eval compute in *) seq_ext_format PowSav_ParametersFRX_Diff_r16__root_list PowSav_ParametersFRX_Diff_r16__root_Format_list PowSav_ParametersFRX_Diff_r16__ext_list PowSav_ParametersFRX_Diff_r16__ext_Format_list.

Opaque PowSav_ParametersFRX_Diff_r16__list_format.
Definition PowSav_ParametersFRX_Diff_r16__F1 (z : PowSav_ParametersFRX_Diff_r16__Type) : PowSav_ParametersFRX_Diff_r16__list_type :=
  (((PowSav_ParametersFRX_Diff_r16__maxBW_Preference_r16 z, (PowSav_ParametersFRX_Diff_r16__maxMIMO_LayerPreference_r16 z, tt))), (
tt)).
Definition PowSav_ParametersFRX_Diff_r16__F2 (y : PowSav_ParametersFRX_Diff_r16__list_type) : PowSav_ParametersFRX_Diff_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__PowSav_ParametersFRX_Diff_r16__Type j0 j1
  end.
Definition PowSav_ParametersFRX_Diff_r16__helper1 : (forall a : PowSav_ParametersFRX_Diff_r16__Type, PowSav_ParametersFRX_Diff_r16__cond a -> PowSav_ParametersFRX_Diff_r16__list_cond (PowSav_ParametersFRX_Diff_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PowSav_ParametersFRX_Diff_r16__helper2 : (forall a : PowSav_ParametersFRX_Diff_r16__Type, PowSav_ParametersFRX_Diff_r16__F2 (PowSav_ParametersFRX_Diff_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PowSav_ParametersFRX_Diff_r16__helper3 : (forall b : PowSav_ParametersFRX_Diff_r16__list_type, PowSav_ParametersFRX_Diff_r16__list_cond b -> PowSav_ParametersFRX_Diff_r16__cond (PowSav_ParametersFRX_Diff_r16__F2 b) /\ PowSav_ParametersFRX_Diff_r16__F1 (PowSav_ParametersFRX_Diff_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PowSav_ParametersFRX_Diff_r16__cond, PowSav_ParametersFRX_Diff_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PowSav_ParametersFRX_Diff_r16__Format : T_Format PowSav_ParametersFRX_Diff_r16__Type PowSav_ParametersFRX_Diff_r16__cond :=
 proj2_format PowSav_ParametersFRX_Diff_r16__cond PowSav_ParametersFRX_Diff_r16__list_format  PowSav_ParametersFRX_Diff_r16__F1 PowSav_ParametersFRX_Diff_r16__F2 PowSav_ParametersFRX_Diff_r16__helper1 PowSav_ParametersFRX_Diff_r16__helper2 PowSav_ParametersFRX_Diff_r16__helper3.

Opaque PowSav_ParametersFRX_Diff_r16__cond PowSav_ParametersFRX_Diff_r16__Format.

