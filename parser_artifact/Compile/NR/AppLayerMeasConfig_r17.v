Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.MeasConfigAppLayer_r17.

Opaque MeasConfigAppLayer_r17__cond MeasConfigAppLayer_r17__Format.

Definition AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__Type := list MeasConfigAppLayer_r17__Type.

Lemma AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__helper1 : (0 <= 1 <= maxNrofAppLayerMeas_r17)%Z. unfold maxNrofAppLayerMeas_r17.
 lia. Qed.
Lemma AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofAppLayerMeas_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAppLayerMeas_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__cond (z : AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAppLayerMeas_r17)%Z /\ (list_and MeasConfigAppLayer_r17__cond z) .

Require Import NR.MeasConfigAppLayerId_r17.

Opaque MeasConfigAppLayerId_r17__cond MeasConfigAppLayerId_r17__Format.

Definition AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__Type := list MeasConfigAppLayerId_r17__Type.

Lemma AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__helper1 : (0 <= 1 <= maxNrofAppLayerMeas_r17)%Z. unfold maxNrofAppLayerMeas_r17.
 lia. Qed.
Lemma AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__helper2 : to_bit_sz (Z.to_nat (maxNrofAppLayerMeas_r17 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxNrofAppLayerMeas_r17 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__cond (z : AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__Type) :=  (1 <= Z.of_nat (length z) <= maxNrofAppLayerMeas_r17)%Z /\ (list_and MeasConfigAppLayerId_r17__cond z) .

Inductive AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Type : Set :=
 | AppLayerMeasConfig_r17__rrc_SegAllowed_r17__enabled
.
Definition AppLayerMeasConfig_r17__rrc_SegAllowed_r17__cond := (fun (_ : AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Type) => True).
Lemma AppLayerMeasConfig_r17__rrc_SegAllowed_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition AppLayerMeasConfig_r17__rrc_SegAllowed_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 AppLayerMeasConfig_r17__rrc_SegAllowed_r17__nat__helper.

Definition AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F1 t :=
  match t with
  | AppLayerMeasConfig_r17__rrc_SegAllowed_r17__enabled => 0
  end.
Definition AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F2 n :=
  match n with
  | 0 => AppLayerMeasConfig_r17__rrc_SegAllowed_r17__enabled
  | _ => AppLayerMeasConfig_r17__rrc_SegAllowed_r17__enabled
  end.
Lemma AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F1F2 : forall x : AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Type, (AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F1 x <= 0) /\ AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F2 (AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F1 x) = x. imp_solve. Qed.
Lemma AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F2F1 : forall (y : nat) (H : y <= 0), AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F1 (AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F2 y) = y. enum_solve H y. Qed.

Record AppLayerMeasConfig_r17__Type : Set :=
  make__AppLayerMeasConfig_r17__Type {
    AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17 : option AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__Type ;
    AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17 : option AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__Type ;
    AppLayerMeasConfig_r17__rrc_SegAllowed_r17 : option AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Type ;
}.
Definition AppLayerMeasConfig_r17__root_list : list seq_elem := (
 Opt AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__Type AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__cond ::
 Opt AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__Type AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__cond ::
 Opt AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Type AppLayerMeasConfig_r17__rrc_SegAllowed_r17__cond ::
 nil).
Definition AppLayerMeasConfig_r17__ext_list : list typ := (
  nil).
Definition AppLayerMeasConfig_r17__cond (z : AppLayerMeasConfig_r17__Type) := 
(  opt_cond AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__cond (AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17 z) /\
  opt_cond AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__cond (AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17 z) /\
  opt_cond AppLayerMeasConfig_r17__rrc_SegAllowed_r17__cond (AppLayerMeasConfig_r17__rrc_SegAllowed_r17 z) /\
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
Definition AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__Format : T_Format AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__Type AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__cond := seq_of_format MeasConfigAppLayer_r17__Format 1 maxNrofAppLayerMeas_r17 AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__helper1 AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__helper2.

Opaque AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__cond AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__Format.

Definition AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__Format : T_Format AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__Type AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__cond := seq_of_format MeasConfigAppLayerId_r17__Format 1 maxNrofAppLayerMeas_r17 AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__helper1 AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__helper2.

Opaque AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__cond AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__Format.

Definition AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Format : T_Format AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format AppLayerMeasConfig_r17__rrc_SegAllowed_r17__nat__Format AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F1 AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F2 AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F1F2 AppLayerMeasConfig_r17__rrc_SegAllowed_r17__F2F1.

Opaque AppLayerMeasConfig_r17__rrc_SegAllowed_r17__cond AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Format.


Definition AppLayerMeasConfig_r17__root_Format_Type := Eval cbn in seq_format_prod AppLayerMeasConfig_r17__root_list.
Definition AppLayerMeasConfig_r17__root_Format_list : AppLayerMeasConfig_r17__root_Format_Type :=
  (AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17__Format, (AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17__Format, (AppLayerMeasConfig_r17__rrc_SegAllowed_r17__Format, unit_format))).

Definition AppLayerMeasConfig_r17__ext_Format_Type := Eval cbn in get_formats AppLayerMeasConfig_r17__ext_list.
Definition AppLayerMeasConfig_r17__ext_Format_list : AppLayerMeasConfig_r17__ext_Format_Type :=
  unit__Format.

Definition AppLayerMeasConfig_r17__list_type : Set := (seq_type AppLayerMeasConfig_r17__root_list) * (seq_ext_type AppLayerMeasConfig_r17__ext_list).
Definition AppLayerMeasConfig_r17__list_cond (z : AppLayerMeasConfig_r17__list_type) : Prop :=
        (seq_cond AppLayerMeasConfig_r17__root_list (fst z)) /\ (seq_ext_cond AppLayerMeasConfig_r17__ext_list (snd z)).
Definition AppLayerMeasConfig_r17__list_format : T_Format AppLayerMeasConfig_r17__list_type AppLayerMeasConfig_r17__list_cond :=
 (* Eval compute in *) seq_ext_format AppLayerMeasConfig_r17__root_list AppLayerMeasConfig_r17__root_Format_list AppLayerMeasConfig_r17__ext_list AppLayerMeasConfig_r17__ext_Format_list.

Opaque AppLayerMeasConfig_r17__list_format.
Definition AppLayerMeasConfig_r17__F1 (z : AppLayerMeasConfig_r17__Type) : AppLayerMeasConfig_r17__list_type :=
  (((AppLayerMeasConfig_r17__measConfigAppLayerToAddModList_r17 z, (AppLayerMeasConfig_r17__measConfigAppLayerToReleaseList_r17 z, (AppLayerMeasConfig_r17__rrc_SegAllowed_r17 z, tt)))), (
tt)).
Definition AppLayerMeasConfig_r17__F2 (y : AppLayerMeasConfig_r17__list_type) : AppLayerMeasConfig_r17__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__AppLayerMeasConfig_r17__Type j0 j1 j2
  end.
Definition AppLayerMeasConfig_r17__helper1 : (forall a : AppLayerMeasConfig_r17__Type, AppLayerMeasConfig_r17__cond a -> AppLayerMeasConfig_r17__list_cond (AppLayerMeasConfig_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition AppLayerMeasConfig_r17__helper2 : (forall a : AppLayerMeasConfig_r17__Type, AppLayerMeasConfig_r17__F2 (AppLayerMeasConfig_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition AppLayerMeasConfig_r17__helper3 : (forall b : AppLayerMeasConfig_r17__list_type, AppLayerMeasConfig_r17__list_cond b -> AppLayerMeasConfig_r17__cond (AppLayerMeasConfig_r17__F2 b) /\ AppLayerMeasConfig_r17__F1 (AppLayerMeasConfig_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold AppLayerMeasConfig_r17__cond, AppLayerMeasConfig_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition AppLayerMeasConfig_r17__Format : T_Format AppLayerMeasConfig_r17__Type AppLayerMeasConfig_r17__cond :=
 proj2_format AppLayerMeasConfig_r17__cond AppLayerMeasConfig_r17__list_format  AppLayerMeasConfig_r17__F1 AppLayerMeasConfig_r17__F2 AppLayerMeasConfig_r17__helper1 AppLayerMeasConfig_r17__helper2 AppLayerMeasConfig_r17__helper3.

Opaque AppLayerMeasConfig_r17__cond AppLayerMeasConfig_r17__Format.

