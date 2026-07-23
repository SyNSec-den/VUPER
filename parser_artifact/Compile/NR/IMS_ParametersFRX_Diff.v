Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive IMS_ParametersFRX_Diff__voiceOverNR__Type : Set :=
 | IMS_ParametersFRX_Diff__voiceOverNR__supported
.
Definition IMS_ParametersFRX_Diff__voiceOverNR__cond := (fun (_ : IMS_ParametersFRX_Diff__voiceOverNR__Type) => True).
Lemma IMS_ParametersFRX_Diff__voiceOverNR__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition IMS_ParametersFRX_Diff__voiceOverNR__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 IMS_ParametersFRX_Diff__voiceOverNR__nat__helper.

Definition IMS_ParametersFRX_Diff__voiceOverNR__F1 t :=
  match t with
  | IMS_ParametersFRX_Diff__voiceOverNR__supported => 0
  end.
Definition IMS_ParametersFRX_Diff__voiceOverNR__F2 n :=
  match n with
  | 0 => IMS_ParametersFRX_Diff__voiceOverNR__supported
  | _ => IMS_ParametersFRX_Diff__voiceOverNR__supported
  end.
Lemma IMS_ParametersFRX_Diff__voiceOverNR__F1F2 : forall x : IMS_ParametersFRX_Diff__voiceOverNR__Type, (IMS_ParametersFRX_Diff__voiceOverNR__F1 x <= 0) /\ IMS_ParametersFRX_Diff__voiceOverNR__F2 (IMS_ParametersFRX_Diff__voiceOverNR__F1 x) = x. imp_solve. Qed.
Lemma IMS_ParametersFRX_Diff__voiceOverNR__F2F1 : forall (y : nat) (H : y <= 0), IMS_ParametersFRX_Diff__voiceOverNR__F1 (IMS_ParametersFRX_Diff__voiceOverNR__F2 y) = y. enum_solve H y. Qed.

Record IMS_ParametersFRX_Diff__Type : Set :=
  make__IMS_ParametersFRX_Diff__Type {
    IMS_ParametersFRX_Diff__voiceOverNR : option IMS_ParametersFRX_Diff__voiceOverNR__Type ;
}.
Definition IMS_ParametersFRX_Diff__root_list : list seq_elem := (
 Opt IMS_ParametersFRX_Diff__voiceOverNR__Type IMS_ParametersFRX_Diff__voiceOverNR__cond ::
 nil).
Definition IMS_ParametersFRX_Diff__ext_list : list typ := (
  nil).
Definition IMS_ParametersFRX_Diff__cond (z : IMS_ParametersFRX_Diff__Type) := 
(  opt_cond IMS_ParametersFRX_Diff__voiceOverNR__cond (IMS_ParametersFRX_Diff__voiceOverNR z) /\
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
Definition IMS_ParametersFRX_Diff__voiceOverNR__Format : T_Format IMS_ParametersFRX_Diff__voiceOverNR__Type (fun _ => True) :=
(* Eval compute in *) proj3_format IMS_ParametersFRX_Diff__voiceOverNR__nat__Format IMS_ParametersFRX_Diff__voiceOverNR__F1 IMS_ParametersFRX_Diff__voiceOverNR__F2 IMS_ParametersFRX_Diff__voiceOverNR__F1F2 IMS_ParametersFRX_Diff__voiceOverNR__F2F1.

Opaque IMS_ParametersFRX_Diff__voiceOverNR__cond IMS_ParametersFRX_Diff__voiceOverNR__Format.


Definition IMS_ParametersFRX_Diff__root_Format_Type := Eval cbn in seq_format_prod IMS_ParametersFRX_Diff__root_list.
Definition IMS_ParametersFRX_Diff__root_Format_list : IMS_ParametersFRX_Diff__root_Format_Type :=
  (IMS_ParametersFRX_Diff__voiceOverNR__Format, unit_format).

Definition IMS_ParametersFRX_Diff__ext_Format_Type := Eval cbn in get_formats IMS_ParametersFRX_Diff__ext_list.
Definition IMS_ParametersFRX_Diff__ext_Format_list : IMS_ParametersFRX_Diff__ext_Format_Type :=
  unit__Format.

Definition IMS_ParametersFRX_Diff__list_type : Set := (seq_type IMS_ParametersFRX_Diff__root_list) * (seq_ext_type IMS_ParametersFRX_Diff__ext_list).
Definition IMS_ParametersFRX_Diff__list_cond (z : IMS_ParametersFRX_Diff__list_type) : Prop :=
        (seq_cond IMS_ParametersFRX_Diff__root_list (fst z)) /\ (seq_ext_cond IMS_ParametersFRX_Diff__ext_list (snd z)).
Definition IMS_ParametersFRX_Diff__list_format : T_Format IMS_ParametersFRX_Diff__list_type IMS_ParametersFRX_Diff__list_cond :=
 (* Eval compute in *) seq_ext_format IMS_ParametersFRX_Diff__root_list IMS_ParametersFRX_Diff__root_Format_list IMS_ParametersFRX_Diff__ext_list IMS_ParametersFRX_Diff__ext_Format_list.

Opaque IMS_ParametersFRX_Diff__list_format.
Definition IMS_ParametersFRX_Diff__F1 (z : IMS_ParametersFRX_Diff__Type) : IMS_ParametersFRX_Diff__list_type :=
  (((IMS_ParametersFRX_Diff__voiceOverNR z, tt)), (
tt)).
Definition IMS_ParametersFRX_Diff__F2 (y : IMS_ParametersFRX_Diff__list_type) : IMS_ParametersFRX_Diff__Type :=
  match y with
  | ((j0, _), _)=>
    make__IMS_ParametersFRX_Diff__Type j0
  end.
Definition IMS_ParametersFRX_Diff__helper1 : (forall a : IMS_ParametersFRX_Diff__Type, IMS_ParametersFRX_Diff__cond a -> IMS_ParametersFRX_Diff__list_cond (IMS_ParametersFRX_Diff__F1 a)).
                     intros. destruct a. auto. Qed.
Definition IMS_ParametersFRX_Diff__helper2 : (forall a : IMS_ParametersFRX_Diff__Type, IMS_ParametersFRX_Diff__F2 (IMS_ParametersFRX_Diff__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition IMS_ParametersFRX_Diff__helper3 : (forall b : IMS_ParametersFRX_Diff__list_type, IMS_ParametersFRX_Diff__list_cond b -> IMS_ParametersFRX_Diff__cond (IMS_ParametersFRX_Diff__F2 b) /\ IMS_ParametersFRX_Diff__F1 (IMS_ParametersFRX_Diff__F2 b) = b).
                     intros. destruct b as [y y1]. unfold IMS_ParametersFRX_Diff__cond, IMS_ParametersFRX_Diff__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition IMS_ParametersFRX_Diff__Format : T_Format IMS_ParametersFRX_Diff__Type IMS_ParametersFRX_Diff__cond :=
 proj2_format IMS_ParametersFRX_Diff__cond IMS_ParametersFRX_Diff__list_format  IMS_ParametersFRX_Diff__F1 IMS_ParametersFRX_Diff__F2 IMS_ParametersFRX_Diff__helper1 IMS_ParametersFRX_Diff__helper2 IMS_ParametersFRX_Diff__helper3.

Opaque IMS_ParametersFRX_Diff__cond IMS_ParametersFRX_Diff__Format.

