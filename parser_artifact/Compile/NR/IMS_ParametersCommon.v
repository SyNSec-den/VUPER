Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive IMS_ParametersCommon__voiceOverEUTRA_5GC__Type : Set :=
 | IMS_ParametersCommon__voiceOverEUTRA_5GC__supported
.
Definition IMS_ParametersCommon__voiceOverEUTRA_5GC__cond := (fun (_ : IMS_ParametersCommon__voiceOverEUTRA_5GC__Type) => True).
Lemma IMS_ParametersCommon__voiceOverEUTRA_5GC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition IMS_ParametersCommon__voiceOverEUTRA_5GC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 IMS_ParametersCommon__voiceOverEUTRA_5GC__nat__helper.

Definition IMS_ParametersCommon__voiceOverEUTRA_5GC__F1 t :=
  match t with
  | IMS_ParametersCommon__voiceOverEUTRA_5GC__supported => 0
  end.
Definition IMS_ParametersCommon__voiceOverEUTRA_5GC__F2 n :=
  match n with
  | 0 => IMS_ParametersCommon__voiceOverEUTRA_5GC__supported
  | _ => IMS_ParametersCommon__voiceOverEUTRA_5GC__supported
  end.
Lemma IMS_ParametersCommon__voiceOverEUTRA_5GC__F1F2 : forall x : IMS_ParametersCommon__voiceOverEUTRA_5GC__Type, (IMS_ParametersCommon__voiceOverEUTRA_5GC__F1 x <= 0) /\ IMS_ParametersCommon__voiceOverEUTRA_5GC__F2 (IMS_ParametersCommon__voiceOverEUTRA_5GC__F1 x) = x. imp_solve. Qed.
Lemma IMS_ParametersCommon__voiceOverEUTRA_5GC__F2F1 : forall (y : nat) (H : y <= 0), IMS_ParametersCommon__voiceOverEUTRA_5GC__F1 (IMS_ParametersCommon__voiceOverEUTRA_5GC__F2 y) = y. enum_solve H y. Qed.

Inductive IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Type : Set :=
 | IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__supported
.
Definition IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__cond := (fun (_ : IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Type) => True).
Lemma IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__nat__helper.

Definition IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F1 t :=
  match t with
  | IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__supported => 0
  end.
Definition IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F2 n :=
  match n with
  | 0 => IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__supported
  | _ => IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__supported
  end.
Lemma IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F1F2 : forall x : IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Type, (IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F1 x <= 0) /\ IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F2 (IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F1 x) = x. imp_solve. Qed.
Lemma IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F2F1 : forall (y : nat) (H : y <= 0), IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F1 (IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F2 y) = y. enum_solve H y. Qed.

Record IMS_ParametersCommon__ext0O__Type : Set :=
  make__IMS_ParametersCommon__ext0O__Type {
    IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC : option IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Type ;
}.
Definition IMS_ParametersCommon__ext0O__list := (
 Opt IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Type IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__cond ::
 nil).
Definition IMS_ParametersCommon__ext0O__cond z := 
  opt_cond IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__cond (IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC z) /\
  True.

Definition IMS_ParametersCommon__ext0__Type := IMS_ParametersCommon__ext0O__Type.
Definition IMS_ParametersCommon__ext0__cond := IMS_ParametersCommon__ext0O__cond.

Inductive IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Type : Set :=
 | IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__supported
.
Definition IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__cond := (fun (_ : IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Type) => True).
Lemma IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__nat__helper.

Definition IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F1 t :=
  match t with
  | IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__supported => 0
  end.
Definition IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F2 n :=
  match n with
  | 0 => IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__supported
  | _ => IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__supported
  end.
Lemma IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F1F2 : forall x : IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Type, (IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F1 x <= 0) /\ IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F2 (IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F1 x) = x. imp_solve. Qed.
Lemma IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F2F1 : forall (y : nat) (H : y <= 0), IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F1 (IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F2 y) = y. enum_solve H y. Qed.

Record IMS_ParametersCommon__ext1O__Type : Set :=
  make__IMS_ParametersCommon__ext1O__Type {
    IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16 : option IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Type ;
}.
Definition IMS_ParametersCommon__ext1O__list := (
 Opt IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Type IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__cond ::
 nil).
Definition IMS_ParametersCommon__ext1O__cond z := 
  opt_cond IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__cond (IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16 z) /\
  True.

Definition IMS_ParametersCommon__ext1__Type := IMS_ParametersCommon__ext1O__Type.
Definition IMS_ParametersCommon__ext1__cond := IMS_ParametersCommon__ext1O__cond.

Record IMS_ParametersCommon__Type : Set :=
  make__IMS_ParametersCommon__Type {
    IMS_ParametersCommon__voiceOverEUTRA_5GC : option IMS_ParametersCommon__voiceOverEUTRA_5GC__Type ;
    IMS_ParametersCommon__ext0 : option IMS_ParametersCommon__ext0__Type ;
    IMS_ParametersCommon__ext1 : option IMS_ParametersCommon__ext1__Type ;
}.
Definition IMS_ParametersCommon__root_list : list seq_elem := (
 Opt IMS_ParametersCommon__voiceOverEUTRA_5GC__Type IMS_ParametersCommon__voiceOverEUTRA_5GC__cond ::
 nil).
Definition IMS_ParametersCommon__ext_list : list typ := (
  typ_cons IMS_ParametersCommon__ext0__Type IMS_ParametersCommon__ext0__cond ::
  typ_cons IMS_ParametersCommon__ext1__Type IMS_ParametersCommon__ext1__cond ::
  nil).
Definition IMS_ParametersCommon__cond (z : IMS_ParametersCommon__Type) := 
(  opt_cond IMS_ParametersCommon__voiceOverEUTRA_5GC__cond (IMS_ParametersCommon__voiceOverEUTRA_5GC z) /\
  True) /\ 
(  opt_cond IMS_ParametersCommon__ext0__cond (IMS_ParametersCommon__ext0 z) /\
  opt_cond IMS_ParametersCommon__ext1__cond (IMS_ParametersCommon__ext1 z) /\
  True).


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
Definition IMS_ParametersCommon__voiceOverEUTRA_5GC__Format : T_Format IMS_ParametersCommon__voiceOverEUTRA_5GC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format IMS_ParametersCommon__voiceOverEUTRA_5GC__nat__Format IMS_ParametersCommon__voiceOverEUTRA_5GC__F1 IMS_ParametersCommon__voiceOverEUTRA_5GC__F2 IMS_ParametersCommon__voiceOverEUTRA_5GC__F1F2 IMS_ParametersCommon__voiceOverEUTRA_5GC__F2F1.

Opaque IMS_ParametersCommon__voiceOverEUTRA_5GC__cond IMS_ParametersCommon__voiceOverEUTRA_5GC__Format.

Definition IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Format : T_Format IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__nat__Format IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F1 IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F2 IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F1F2 IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__F2F1.

Opaque IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__cond IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Format.


Definition IMS_ParametersCommon__ext0O__Format_Type := Eval cbn in seq_format_prod IMS_ParametersCommon__ext0O__list.
Definition IMS_ParametersCommon__ext0O__Format_list : IMS_ParametersCommon__ext0O__Format_Type :=
  (IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC__Format, unit_format).
Definition IMS_ParametersCommon__ext0O__list__Format := (*Eval compute in *) seq_format IMS_ParametersCommon__ext0O__list IMS_ParametersCommon__ext0O__Format_list.
Definition IMS_ParametersCommon__ext0O__F1 z :=
  (IMS_ParametersCommon__ext0O__voiceOverSCG_BearerEUTRA_5GC z, tt).
Definition IMS_ParametersCommon__ext0O__F2 (y : seq_type IMS_ParametersCommon__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__IMS_ParametersCommon__ext0O__Type i0
  end.
Lemma IMS_ParametersCommon__ext0O__F1F2_cond (z : IMS_ParametersCommon__ext0O__Type)
  : IMS_ParametersCommon__ext0O__cond z ->
  (seq_cond IMS_ParametersCommon__ext0O__list (IMS_ParametersCommon__ext0O__F1 z)).
intro H. unfold IMS_ParametersCommon__ext0O__cond in H. simpl. auto. Qed.
Lemma IMS_ParametersCommon__ext0O__F1F2_cond2 (z : IMS_ParametersCommon__ext0O__Type)
 : IMS_ParametersCommon__ext0O__F2 (IMS_ParametersCommon__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma IMS_ParametersCommon__ext0O__F2F1_cond (y : seq_type IMS_ParametersCommon__ext0O__list)
  : seq_cond IMS_ParametersCommon__ext0O__list y ->
 (IMS_ParametersCommon__ext0O__cond (IMS_ParametersCommon__ext0O__F2 y)) /\  IMS_ParametersCommon__ext0O__F1 (IMS_ParametersCommon__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold IMS_ParametersCommon__ext0O__cond. simpl in *. auto.
 - simpl. unfold IMS_ParametersCommon__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition IMS_ParametersCommon__ext0O__Format : T_Format IMS_ParametersCommon__ext0O__Type IMS_ParametersCommon__ext0O__cond :=
        proj2_format  IMS_ParametersCommon__ext0O__cond IMS_ParametersCommon__ext0O__list__Format
    IMS_ParametersCommon__ext0O__F1 IMS_ParametersCommon__ext0O__F2 IMS_ParametersCommon__ext0O__F1F2_cond  IMS_ParametersCommon__ext0O__F1F2_cond2 IMS_ParametersCommon__ext0O__F2F1_cond.
Opaque IMS_ParametersCommon__ext0O__cond IMS_ParametersCommon__ext0O__Format.

Definition IMS_ParametersCommon__ext0__check_all_none (b : IMS_ParametersCommon__ext0O__Type) : bool :=
match b with 
  | make__IMS_ParametersCommon__ext0O__Type None  => false 
  | _ => true 
 end.
Definition IMS_ParametersCommon__ext0__Format : T_Format IMS_ParametersCommon__ext0__Type IMS_ParametersCommon__ext0__cond :=
  restrict_add_format IMS_ParametersCommon__ext0__check_all_none IMS_ParametersCommon__ext0O__Format.

Opaque IMS_ParametersCommon__ext0__cond IMS_ParametersCommon__ext0__Format.

Definition IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Format : T_Format IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__nat__Format IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F1 IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F2 IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F1F2 IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__F2F1.

Opaque IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__cond IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Format.


Definition IMS_ParametersCommon__ext1O__Format_Type := Eval cbn in seq_format_prod IMS_ParametersCommon__ext1O__list.
Definition IMS_ParametersCommon__ext1O__Format_list : IMS_ParametersCommon__ext1O__Format_Type :=
  (IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16__Format, unit_format).
Definition IMS_ParametersCommon__ext1O__list__Format := (*Eval compute in *) seq_format IMS_ParametersCommon__ext1O__list IMS_ParametersCommon__ext1O__Format_list.
Definition IMS_ParametersCommon__ext1O__F1 z :=
  (IMS_ParametersCommon__ext1O__voiceFallbackIndicationEPS_r16 z, tt).
Definition IMS_ParametersCommon__ext1O__F2 (y : seq_type IMS_ParametersCommon__ext1O__list) :=
  match y with
  | (i0, _)=>
    make__IMS_ParametersCommon__ext1O__Type i0
  end.
Lemma IMS_ParametersCommon__ext1O__F1F2_cond (z : IMS_ParametersCommon__ext1O__Type)
  : IMS_ParametersCommon__ext1O__cond z ->
  (seq_cond IMS_ParametersCommon__ext1O__list (IMS_ParametersCommon__ext1O__F1 z)).
intro H. unfold IMS_ParametersCommon__ext1O__cond in H. simpl. auto. Qed.
Lemma IMS_ParametersCommon__ext1O__F1F2_cond2 (z : IMS_ParametersCommon__ext1O__Type)
 : IMS_ParametersCommon__ext1O__F2 (IMS_ParametersCommon__ext1O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma IMS_ParametersCommon__ext1O__F2F1_cond (y : seq_type IMS_ParametersCommon__ext1O__list)
  : seq_cond IMS_ParametersCommon__ext1O__list y ->
 (IMS_ParametersCommon__ext1O__cond (IMS_ParametersCommon__ext1O__F2 y)) /\  IMS_ParametersCommon__ext1O__F1 (IMS_ParametersCommon__ext1O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold IMS_ParametersCommon__ext1O__cond. simpl in *. auto.
 - simpl. unfold IMS_ParametersCommon__ext1O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition IMS_ParametersCommon__ext1O__Format : T_Format IMS_ParametersCommon__ext1O__Type IMS_ParametersCommon__ext1O__cond :=
        proj2_format  IMS_ParametersCommon__ext1O__cond IMS_ParametersCommon__ext1O__list__Format
    IMS_ParametersCommon__ext1O__F1 IMS_ParametersCommon__ext1O__F2 IMS_ParametersCommon__ext1O__F1F2_cond  IMS_ParametersCommon__ext1O__F1F2_cond2 IMS_ParametersCommon__ext1O__F2F1_cond.
Opaque IMS_ParametersCommon__ext1O__cond IMS_ParametersCommon__ext1O__Format.

Definition IMS_ParametersCommon__ext1__check_all_none (b : IMS_ParametersCommon__ext1O__Type) : bool :=
match b with 
  | make__IMS_ParametersCommon__ext1O__Type None  => false 
  | _ => true 
 end.
Definition IMS_ParametersCommon__ext1__Format : T_Format IMS_ParametersCommon__ext1__Type IMS_ParametersCommon__ext1__cond :=
  restrict_add_format IMS_ParametersCommon__ext1__check_all_none IMS_ParametersCommon__ext1O__Format.

Opaque IMS_ParametersCommon__ext1__cond IMS_ParametersCommon__ext1__Format.


Definition IMS_ParametersCommon__root_Format_Type := Eval cbn in seq_format_prod IMS_ParametersCommon__root_list.
Definition IMS_ParametersCommon__root_Format_list : IMS_ParametersCommon__root_Format_Type :=
  (IMS_ParametersCommon__voiceOverEUTRA_5GC__Format, unit_format).

Definition IMS_ParametersCommon__ext_Format_Type := Eval cbn in get_formats IMS_ParametersCommon__ext_list.
Definition IMS_ParametersCommon__ext_Format_list : IMS_ParametersCommon__ext_Format_Type :=
  (IMS_ParametersCommon__ext0__Format, (IMS_ParametersCommon__ext1__Format, unit__Format)).

Definition IMS_ParametersCommon__list_type : Set := (seq_type IMS_ParametersCommon__root_list) * (seq_ext_type IMS_ParametersCommon__ext_list).
Definition IMS_ParametersCommon__list_cond (z : IMS_ParametersCommon__list_type) : Prop :=
        (seq_cond IMS_ParametersCommon__root_list (fst z)) /\ (seq_ext_cond IMS_ParametersCommon__ext_list (snd z)).
Definition IMS_ParametersCommon__list_format : T_Format IMS_ParametersCommon__list_type IMS_ParametersCommon__list_cond :=
 (* Eval compute in *) seq_ext_format IMS_ParametersCommon__root_list IMS_ParametersCommon__root_Format_list IMS_ParametersCommon__ext_list IMS_ParametersCommon__ext_Format_list.

Opaque IMS_ParametersCommon__list_format.
Definition IMS_ParametersCommon__F1 (z : IMS_ParametersCommon__Type) : IMS_ParametersCommon__list_type :=
  (((IMS_ParametersCommon__voiceOverEUTRA_5GC z, tt)), (
(IMS_ParametersCommon__ext0 z, (IMS_ParametersCommon__ext1 z, tt)))).
Definition IMS_ParametersCommon__F2 (y : IMS_ParametersCommon__list_type) : IMS_ParametersCommon__Type :=
  match y with
  | ((j0, _), (i0, (i1, _)))=>
    make__IMS_ParametersCommon__Type j0 i0 i1
  end.
Definition IMS_ParametersCommon__helper1 : (forall a : IMS_ParametersCommon__Type, IMS_ParametersCommon__cond a -> IMS_ParametersCommon__list_cond (IMS_ParametersCommon__F1 a)).
                     intros. destruct a. auto. Qed.
Definition IMS_ParametersCommon__helper2 : (forall a : IMS_ParametersCommon__Type, IMS_ParametersCommon__F2 (IMS_ParametersCommon__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition IMS_ParametersCommon__helper3 : (forall b : IMS_ParametersCommon__list_type, IMS_ParametersCommon__list_cond b -> IMS_ParametersCommon__cond (IMS_ParametersCommon__F2 b) /\ IMS_ParametersCommon__F1 (IMS_ParametersCommon__F2 b) = b).
                     intros. destruct b as [y y1]. unfold IMS_ParametersCommon__cond, IMS_ParametersCommon__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition IMS_ParametersCommon__Format : T_Format IMS_ParametersCommon__Type IMS_ParametersCommon__cond :=
 proj2_format IMS_ParametersCommon__cond IMS_ParametersCommon__list_format  IMS_ParametersCommon__F1 IMS_ParametersCommon__F2 IMS_ParametersCommon__helper1 IMS_ParametersCommon__helper2 IMS_ParametersCommon__helper3.

Opaque IMS_ParametersCommon__cond IMS_ParametersCommon__Format.

