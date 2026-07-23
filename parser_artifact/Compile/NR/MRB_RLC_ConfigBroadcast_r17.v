Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.LogicalChannelIdentity.

Opaque LogicalChannelIdentity__cond LogicalChannelIdentity__Format.

Inductive MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Type : Set :=
 | MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__size6
.
Definition MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__cond := (fun (_ : MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Type) => True).
Lemma MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__nat__helper.

Definition MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F1 t :=
  match t with
  | MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__size6 => 0
  end.
Definition MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F2 n :=
  match n with
  | 0 => MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__size6
  | _ => MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__size6
  end.
Lemma MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F1F2 : forall x : MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Type, (MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F1 x <= 0) /\ MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F2 (MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F1 x) = x. imp_solve. Qed.
Lemma MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F2F1 : forall (y : nat) (H : y <= 0), MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F1 (MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.T_Reassembly.

Opaque T_Reassembly__cond T_Reassembly__Format.

Record MRB_RLC_ConfigBroadcast_r17__Type : Set :=
  make__MRB_RLC_ConfigBroadcast_r17__Type {
    MRB_RLC_ConfigBroadcast_r17__logicalChannelIdentity_r17 : LogicalChannelIdentity__Type ;
    MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17 : option MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Type ;
    MRB_RLC_ConfigBroadcast_r17__t_Reassembly_r17 : option T_Reassembly__Type ;
}.
Definition MRB_RLC_ConfigBroadcast_r17__list := (
 Nor LogicalChannelIdentity__Type LogicalChannelIdentity__cond ::
 Opt MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Type MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__cond ::
 Opt T_Reassembly__Type T_Reassembly__cond ::
 nil).
Definition MRB_RLC_ConfigBroadcast_r17__cond z := 
  LogicalChannelIdentity__cond (MRB_RLC_ConfigBroadcast_r17__logicalChannelIdentity_r17 z) /\
  opt_cond MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__cond (MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17 z) /\
  opt_cond T_Reassembly__cond (MRB_RLC_ConfigBroadcast_r17__t_Reassembly_r17 z) /\
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
Definition MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Format : T_Format MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__nat__Format MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F1 MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F2 MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F1F2 MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__F2F1.

Opaque MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__cond MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Format.


Definition MRB_RLC_ConfigBroadcast_r17__Format_Type := Eval cbn in seq_format_prod MRB_RLC_ConfigBroadcast_r17__list.
Definition MRB_RLC_ConfigBroadcast_r17__Format_list : MRB_RLC_ConfigBroadcast_r17__Format_Type :=
  (LogicalChannelIdentity__Format, (MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17__Format, (T_Reassembly__Format, unit_format))).
Definition MRB_RLC_ConfigBroadcast_r17__list__Format := (*Eval compute in *) seq_format MRB_RLC_ConfigBroadcast_r17__list MRB_RLC_ConfigBroadcast_r17__Format_list.
Definition MRB_RLC_ConfigBroadcast_r17__F1 z :=
  (MRB_RLC_ConfigBroadcast_r17__logicalChannelIdentity_r17 z, (MRB_RLC_ConfigBroadcast_r17__sn_FieldLength_r17 z, (MRB_RLC_ConfigBroadcast_r17__t_Reassembly_r17 z, tt))).
Definition MRB_RLC_ConfigBroadcast_r17__F2 (y : seq_type MRB_RLC_ConfigBroadcast_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MRB_RLC_ConfigBroadcast_r17__Type i0 i1 i2
  end.
Lemma MRB_RLC_ConfigBroadcast_r17__F1F2_cond (z : MRB_RLC_ConfigBroadcast_r17__Type)
  : MRB_RLC_ConfigBroadcast_r17__cond z ->
  (seq_cond MRB_RLC_ConfigBroadcast_r17__list (MRB_RLC_ConfigBroadcast_r17__F1 z)).
intro H. unfold MRB_RLC_ConfigBroadcast_r17__cond in H. simpl. auto. Qed.
Lemma MRB_RLC_ConfigBroadcast_r17__F1F2_cond2 (z : MRB_RLC_ConfigBroadcast_r17__Type)
 : MRB_RLC_ConfigBroadcast_r17__F2 (MRB_RLC_ConfigBroadcast_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRB_RLC_ConfigBroadcast_r17__F2F1_cond (y : seq_type MRB_RLC_ConfigBroadcast_r17__list)
  : seq_cond MRB_RLC_ConfigBroadcast_r17__list y ->
 (MRB_RLC_ConfigBroadcast_r17__cond (MRB_RLC_ConfigBroadcast_r17__F2 y)) /\  MRB_RLC_ConfigBroadcast_r17__F1 (MRB_RLC_ConfigBroadcast_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRB_RLC_ConfigBroadcast_r17__cond. simpl in *. auto.
 - simpl. unfold MRB_RLC_ConfigBroadcast_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRB_RLC_ConfigBroadcast_r17__Format : T_Format MRB_RLC_ConfigBroadcast_r17__Type MRB_RLC_ConfigBroadcast_r17__cond :=
        proj2_format  MRB_RLC_ConfigBroadcast_r17__cond MRB_RLC_ConfigBroadcast_r17__list__Format
    MRB_RLC_ConfigBroadcast_r17__F1 MRB_RLC_ConfigBroadcast_r17__F2 MRB_RLC_ConfigBroadcast_r17__F1F2_cond  MRB_RLC_ConfigBroadcast_r17__F1F2_cond2 MRB_RLC_ConfigBroadcast_r17__F2F1_cond.
Opaque MRB_RLC_ConfigBroadcast_r17__cond MRB_RLC_ConfigBroadcast_r17__Format.

