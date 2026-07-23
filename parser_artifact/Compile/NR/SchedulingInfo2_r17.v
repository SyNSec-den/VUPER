Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive SchedulingInfo2_r17__si_BroadcastStatus_r17__Type : Set :=
 | SchedulingInfo2_r17__si_BroadcastStatus_r17__broadcasting
 | SchedulingInfo2_r17__si_BroadcastStatus_r17__notBroadcasting
.
Definition SchedulingInfo2_r17__si_BroadcastStatus_r17__cond := (fun (_ : SchedulingInfo2_r17__si_BroadcastStatus_r17__Type) => True).
Lemma SchedulingInfo2_r17__si_BroadcastStatus_r17__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SchedulingInfo2_r17__si_BroadcastStatus_r17__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SchedulingInfo2_r17__si_BroadcastStatus_r17__nat__helper.

Definition SchedulingInfo2_r17__si_BroadcastStatus_r17__F1 t :=
  match t with
  | SchedulingInfo2_r17__si_BroadcastStatus_r17__broadcasting => 0
  | SchedulingInfo2_r17__si_BroadcastStatus_r17__notBroadcasting => 1
  end.
Definition SchedulingInfo2_r17__si_BroadcastStatus_r17__F2 n :=
  match n with
  | 0 => SchedulingInfo2_r17__si_BroadcastStatus_r17__broadcasting
  | 1 => SchedulingInfo2_r17__si_BroadcastStatus_r17__notBroadcasting
  | _ => SchedulingInfo2_r17__si_BroadcastStatus_r17__broadcasting
  end.
Lemma SchedulingInfo2_r17__si_BroadcastStatus_r17__F1F2 : forall x : SchedulingInfo2_r17__si_BroadcastStatus_r17__Type, (SchedulingInfo2_r17__si_BroadcastStatus_r17__F1 x <= 1) /\ SchedulingInfo2_r17__si_BroadcastStatus_r17__F2 (SchedulingInfo2_r17__si_BroadcastStatus_r17__F1 x) = x. imp_solve. Qed.
Lemma SchedulingInfo2_r17__si_BroadcastStatus_r17__F2F1 : forall (y : nat) (H : y <= 1), SchedulingInfo2_r17__si_BroadcastStatus_r17__F1 (SchedulingInfo2_r17__si_BroadcastStatus_r17__F2 y) = y. enum_solve H y. Qed.

Lemma SchedulingInfo2_r17__si_WindowPosition_r17__helper1 : (1 <= 256)%Z.  lia. Qed.
Lemma SchedulingInfo2_r17__si_WindowPosition_r17__helper2 : to_bit_sz (Z.to_nat (256 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SchedulingInfo2_r17__si_WindowPosition_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SchedulingInfo2_r17__si_WindowPosition_r17__Type := Z.
Definition SchedulingInfo2_r17__si_WindowPosition_r17__cond := (fun z => (1 <= z <= 256)%Z).
Inductive SchedulingInfo2_r17__si_Periodicity_r17__Type : Set :=
 | SchedulingInfo2_r17__si_Periodicity_r17__rf8
 | SchedulingInfo2_r17__si_Periodicity_r17__rf16
 | SchedulingInfo2_r17__si_Periodicity_r17__rf32
 | SchedulingInfo2_r17__si_Periodicity_r17__rf64
 | SchedulingInfo2_r17__si_Periodicity_r17__rf128
 | SchedulingInfo2_r17__si_Periodicity_r17__rf256
 | SchedulingInfo2_r17__si_Periodicity_r17__rf512
.
Definition SchedulingInfo2_r17__si_Periodicity_r17__cond := (fun (_ : SchedulingInfo2_r17__si_Periodicity_r17__Type) => True).
Lemma SchedulingInfo2_r17__si_Periodicity_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SchedulingInfo2_r17__si_Periodicity_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 SchedulingInfo2_r17__si_Periodicity_r17__nat__helper.

Definition SchedulingInfo2_r17__si_Periodicity_r17__F1 t :=
  match t with
  | SchedulingInfo2_r17__si_Periodicity_r17__rf8 => 0
  | SchedulingInfo2_r17__si_Periodicity_r17__rf16 => 1
  | SchedulingInfo2_r17__si_Periodicity_r17__rf32 => 2
  | SchedulingInfo2_r17__si_Periodicity_r17__rf64 => 3
  | SchedulingInfo2_r17__si_Periodicity_r17__rf128 => 4
  | SchedulingInfo2_r17__si_Periodicity_r17__rf256 => 5
  | SchedulingInfo2_r17__si_Periodicity_r17__rf512 => 6
  end.
Definition SchedulingInfo2_r17__si_Periodicity_r17__F2 n :=
  match n with
  | 0 => SchedulingInfo2_r17__si_Periodicity_r17__rf8
  | 1 => SchedulingInfo2_r17__si_Periodicity_r17__rf16
  | 2 => SchedulingInfo2_r17__si_Periodicity_r17__rf32
  | 3 => SchedulingInfo2_r17__si_Periodicity_r17__rf64
  | 4 => SchedulingInfo2_r17__si_Periodicity_r17__rf128
  | 5 => SchedulingInfo2_r17__si_Periodicity_r17__rf256
  | 6 => SchedulingInfo2_r17__si_Periodicity_r17__rf512
  | _ => SchedulingInfo2_r17__si_Periodicity_r17__rf8
  end.
Lemma SchedulingInfo2_r17__si_Periodicity_r17__F1F2 : forall x : SchedulingInfo2_r17__si_Periodicity_r17__Type, (SchedulingInfo2_r17__si_Periodicity_r17__F1 x <= 6) /\ SchedulingInfo2_r17__si_Periodicity_r17__F2 (SchedulingInfo2_r17__si_Periodicity_r17__F1 x) = x. imp_solve. Qed.
Lemma SchedulingInfo2_r17__si_Periodicity_r17__F2F1 : forall (y : nat) (H : y <= 6), SchedulingInfo2_r17__si_Periodicity_r17__F1 (SchedulingInfo2_r17__si_Periodicity_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SIB_Mapping_v1700.

Opaque SIB_Mapping_v1700__cond SIB_Mapping_v1700__Format.

Record SchedulingInfo2_r17__Type : Set :=
  make__SchedulingInfo2_r17__Type {
    SchedulingInfo2_r17__si_BroadcastStatus_r17 : SchedulingInfo2_r17__si_BroadcastStatus_r17__Type ;
    SchedulingInfo2_r17__si_WindowPosition_r17 : Z ;
    SchedulingInfo2_r17__si_Periodicity_r17 : SchedulingInfo2_r17__si_Periodicity_r17__Type ;
    SchedulingInfo2_r17__sib_MappingInfo_r17 : SIB_Mapping_v1700__Type ;
}.
Definition SchedulingInfo2_r17__list := (
 Nor SchedulingInfo2_r17__si_BroadcastStatus_r17__Type SchedulingInfo2_r17__si_BroadcastStatus_r17__cond ::
 Nor Z SchedulingInfo2_r17__si_WindowPosition_r17__cond ::
 Nor SchedulingInfo2_r17__si_Periodicity_r17__Type SchedulingInfo2_r17__si_Periodicity_r17__cond ::
 Nor SIB_Mapping_v1700__Type SIB_Mapping_v1700__cond ::
 nil).
Definition SchedulingInfo2_r17__cond z := 
  SchedulingInfo2_r17__si_BroadcastStatus_r17__cond (SchedulingInfo2_r17__si_BroadcastStatus_r17 z) /\
  SchedulingInfo2_r17__si_WindowPosition_r17__cond (SchedulingInfo2_r17__si_WindowPosition_r17 z) /\
  SchedulingInfo2_r17__si_Periodicity_r17__cond (SchedulingInfo2_r17__si_Periodicity_r17 z) /\
  SIB_Mapping_v1700__cond (SchedulingInfo2_r17__sib_MappingInfo_r17 z) /\
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
Definition SchedulingInfo2_r17__si_BroadcastStatus_r17__Format : T_Format SchedulingInfo2_r17__si_BroadcastStatus_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SchedulingInfo2_r17__si_BroadcastStatus_r17__nat__Format SchedulingInfo2_r17__si_BroadcastStatus_r17__F1 SchedulingInfo2_r17__si_BroadcastStatus_r17__F2 SchedulingInfo2_r17__si_BroadcastStatus_r17__F1F2 SchedulingInfo2_r17__si_BroadcastStatus_r17__F2F1.

Opaque SchedulingInfo2_r17__si_BroadcastStatus_r17__cond SchedulingInfo2_r17__si_BroadcastStatus_r17__Format.

Definition SchedulingInfo2_r17__si_WindowPosition_r17__Format : T_Format Z SchedulingInfo2_r17__si_WindowPosition_r17__cond :=
 ranged_int_format (1) (256) SchedulingInfo2_r17__si_WindowPosition_r17__helper1 SchedulingInfo2_r17__si_WindowPosition_r17__helper2.

Opaque SchedulingInfo2_r17__si_WindowPosition_r17__cond SchedulingInfo2_r17__si_WindowPosition_r17__Format.

Definition SchedulingInfo2_r17__si_Periodicity_r17__Format : T_Format SchedulingInfo2_r17__si_Periodicity_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SchedulingInfo2_r17__si_Periodicity_r17__nat__Format SchedulingInfo2_r17__si_Periodicity_r17__F1 SchedulingInfo2_r17__si_Periodicity_r17__F2 SchedulingInfo2_r17__si_Periodicity_r17__F1F2 SchedulingInfo2_r17__si_Periodicity_r17__F2F1.

Opaque SchedulingInfo2_r17__si_Periodicity_r17__cond SchedulingInfo2_r17__si_Periodicity_r17__Format.


Definition SchedulingInfo2_r17__Format_Type := Eval cbn in seq_format_prod SchedulingInfo2_r17__list.
Definition SchedulingInfo2_r17__Format_list : SchedulingInfo2_r17__Format_Type :=
  (SchedulingInfo2_r17__si_BroadcastStatus_r17__Format, (SchedulingInfo2_r17__si_WindowPosition_r17__Format, (SchedulingInfo2_r17__si_Periodicity_r17__Format, (SIB_Mapping_v1700__Format, unit_format)))).
Definition SchedulingInfo2_r17__list__Format := (*Eval compute in *) seq_format SchedulingInfo2_r17__list SchedulingInfo2_r17__Format_list.
Definition SchedulingInfo2_r17__F1 z :=
  (SchedulingInfo2_r17__si_BroadcastStatus_r17 z, (SchedulingInfo2_r17__si_WindowPosition_r17 z, (SchedulingInfo2_r17__si_Periodicity_r17 z, (SchedulingInfo2_r17__sib_MappingInfo_r17 z, tt)))).
Definition SchedulingInfo2_r17__F2 (y : seq_type SchedulingInfo2_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__SchedulingInfo2_r17__Type i0 i1 i2 i3
  end.
Lemma SchedulingInfo2_r17__F1F2_cond (z : SchedulingInfo2_r17__Type)
  : SchedulingInfo2_r17__cond z ->
  (seq_cond SchedulingInfo2_r17__list (SchedulingInfo2_r17__F1 z)).
intro H. unfold SchedulingInfo2_r17__cond in H. simpl. auto. Qed.
Lemma SchedulingInfo2_r17__F1F2_cond2 (z : SchedulingInfo2_r17__Type)
 : SchedulingInfo2_r17__F2 (SchedulingInfo2_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SchedulingInfo2_r17__F2F1_cond (y : seq_type SchedulingInfo2_r17__list)
  : seq_cond SchedulingInfo2_r17__list y ->
 (SchedulingInfo2_r17__cond (SchedulingInfo2_r17__F2 y)) /\  SchedulingInfo2_r17__F1 (SchedulingInfo2_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SchedulingInfo2_r17__cond. simpl in *. auto.
 - simpl. unfold SchedulingInfo2_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SchedulingInfo2_r17__Format : T_Format SchedulingInfo2_r17__Type SchedulingInfo2_r17__cond :=
        proj2_format  SchedulingInfo2_r17__cond SchedulingInfo2_r17__list__Format
    SchedulingInfo2_r17__F1 SchedulingInfo2_r17__F2 SchedulingInfo2_r17__F1F2_cond  SchedulingInfo2_r17__F1F2_cond2 SchedulingInfo2_r17__F2F1_cond.
Opaque SchedulingInfo2_r17__cond SchedulingInfo2_r17__Format.

