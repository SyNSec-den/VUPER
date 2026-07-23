Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ReferenceTime_r16.

Opaque ReferenceTime_r16__cond ReferenceTime_r16__Format.

Lemma ReferenceTimeInfo_r16__uncertainty_r16__helper1 : (0 <= 32767)%Z.  lia. Qed.
Lemma ReferenceTimeInfo_r16__uncertainty_r16__helper2 : to_bit_sz (Z.to_nat (32767 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32767 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ReferenceTimeInfo_r16__uncertainty_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ReferenceTimeInfo_r16__uncertainty_r16__Type := Z.
Definition ReferenceTimeInfo_r16__uncertainty_r16__cond := (fun z => (0 <= z <= 32767)%Z).
Inductive ReferenceTimeInfo_r16__timeInfoType_r16__Type : Set :=
 | ReferenceTimeInfo_r16__timeInfoType_r16__localClock
.
Definition ReferenceTimeInfo_r16__timeInfoType_r16__cond := (fun (_ : ReferenceTimeInfo_r16__timeInfoType_r16__Type) => True).
Lemma ReferenceTimeInfo_r16__timeInfoType_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReferenceTimeInfo_r16__timeInfoType_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ReferenceTimeInfo_r16__timeInfoType_r16__nat__helper.

Definition ReferenceTimeInfo_r16__timeInfoType_r16__F1 t :=
  match t with
  | ReferenceTimeInfo_r16__timeInfoType_r16__localClock => 0
  end.
Definition ReferenceTimeInfo_r16__timeInfoType_r16__F2 n :=
  match n with
  | 0 => ReferenceTimeInfo_r16__timeInfoType_r16__localClock
  | _ => ReferenceTimeInfo_r16__timeInfoType_r16__localClock
  end.
Lemma ReferenceTimeInfo_r16__timeInfoType_r16__F1F2 : forall x : ReferenceTimeInfo_r16__timeInfoType_r16__Type, (ReferenceTimeInfo_r16__timeInfoType_r16__F1 x <= 0) /\ ReferenceTimeInfo_r16__timeInfoType_r16__F2 (ReferenceTimeInfo_r16__timeInfoType_r16__F1 x) = x. imp_solve. Qed.
Lemma ReferenceTimeInfo_r16__timeInfoType_r16__F2F1 : forall (y : nat) (H : y <= 0), ReferenceTimeInfo_r16__timeInfoType_r16__F1 (ReferenceTimeInfo_r16__timeInfoType_r16__F2 y) = y. enum_solve H y. Qed.

Lemma ReferenceTimeInfo_r16__referenceSFN_r16__helper1 : (0 <= 1023)%Z.  lia. Qed.
Lemma ReferenceTimeInfo_r16__referenceSFN_r16__helper2 : to_bit_sz (Z.to_nat (1023 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1023 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply ReferenceTimeInfo_r16__referenceSFN_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ReferenceTimeInfo_r16__referenceSFN_r16__Type := Z.
Definition ReferenceTimeInfo_r16__referenceSFN_r16__cond := (fun z => (0 <= z <= 1023)%Z).
Record ReferenceTimeInfo_r16__Type : Set :=
  make__ReferenceTimeInfo_r16__Type {
    ReferenceTimeInfo_r16__time_r16 : ReferenceTime_r16__Type ;
    ReferenceTimeInfo_r16__uncertainty_r16 : option Z ;
    ReferenceTimeInfo_r16__timeInfoType_r16 : option ReferenceTimeInfo_r16__timeInfoType_r16__Type ;
    ReferenceTimeInfo_r16__referenceSFN_r16 : option Z ;
}.
Definition ReferenceTimeInfo_r16__list := (
 Nor ReferenceTime_r16__Type ReferenceTime_r16__cond ::
 Opt Z ReferenceTimeInfo_r16__uncertainty_r16__cond ::
 Opt ReferenceTimeInfo_r16__timeInfoType_r16__Type ReferenceTimeInfo_r16__timeInfoType_r16__cond ::
 Opt Z ReferenceTimeInfo_r16__referenceSFN_r16__cond ::
 nil).
Definition ReferenceTimeInfo_r16__cond z := 
  ReferenceTime_r16__cond (ReferenceTimeInfo_r16__time_r16 z) /\
  opt_cond ReferenceTimeInfo_r16__uncertainty_r16__cond (ReferenceTimeInfo_r16__uncertainty_r16 z) /\
  opt_cond ReferenceTimeInfo_r16__timeInfoType_r16__cond (ReferenceTimeInfo_r16__timeInfoType_r16 z) /\
  opt_cond ReferenceTimeInfo_r16__referenceSFN_r16__cond (ReferenceTimeInfo_r16__referenceSFN_r16 z) /\
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
Definition ReferenceTimeInfo_r16__uncertainty_r16__Format : T_Format Z ReferenceTimeInfo_r16__uncertainty_r16__cond :=
 ranged_int_format (0) (32767) ReferenceTimeInfo_r16__uncertainty_r16__helper1 ReferenceTimeInfo_r16__uncertainty_r16__helper2.

Opaque ReferenceTimeInfo_r16__uncertainty_r16__cond ReferenceTimeInfo_r16__uncertainty_r16__Format.

Definition ReferenceTimeInfo_r16__timeInfoType_r16__Format : T_Format ReferenceTimeInfo_r16__timeInfoType_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReferenceTimeInfo_r16__timeInfoType_r16__nat__Format ReferenceTimeInfo_r16__timeInfoType_r16__F1 ReferenceTimeInfo_r16__timeInfoType_r16__F2 ReferenceTimeInfo_r16__timeInfoType_r16__F1F2 ReferenceTimeInfo_r16__timeInfoType_r16__F2F1.

Opaque ReferenceTimeInfo_r16__timeInfoType_r16__cond ReferenceTimeInfo_r16__timeInfoType_r16__Format.

Definition ReferenceTimeInfo_r16__referenceSFN_r16__Format : T_Format Z ReferenceTimeInfo_r16__referenceSFN_r16__cond :=
 ranged_int_format (0) (1023) ReferenceTimeInfo_r16__referenceSFN_r16__helper1 ReferenceTimeInfo_r16__referenceSFN_r16__helper2.

Opaque ReferenceTimeInfo_r16__referenceSFN_r16__cond ReferenceTimeInfo_r16__referenceSFN_r16__Format.


Definition ReferenceTimeInfo_r16__Format_Type := Eval cbn in seq_format_prod ReferenceTimeInfo_r16__list.
Definition ReferenceTimeInfo_r16__Format_list : ReferenceTimeInfo_r16__Format_Type :=
  (ReferenceTime_r16__Format, (ReferenceTimeInfo_r16__uncertainty_r16__Format, (ReferenceTimeInfo_r16__timeInfoType_r16__Format, (ReferenceTimeInfo_r16__referenceSFN_r16__Format, unit_format)))).
Definition ReferenceTimeInfo_r16__list__Format := (*Eval compute in *) seq_format ReferenceTimeInfo_r16__list ReferenceTimeInfo_r16__Format_list.
Definition ReferenceTimeInfo_r16__F1 z :=
  (ReferenceTimeInfo_r16__time_r16 z, (ReferenceTimeInfo_r16__uncertainty_r16 z, (ReferenceTimeInfo_r16__timeInfoType_r16 z, (ReferenceTimeInfo_r16__referenceSFN_r16 z, tt)))).
Definition ReferenceTimeInfo_r16__F2 (y : seq_type ReferenceTimeInfo_r16__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__ReferenceTimeInfo_r16__Type i0 i1 i2 i3
  end.
Lemma ReferenceTimeInfo_r16__F1F2_cond (z : ReferenceTimeInfo_r16__Type)
  : ReferenceTimeInfo_r16__cond z ->
  (seq_cond ReferenceTimeInfo_r16__list (ReferenceTimeInfo_r16__F1 z)).
intro H. unfold ReferenceTimeInfo_r16__cond in H. simpl. auto. Qed.
Lemma ReferenceTimeInfo_r16__F1F2_cond2 (z : ReferenceTimeInfo_r16__Type)
 : ReferenceTimeInfo_r16__F2 (ReferenceTimeInfo_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReferenceTimeInfo_r16__F2F1_cond (y : seq_type ReferenceTimeInfo_r16__list)
  : seq_cond ReferenceTimeInfo_r16__list y ->
 (ReferenceTimeInfo_r16__cond (ReferenceTimeInfo_r16__F2 y)) /\  ReferenceTimeInfo_r16__F1 (ReferenceTimeInfo_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReferenceTimeInfo_r16__cond. simpl in *. auto.
 - simpl. unfold ReferenceTimeInfo_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReferenceTimeInfo_r16__Format : T_Format ReferenceTimeInfo_r16__Type ReferenceTimeInfo_r16__cond :=
        proj2_format  ReferenceTimeInfo_r16__cond ReferenceTimeInfo_r16__list__Format
    ReferenceTimeInfo_r16__F1 ReferenceTimeInfo_r16__F2 ReferenceTimeInfo_r16__F1F2_cond  ReferenceTimeInfo_r16__F1F2_cond2 ReferenceTimeInfo_r16__F2F1_cond.
Opaque ReferenceTimeInfo_r16__cond ReferenceTimeInfo_r16__Format.

