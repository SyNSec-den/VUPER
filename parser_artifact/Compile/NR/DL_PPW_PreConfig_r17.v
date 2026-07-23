Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DL_PPW_ID_r17.

Opaque DL_PPW_ID_r17__cond DL_PPW_ID_r17__Format.

Require Import NR.DL_PPW_PeriodicityAndStartSlot_r17.

Opaque DL_PPW_PeriodicityAndStartSlot_r17__cond DL_PPW_PeriodicityAndStartSlot_r17__Format.

Lemma DL_PPW_PreConfig_r17__length_r17__helper1 : (1 <= 160)%Z.  lia. Qed.
Lemma DL_PPW_PreConfig_r17__length_r17__helper2 : to_bit_sz (Z.to_nat (160 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (160 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DL_PPW_PreConfig_r17__length_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DL_PPW_PreConfig_r17__length_r17__Type := Z.
Definition DL_PPW_PreConfig_r17__length_r17__cond := (fun z => (1 <= z <= 160)%Z).
Inductive DL_PPW_PreConfig_r17__type_r17__Type : Set :=
 | DL_PPW_PreConfig_r17__type_r17__type1A
 | DL_PPW_PreConfig_r17__type_r17__type1B
 | DL_PPW_PreConfig_r17__type_r17__type2
.
Definition DL_PPW_PreConfig_r17__type_r17__cond := (fun (_ : DL_PPW_PreConfig_r17__type_r17__Type) => True).
Lemma DL_PPW_PreConfig_r17__type_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DL_PPW_PreConfig_r17__type_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 DL_PPW_PreConfig_r17__type_r17__nat__helper.

Definition DL_PPW_PreConfig_r17__type_r17__F1 t :=
  match t with
  | DL_PPW_PreConfig_r17__type_r17__type1A => 0
  | DL_PPW_PreConfig_r17__type_r17__type1B => 1
  | DL_PPW_PreConfig_r17__type_r17__type2 => 2
  end.
Definition DL_PPW_PreConfig_r17__type_r17__F2 n :=
  match n with
  | 0 => DL_PPW_PreConfig_r17__type_r17__type1A
  | 1 => DL_PPW_PreConfig_r17__type_r17__type1B
  | 2 => DL_PPW_PreConfig_r17__type_r17__type2
  | _ => DL_PPW_PreConfig_r17__type_r17__type1A
  end.
Lemma DL_PPW_PreConfig_r17__type_r17__F1F2 : forall x : DL_PPW_PreConfig_r17__type_r17__Type, (DL_PPW_PreConfig_r17__type_r17__F1 x <= 2) /\ DL_PPW_PreConfig_r17__type_r17__F2 (DL_PPW_PreConfig_r17__type_r17__F1 x) = x. imp_solve. Qed.
Lemma DL_PPW_PreConfig_r17__type_r17__F2F1 : forall (y : nat) (H : y <= 2), DL_PPW_PreConfig_r17__type_r17__F1 (DL_PPW_PreConfig_r17__type_r17__F2 y) = y. enum_solve H y. Qed.

Inductive DL_PPW_PreConfig_r17__priority_r17__Type : Set :=
 | DL_PPW_PreConfig_r17__priority_r17__st1
 | DL_PPW_PreConfig_r17__priority_r17__st2
 | DL_PPW_PreConfig_r17__priority_r17__st3
.
Definition DL_PPW_PreConfig_r17__priority_r17__cond := (fun (_ : DL_PPW_PreConfig_r17__priority_r17__Type) => True).
Lemma DL_PPW_PreConfig_r17__priority_r17__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DL_PPW_PreConfig_r17__priority_r17__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 DL_PPW_PreConfig_r17__priority_r17__nat__helper.

Definition DL_PPW_PreConfig_r17__priority_r17__F1 t :=
  match t with
  | DL_PPW_PreConfig_r17__priority_r17__st1 => 0
  | DL_PPW_PreConfig_r17__priority_r17__st2 => 1
  | DL_PPW_PreConfig_r17__priority_r17__st3 => 2
  end.
Definition DL_PPW_PreConfig_r17__priority_r17__F2 n :=
  match n with
  | 0 => DL_PPW_PreConfig_r17__priority_r17__st1
  | 1 => DL_PPW_PreConfig_r17__priority_r17__st2
  | 2 => DL_PPW_PreConfig_r17__priority_r17__st3
  | _ => DL_PPW_PreConfig_r17__priority_r17__st1
  end.
Lemma DL_PPW_PreConfig_r17__priority_r17__F1F2 : forall x : DL_PPW_PreConfig_r17__priority_r17__Type, (DL_PPW_PreConfig_r17__priority_r17__F1 x <= 2) /\ DL_PPW_PreConfig_r17__priority_r17__F2 (DL_PPW_PreConfig_r17__priority_r17__F1 x) = x. imp_solve. Qed.
Lemma DL_PPW_PreConfig_r17__priority_r17__F2F1 : forall (y : nat) (H : y <= 2), DL_PPW_PreConfig_r17__priority_r17__F1 (DL_PPW_PreConfig_r17__priority_r17__F2 y) = y. enum_solve H y. Qed.

Record DL_PPW_PreConfig_r17__Type : Set :=
  make__DL_PPW_PreConfig_r17__Type {
    DL_PPW_PreConfig_r17__dl_PPW_ID_r17 : DL_PPW_ID_r17__Type ;
    DL_PPW_PreConfig_r17__dl_PPW_PeriodicityAndStartSlot_r17 : DL_PPW_PeriodicityAndStartSlot_r17__Type ;
    DL_PPW_PreConfig_r17__length_r17 : Z ;
    DL_PPW_PreConfig_r17__type_r17 : option DL_PPW_PreConfig_r17__type_r17__Type ;
    DL_PPW_PreConfig_r17__priority_r17 : option DL_PPW_PreConfig_r17__priority_r17__Type ;
}.
Definition DL_PPW_PreConfig_r17__list := (
 Nor DL_PPW_ID_r17__Type DL_PPW_ID_r17__cond ::
 Nor DL_PPW_PeriodicityAndStartSlot_r17__Type DL_PPW_PeriodicityAndStartSlot_r17__cond ::
 Nor Z DL_PPW_PreConfig_r17__length_r17__cond ::
 Opt DL_PPW_PreConfig_r17__type_r17__Type DL_PPW_PreConfig_r17__type_r17__cond ::
 Opt DL_PPW_PreConfig_r17__priority_r17__Type DL_PPW_PreConfig_r17__priority_r17__cond ::
 nil).
Definition DL_PPW_PreConfig_r17__cond z := 
  DL_PPW_ID_r17__cond (DL_PPW_PreConfig_r17__dl_PPW_ID_r17 z) /\
  DL_PPW_PeriodicityAndStartSlot_r17__cond (DL_PPW_PreConfig_r17__dl_PPW_PeriodicityAndStartSlot_r17 z) /\
  DL_PPW_PreConfig_r17__length_r17__cond (DL_PPW_PreConfig_r17__length_r17 z) /\
  opt_cond DL_PPW_PreConfig_r17__type_r17__cond (DL_PPW_PreConfig_r17__type_r17 z) /\
  opt_cond DL_PPW_PreConfig_r17__priority_r17__cond (DL_PPW_PreConfig_r17__priority_r17 z) /\
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
Definition DL_PPW_PreConfig_r17__length_r17__Format : T_Format Z DL_PPW_PreConfig_r17__length_r17__cond :=
 ranged_int_format (1) (160) DL_PPW_PreConfig_r17__length_r17__helper1 DL_PPW_PreConfig_r17__length_r17__helper2.

Opaque DL_PPW_PreConfig_r17__length_r17__cond DL_PPW_PreConfig_r17__length_r17__Format.

Definition DL_PPW_PreConfig_r17__type_r17__Format : T_Format DL_PPW_PreConfig_r17__type_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DL_PPW_PreConfig_r17__type_r17__nat__Format DL_PPW_PreConfig_r17__type_r17__F1 DL_PPW_PreConfig_r17__type_r17__F2 DL_PPW_PreConfig_r17__type_r17__F1F2 DL_PPW_PreConfig_r17__type_r17__F2F1.

Opaque DL_PPW_PreConfig_r17__type_r17__cond DL_PPW_PreConfig_r17__type_r17__Format.

Definition DL_PPW_PreConfig_r17__priority_r17__Format : T_Format DL_PPW_PreConfig_r17__priority_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DL_PPW_PreConfig_r17__priority_r17__nat__Format DL_PPW_PreConfig_r17__priority_r17__F1 DL_PPW_PreConfig_r17__priority_r17__F2 DL_PPW_PreConfig_r17__priority_r17__F1F2 DL_PPW_PreConfig_r17__priority_r17__F2F1.

Opaque DL_PPW_PreConfig_r17__priority_r17__cond DL_PPW_PreConfig_r17__priority_r17__Format.


Definition DL_PPW_PreConfig_r17__Format_Type := Eval cbn in seq_format_prod DL_PPW_PreConfig_r17__list.
Definition DL_PPW_PreConfig_r17__Format_list : DL_PPW_PreConfig_r17__Format_Type :=
  (DL_PPW_ID_r17__Format, (DL_PPW_PeriodicityAndStartSlot_r17__Format, (DL_PPW_PreConfig_r17__length_r17__Format, (DL_PPW_PreConfig_r17__type_r17__Format, (DL_PPW_PreConfig_r17__priority_r17__Format, unit_format))))).
Definition DL_PPW_PreConfig_r17__list__Format := (*Eval compute in *) seq_format DL_PPW_PreConfig_r17__list DL_PPW_PreConfig_r17__Format_list.
Definition DL_PPW_PreConfig_r17__F1 z :=
  (DL_PPW_PreConfig_r17__dl_PPW_ID_r17 z, (DL_PPW_PreConfig_r17__dl_PPW_PeriodicityAndStartSlot_r17 z, (DL_PPW_PreConfig_r17__length_r17 z, (DL_PPW_PreConfig_r17__type_r17 z, (DL_PPW_PreConfig_r17__priority_r17 z, tt))))).
Definition DL_PPW_PreConfig_r17__F2 (y : seq_type DL_PPW_PreConfig_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__DL_PPW_PreConfig_r17__Type i0 i1 i2 i3 i4
  end.
Lemma DL_PPW_PreConfig_r17__F1F2_cond (z : DL_PPW_PreConfig_r17__Type)
  : DL_PPW_PreConfig_r17__cond z ->
  (seq_cond DL_PPW_PreConfig_r17__list (DL_PPW_PreConfig_r17__F1 z)).
intro H. unfold DL_PPW_PreConfig_r17__cond in H. simpl. auto. Qed.
Lemma DL_PPW_PreConfig_r17__F1F2_cond2 (z : DL_PPW_PreConfig_r17__Type)
 : DL_PPW_PreConfig_r17__F2 (DL_PPW_PreConfig_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DL_PPW_PreConfig_r17__F2F1_cond (y : seq_type DL_PPW_PreConfig_r17__list)
  : seq_cond DL_PPW_PreConfig_r17__list y ->
 (DL_PPW_PreConfig_r17__cond (DL_PPW_PreConfig_r17__F2 y)) /\  DL_PPW_PreConfig_r17__F1 (DL_PPW_PreConfig_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DL_PPW_PreConfig_r17__cond. simpl in *. auto.
 - simpl. unfold DL_PPW_PreConfig_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DL_PPW_PreConfig_r17__Format : T_Format DL_PPW_PreConfig_r17__Type DL_PPW_PreConfig_r17__cond :=
        proj2_format  DL_PPW_PreConfig_r17__cond DL_PPW_PreConfig_r17__list__Format
    DL_PPW_PreConfig_r17__F1 DL_PPW_PreConfig_r17__F2 DL_PPW_PreConfig_r17__F1F2_cond  DL_PPW_PreConfig_r17__F1F2_cond2 DL_PPW_PreConfig_r17__F2F1_cond.
Opaque DL_PPW_PreConfig_r17__cond DL_PPW_PreConfig_r17__Format.

