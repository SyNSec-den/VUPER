Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ARFCN_ValueEUTRA.

Opaque ARFCN_ValueEUTRA__cond ARFCN_ValueEUTRA__Format.

Lemma EUTRA_RSTD_Info__measPRS_Offset__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma EUTRA_RSTD_Info__measPRS_Offset__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply EUTRA_RSTD_Info__measPRS_Offset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition EUTRA_RSTD_Info__measPRS_Offset__Type := Z.
Definition EUTRA_RSTD_Info__measPRS_Offset__cond := (fun z => (0 <= z <= 39)%Z).
Record EUTRA_RSTD_Info__Type : Set :=
  make__EUTRA_RSTD_Info__Type {
    EUTRA_RSTD_Info__carrierFreq : ARFCN_ValueEUTRA__Type ;
    EUTRA_RSTD_Info__measPRS_Offset : Z ;
}.
Definition EUTRA_RSTD_Info__root_list : list seq_elem := (
 Nor ARFCN_ValueEUTRA__Type ARFCN_ValueEUTRA__cond ::
 Nor Z EUTRA_RSTD_Info__measPRS_Offset__cond ::
 nil).
Definition EUTRA_RSTD_Info__ext_list : list typ := (
  nil).
Definition EUTRA_RSTD_Info__cond (z : EUTRA_RSTD_Info__Type) := 
(  ARFCN_ValueEUTRA__cond (EUTRA_RSTD_Info__carrierFreq z) /\
  EUTRA_RSTD_Info__measPRS_Offset__cond (EUTRA_RSTD_Info__measPRS_Offset z) /\
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
Definition EUTRA_RSTD_Info__measPRS_Offset__Format : T_Format Z EUTRA_RSTD_Info__measPRS_Offset__cond :=
 ranged_int_format (0) (39) EUTRA_RSTD_Info__measPRS_Offset__helper1 EUTRA_RSTD_Info__measPRS_Offset__helper2.

Opaque EUTRA_RSTD_Info__measPRS_Offset__cond EUTRA_RSTD_Info__measPRS_Offset__Format.


Definition EUTRA_RSTD_Info__root_Format_Type := Eval cbn in seq_format_prod EUTRA_RSTD_Info__root_list.
Definition EUTRA_RSTD_Info__root_Format_list : EUTRA_RSTD_Info__root_Format_Type :=
  (ARFCN_ValueEUTRA__Format, (EUTRA_RSTD_Info__measPRS_Offset__Format, unit_format)).

Definition EUTRA_RSTD_Info__ext_Format_Type := Eval cbn in get_formats EUTRA_RSTD_Info__ext_list.
Definition EUTRA_RSTD_Info__ext_Format_list : EUTRA_RSTD_Info__ext_Format_Type :=
  unit__Format.

Definition EUTRA_RSTD_Info__list_type : Set := (seq_type EUTRA_RSTD_Info__root_list) * (seq_ext_type EUTRA_RSTD_Info__ext_list).
Definition EUTRA_RSTD_Info__list_cond (z : EUTRA_RSTD_Info__list_type) : Prop :=
        (seq_cond EUTRA_RSTD_Info__root_list (fst z)) /\ (seq_ext_cond EUTRA_RSTD_Info__ext_list (snd z)).
Definition EUTRA_RSTD_Info__list_format : T_Format EUTRA_RSTD_Info__list_type EUTRA_RSTD_Info__list_cond :=
 (* Eval compute in *) seq_ext_format EUTRA_RSTD_Info__root_list EUTRA_RSTD_Info__root_Format_list EUTRA_RSTD_Info__ext_list EUTRA_RSTD_Info__ext_Format_list.

Opaque EUTRA_RSTD_Info__list_format.
Definition EUTRA_RSTD_Info__F1 (z : EUTRA_RSTD_Info__Type) : EUTRA_RSTD_Info__list_type :=
  (((EUTRA_RSTD_Info__carrierFreq z, (EUTRA_RSTD_Info__measPRS_Offset z, tt))), (
tt)).
Definition EUTRA_RSTD_Info__F2 (y : EUTRA_RSTD_Info__list_type) : EUTRA_RSTD_Info__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__EUTRA_RSTD_Info__Type j0 j1
  end.
Definition EUTRA_RSTD_Info__helper1 : (forall a : EUTRA_RSTD_Info__Type, EUTRA_RSTD_Info__cond a -> EUTRA_RSTD_Info__list_cond (EUTRA_RSTD_Info__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EUTRA_RSTD_Info__helper2 : (forall a : EUTRA_RSTD_Info__Type, EUTRA_RSTD_Info__F2 (EUTRA_RSTD_Info__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EUTRA_RSTD_Info__helper3 : (forall b : EUTRA_RSTD_Info__list_type, EUTRA_RSTD_Info__list_cond b -> EUTRA_RSTD_Info__cond (EUTRA_RSTD_Info__F2 b) /\ EUTRA_RSTD_Info__F1 (EUTRA_RSTD_Info__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EUTRA_RSTD_Info__cond, EUTRA_RSTD_Info__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EUTRA_RSTD_Info__Format : T_Format EUTRA_RSTD_Info__Type EUTRA_RSTD_Info__cond :=
 proj2_format EUTRA_RSTD_Info__cond EUTRA_RSTD_Info__list_format  EUTRA_RSTD_Info__F1 EUTRA_RSTD_Info__F2 EUTRA_RSTD_Info__helper1 EUTRA_RSTD_Info__helper2 EUTRA_RSTD_Info__helper3.

Opaque EUTRA_RSTD_Info__cond EUTRA_RSTD_Info__Format.

