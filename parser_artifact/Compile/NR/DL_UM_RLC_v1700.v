Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.T_ReassemblyExt_r17.

Opaque T_ReassemblyExt_r17__cond T_ReassemblyExt_r17__Format.

Record DL_UM_RLC_v1700__Type : Set :=
  make__DL_UM_RLC_v1700__Type {
    DL_UM_RLC_v1700__t_ReassemblyExt_r17 : option T_ReassemblyExt_r17__Type ;
}.
Definition DL_UM_RLC_v1700__list := (
 Opt T_ReassemblyExt_r17__Type T_ReassemblyExt_r17__cond ::
 nil).
Definition DL_UM_RLC_v1700__cond z := 
  opt_cond T_ReassemblyExt_r17__cond (DL_UM_RLC_v1700__t_ReassemblyExt_r17 z) /\
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

Definition DL_UM_RLC_v1700__Format_Type := Eval cbn in seq_format_prod DL_UM_RLC_v1700__list.
Definition DL_UM_RLC_v1700__Format_list : DL_UM_RLC_v1700__Format_Type :=
  (T_ReassemblyExt_r17__Format, unit_format).
Definition DL_UM_RLC_v1700__list__Format := (*Eval compute in *) seq_format DL_UM_RLC_v1700__list DL_UM_RLC_v1700__Format_list.
Definition DL_UM_RLC_v1700__F1 z :=
  (DL_UM_RLC_v1700__t_ReassemblyExt_r17 z, tt).
Definition DL_UM_RLC_v1700__F2 (y : seq_type DL_UM_RLC_v1700__list) :=
  match y with
  | (i0, _)=>
    make__DL_UM_RLC_v1700__Type i0
  end.
Lemma DL_UM_RLC_v1700__F1F2_cond (z : DL_UM_RLC_v1700__Type)
  : DL_UM_RLC_v1700__cond z ->
  (seq_cond DL_UM_RLC_v1700__list (DL_UM_RLC_v1700__F1 z)).
intro H. unfold DL_UM_RLC_v1700__cond in H. simpl. auto. Qed.
Lemma DL_UM_RLC_v1700__F1F2_cond2 (z : DL_UM_RLC_v1700__Type)
 : DL_UM_RLC_v1700__F2 (DL_UM_RLC_v1700__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DL_UM_RLC_v1700__F2F1_cond (y : seq_type DL_UM_RLC_v1700__list)
  : seq_cond DL_UM_RLC_v1700__list y ->
 (DL_UM_RLC_v1700__cond (DL_UM_RLC_v1700__F2 y)) /\  DL_UM_RLC_v1700__F1 (DL_UM_RLC_v1700__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DL_UM_RLC_v1700__cond. simpl in *. auto.
 - simpl. unfold DL_UM_RLC_v1700__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DL_UM_RLC_v1700__Format : T_Format DL_UM_RLC_v1700__Type DL_UM_RLC_v1700__cond :=
        proj2_format  DL_UM_RLC_v1700__cond DL_UM_RLC_v1700__list__Format
    DL_UM_RLC_v1700__F1 DL_UM_RLC_v1700__F2 DL_UM_RLC_v1700__F1F2_cond  DL_UM_RLC_v1700__F1F2_cond2 DL_UM_RLC_v1700__F2F1_cond.
Opaque DL_UM_RLC_v1700__cond DL_UM_RLC_v1700__Format.

