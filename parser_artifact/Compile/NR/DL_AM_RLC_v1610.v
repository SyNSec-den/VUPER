Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.T_StatusProhibit_v1610.

Opaque T_StatusProhibit_v1610__cond T_StatusProhibit_v1610__Format.

Record DL_AM_RLC_v1610__Type : Set :=
  make__DL_AM_RLC_v1610__Type {
    DL_AM_RLC_v1610__t_StatusProhibit_v1610 : option T_StatusProhibit_v1610__Type ;
}.
Definition DL_AM_RLC_v1610__root_list : list seq_elem := (
 Opt T_StatusProhibit_v1610__Type T_StatusProhibit_v1610__cond ::
 nil).
Definition DL_AM_RLC_v1610__ext_list : list typ := (
  nil).
Definition DL_AM_RLC_v1610__cond (z : DL_AM_RLC_v1610__Type) := 
(  opt_cond T_StatusProhibit_v1610__cond (DL_AM_RLC_v1610__t_StatusProhibit_v1610 z) /\
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

Definition DL_AM_RLC_v1610__root_Format_Type := Eval cbn in seq_format_prod DL_AM_RLC_v1610__root_list.
Definition DL_AM_RLC_v1610__root_Format_list : DL_AM_RLC_v1610__root_Format_Type :=
  (T_StatusProhibit_v1610__Format, unit_format).

Definition DL_AM_RLC_v1610__ext_Format_Type := Eval cbn in get_formats DL_AM_RLC_v1610__ext_list.
Definition DL_AM_RLC_v1610__ext_Format_list : DL_AM_RLC_v1610__ext_Format_Type :=
  unit__Format.

Definition DL_AM_RLC_v1610__list_type : Set := (seq_type DL_AM_RLC_v1610__root_list) * (seq_ext_type DL_AM_RLC_v1610__ext_list).
Definition DL_AM_RLC_v1610__list_cond (z : DL_AM_RLC_v1610__list_type) : Prop :=
        (seq_cond DL_AM_RLC_v1610__root_list (fst z)) /\ (seq_ext_cond DL_AM_RLC_v1610__ext_list (snd z)).
Definition DL_AM_RLC_v1610__list_format : T_Format DL_AM_RLC_v1610__list_type DL_AM_RLC_v1610__list_cond :=
 (* Eval compute in *) seq_ext_format DL_AM_RLC_v1610__root_list DL_AM_RLC_v1610__root_Format_list DL_AM_RLC_v1610__ext_list DL_AM_RLC_v1610__ext_Format_list.

Opaque DL_AM_RLC_v1610__list_format.
Definition DL_AM_RLC_v1610__F1 (z : DL_AM_RLC_v1610__Type) : DL_AM_RLC_v1610__list_type :=
  (((DL_AM_RLC_v1610__t_StatusProhibit_v1610 z, tt)), (
tt)).
Definition DL_AM_RLC_v1610__F2 (y : DL_AM_RLC_v1610__list_type) : DL_AM_RLC_v1610__Type :=
  match y with
  | ((j0, _), _)=>
    make__DL_AM_RLC_v1610__Type j0
  end.
Definition DL_AM_RLC_v1610__helper1 : (forall a : DL_AM_RLC_v1610__Type, DL_AM_RLC_v1610__cond a -> DL_AM_RLC_v1610__list_cond (DL_AM_RLC_v1610__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DL_AM_RLC_v1610__helper2 : (forall a : DL_AM_RLC_v1610__Type, DL_AM_RLC_v1610__F2 (DL_AM_RLC_v1610__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DL_AM_RLC_v1610__helper3 : (forall b : DL_AM_RLC_v1610__list_type, DL_AM_RLC_v1610__list_cond b -> DL_AM_RLC_v1610__cond (DL_AM_RLC_v1610__F2 b) /\ DL_AM_RLC_v1610__F1 (DL_AM_RLC_v1610__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DL_AM_RLC_v1610__cond, DL_AM_RLC_v1610__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DL_AM_RLC_v1610__Format : T_Format DL_AM_RLC_v1610__Type DL_AM_RLC_v1610__cond :=
 proj2_format DL_AM_RLC_v1610__cond DL_AM_RLC_v1610__list_format  DL_AM_RLC_v1610__F1 DL_AM_RLC_v1610__F2 DL_AM_RLC_v1610__helper1 DL_AM_RLC_v1610__helper2 DL_AM_RLC_v1610__helper3.

Opaque DL_AM_RLC_v1610__cond DL_AM_RLC_v1610__Format.

