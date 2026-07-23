Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma RxTxTimeDiff_r17__result_k5_r17__helper1 : (0 <= 61565)%Z.  lia. Qed.
Lemma RxTxTimeDiff_r17__result_k5_r17__helper2 : to_bit_sz (Z.to_nat (61565 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (61565 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply RxTxTimeDiff_r17__result_k5_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RxTxTimeDiff_r17__result_k5_r17__Type := Z.
Definition RxTxTimeDiff_r17__result_k5_r17__cond := (fun z => (0 <= z <= 61565)%Z).
Record RxTxTimeDiff_r17__Type : Set :=
  make__RxTxTimeDiff_r17__Type {
    RxTxTimeDiff_r17__result_k5_r17 : option Z ;
}.
Definition RxTxTimeDiff_r17__root_list : list seq_elem := (
 Opt Z RxTxTimeDiff_r17__result_k5_r17__cond ::
 nil).
Definition RxTxTimeDiff_r17__ext_list : list typ := (
  nil).
Definition RxTxTimeDiff_r17__cond (z : RxTxTimeDiff_r17__Type) := 
(  opt_cond RxTxTimeDiff_r17__result_k5_r17__cond (RxTxTimeDiff_r17__result_k5_r17 z) /\
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
Definition RxTxTimeDiff_r17__result_k5_r17__Format : T_Format Z RxTxTimeDiff_r17__result_k5_r17__cond :=
 ranged_int_format (0) (61565) RxTxTimeDiff_r17__result_k5_r17__helper1 RxTxTimeDiff_r17__result_k5_r17__helper2.

Opaque RxTxTimeDiff_r17__result_k5_r17__cond RxTxTimeDiff_r17__result_k5_r17__Format.


Definition RxTxTimeDiff_r17__root_Format_Type := Eval cbn in seq_format_prod RxTxTimeDiff_r17__root_list.
Definition RxTxTimeDiff_r17__root_Format_list : RxTxTimeDiff_r17__root_Format_Type :=
  (RxTxTimeDiff_r17__result_k5_r17__Format, unit_format).

Definition RxTxTimeDiff_r17__ext_Format_Type := Eval cbn in get_formats RxTxTimeDiff_r17__ext_list.
Definition RxTxTimeDiff_r17__ext_Format_list : RxTxTimeDiff_r17__ext_Format_Type :=
  unit__Format.

Definition RxTxTimeDiff_r17__list_type : Set := (seq_type RxTxTimeDiff_r17__root_list) * (seq_ext_type RxTxTimeDiff_r17__ext_list).
Definition RxTxTimeDiff_r17__list_cond (z : RxTxTimeDiff_r17__list_type) : Prop :=
        (seq_cond RxTxTimeDiff_r17__root_list (fst z)) /\ (seq_ext_cond RxTxTimeDiff_r17__ext_list (snd z)).
Definition RxTxTimeDiff_r17__list_format : T_Format RxTxTimeDiff_r17__list_type RxTxTimeDiff_r17__list_cond :=
 (* Eval compute in *) seq_ext_format RxTxTimeDiff_r17__root_list RxTxTimeDiff_r17__root_Format_list RxTxTimeDiff_r17__ext_list RxTxTimeDiff_r17__ext_Format_list.

Opaque RxTxTimeDiff_r17__list_format.
Definition RxTxTimeDiff_r17__F1 (z : RxTxTimeDiff_r17__Type) : RxTxTimeDiff_r17__list_type :=
  (((RxTxTimeDiff_r17__result_k5_r17 z, tt)), (
tt)).
Definition RxTxTimeDiff_r17__F2 (y : RxTxTimeDiff_r17__list_type) : RxTxTimeDiff_r17__Type :=
  match y with
  | ((j0, _), _)=>
    make__RxTxTimeDiff_r17__Type j0
  end.
Definition RxTxTimeDiff_r17__helper1 : (forall a : RxTxTimeDiff_r17__Type, RxTxTimeDiff_r17__cond a -> RxTxTimeDiff_r17__list_cond (RxTxTimeDiff_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RxTxTimeDiff_r17__helper2 : (forall a : RxTxTimeDiff_r17__Type, RxTxTimeDiff_r17__F2 (RxTxTimeDiff_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RxTxTimeDiff_r17__helper3 : (forall b : RxTxTimeDiff_r17__list_type, RxTxTimeDiff_r17__list_cond b -> RxTxTimeDiff_r17__cond (RxTxTimeDiff_r17__F2 b) /\ RxTxTimeDiff_r17__F1 (RxTxTimeDiff_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RxTxTimeDiff_r17__cond, RxTxTimeDiff_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RxTxTimeDiff_r17__Format : T_Format RxTxTimeDiff_r17__Type RxTxTimeDiff_r17__cond :=
 proj2_format RxTxTimeDiff_r17__cond RxTxTimeDiff_r17__list_format  RxTxTimeDiff_r17__F1 RxTxTimeDiff_r17__F2 RxTxTimeDiff_r17__helper1 RxTxTimeDiff_r17__helper2 RxTxTimeDiff_r17__helper3.

Opaque RxTxTimeDiff_r17__cond RxTxTimeDiff_r17__Format.

