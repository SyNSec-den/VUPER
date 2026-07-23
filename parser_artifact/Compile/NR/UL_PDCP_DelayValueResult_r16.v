Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DRB_Identity.

Opaque DRB_Identity__cond DRB_Identity__Format.

Lemma UL_PDCP_DelayValueResult_r16__averageDelay_r16__helper1 : (0 <= 10000)%Z.  lia. Qed.
Lemma UL_PDCP_DelayValueResult_r16__averageDelay_r16__helper2 : to_bit_sz (Z.to_nat (10000 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10000 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply UL_PDCP_DelayValueResult_r16__averageDelay_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition UL_PDCP_DelayValueResult_r16__averageDelay_r16__Type := Z.
Definition UL_PDCP_DelayValueResult_r16__averageDelay_r16__cond := (fun z => (0 <= z <= 10000)%Z).
Record UL_PDCP_DelayValueResult_r16__Type : Set :=
  make__UL_PDCP_DelayValueResult_r16__Type {
    UL_PDCP_DelayValueResult_r16__drb_Id_r16 : DRB_Identity__Type ;
    UL_PDCP_DelayValueResult_r16__averageDelay_r16 : Z ;
}.
Definition UL_PDCP_DelayValueResult_r16__root_list : list seq_elem := (
 Nor DRB_Identity__Type DRB_Identity__cond ::
 Nor Z UL_PDCP_DelayValueResult_r16__averageDelay_r16__cond ::
 nil).
Definition UL_PDCP_DelayValueResult_r16__ext_list : list typ := (
  nil).
Definition UL_PDCP_DelayValueResult_r16__cond (z : UL_PDCP_DelayValueResult_r16__Type) := 
(  DRB_Identity__cond (UL_PDCP_DelayValueResult_r16__drb_Id_r16 z) /\
  UL_PDCP_DelayValueResult_r16__averageDelay_r16__cond (UL_PDCP_DelayValueResult_r16__averageDelay_r16 z) /\
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
Definition UL_PDCP_DelayValueResult_r16__averageDelay_r16__Format : T_Format Z UL_PDCP_DelayValueResult_r16__averageDelay_r16__cond :=
 ranged_int_format (0) (10000) UL_PDCP_DelayValueResult_r16__averageDelay_r16__helper1 UL_PDCP_DelayValueResult_r16__averageDelay_r16__helper2.

Opaque UL_PDCP_DelayValueResult_r16__averageDelay_r16__cond UL_PDCP_DelayValueResult_r16__averageDelay_r16__Format.


Definition UL_PDCP_DelayValueResult_r16__root_Format_Type := Eval cbn in seq_format_prod UL_PDCP_DelayValueResult_r16__root_list.
Definition UL_PDCP_DelayValueResult_r16__root_Format_list : UL_PDCP_DelayValueResult_r16__root_Format_Type :=
  (DRB_Identity__Format, (UL_PDCP_DelayValueResult_r16__averageDelay_r16__Format, unit_format)).

Definition UL_PDCP_DelayValueResult_r16__ext_Format_Type := Eval cbn in get_formats UL_PDCP_DelayValueResult_r16__ext_list.
Definition UL_PDCP_DelayValueResult_r16__ext_Format_list : UL_PDCP_DelayValueResult_r16__ext_Format_Type :=
  unit__Format.

Definition UL_PDCP_DelayValueResult_r16__list_type : Set := (seq_type UL_PDCP_DelayValueResult_r16__root_list) * (seq_ext_type UL_PDCP_DelayValueResult_r16__ext_list).
Definition UL_PDCP_DelayValueResult_r16__list_cond (z : UL_PDCP_DelayValueResult_r16__list_type) : Prop :=
        (seq_cond UL_PDCP_DelayValueResult_r16__root_list (fst z)) /\ (seq_ext_cond UL_PDCP_DelayValueResult_r16__ext_list (snd z)).
Definition UL_PDCP_DelayValueResult_r16__list_format : T_Format UL_PDCP_DelayValueResult_r16__list_type UL_PDCP_DelayValueResult_r16__list_cond :=
 (* Eval compute in *) seq_ext_format UL_PDCP_DelayValueResult_r16__root_list UL_PDCP_DelayValueResult_r16__root_Format_list UL_PDCP_DelayValueResult_r16__ext_list UL_PDCP_DelayValueResult_r16__ext_Format_list.

Opaque UL_PDCP_DelayValueResult_r16__list_format.
Definition UL_PDCP_DelayValueResult_r16__F1 (z : UL_PDCP_DelayValueResult_r16__Type) : UL_PDCP_DelayValueResult_r16__list_type :=
  (((UL_PDCP_DelayValueResult_r16__drb_Id_r16 z, (UL_PDCP_DelayValueResult_r16__averageDelay_r16 z, tt))), (
tt)).
Definition UL_PDCP_DelayValueResult_r16__F2 (y : UL_PDCP_DelayValueResult_r16__list_type) : UL_PDCP_DelayValueResult_r16__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__UL_PDCP_DelayValueResult_r16__Type j0 j1
  end.
Definition UL_PDCP_DelayValueResult_r16__helper1 : (forall a : UL_PDCP_DelayValueResult_r16__Type, UL_PDCP_DelayValueResult_r16__cond a -> UL_PDCP_DelayValueResult_r16__list_cond (UL_PDCP_DelayValueResult_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition UL_PDCP_DelayValueResult_r16__helper2 : (forall a : UL_PDCP_DelayValueResult_r16__Type, UL_PDCP_DelayValueResult_r16__F2 (UL_PDCP_DelayValueResult_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition UL_PDCP_DelayValueResult_r16__helper3 : (forall b : UL_PDCP_DelayValueResult_r16__list_type, UL_PDCP_DelayValueResult_r16__list_cond b -> UL_PDCP_DelayValueResult_r16__cond (UL_PDCP_DelayValueResult_r16__F2 b) /\ UL_PDCP_DelayValueResult_r16__F1 (UL_PDCP_DelayValueResult_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold UL_PDCP_DelayValueResult_r16__cond, UL_PDCP_DelayValueResult_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition UL_PDCP_DelayValueResult_r16__Format : T_Format UL_PDCP_DelayValueResult_r16__Type UL_PDCP_DelayValueResult_r16__cond :=
 proj2_format UL_PDCP_DelayValueResult_r16__cond UL_PDCP_DelayValueResult_r16__list_format  UL_PDCP_DelayValueResult_r16__F1 UL_PDCP_DelayValueResult_r16__F2 UL_PDCP_DelayValueResult_r16__helper1 UL_PDCP_DelayValueResult_r16__helper2 UL_PDCP_DelayValueResult_r16__helper3.

Opaque UL_PDCP_DelayValueResult_r16__cond UL_PDCP_DelayValueResult_r16__Format.

