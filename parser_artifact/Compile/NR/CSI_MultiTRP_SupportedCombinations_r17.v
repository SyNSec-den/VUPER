Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Type : Set :=
 | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n2
 | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n4
 | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n8
 | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n12
 | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n16
 | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n24
 | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n32
.
Definition CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__cond := (fun (_ : CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Type) => True).
Lemma CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__nat__helper : to_bit_sz 6 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__nat__Format : T_Format nat (fun z => (z <= 6)) :=
  nat_enum_format 6 CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__nat__helper.

Definition CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F1 t :=
  match t with
  | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n2 => 0
  | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n4 => 1
  | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n8 => 2
  | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n12 => 3
  | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n16 => 4
  | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n24 => 5
  | CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n32 => 6
  end.
Definition CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F2 n :=
  match n with
  | 0 => CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n2
  | 1 => CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n4
  | 2 => CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n8
  | 3 => CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n12
  | 4 => CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n16
  | 5 => CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n24
  | 6 => CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n32
  | _ => CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__n2
  end.
Lemma CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F1F2 : forall x : CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Type, (CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F1 x <= 6) /\ CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F2 (CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F1 x) = x. imp_solve. Qed.
Lemma CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F2F1 : forall (y : nat) (H : y <= 6), CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F1 (CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F2 y) = y. enum_solve H y. Qed.

Lemma CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__helper1 : (2 <= 64)%Z.  lia. Qed.
Lemma CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__helper2 : to_bit_sz (Z.to_nat (64 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__Type := Z.
Definition CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__cond := (fun z => (2 <= z <= 64)%Z).
Lemma CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__Type := Z.
Definition CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__cond := (fun z => (2 <= z <= 256)%Z).
Record CSI_MultiTRP_SupportedCombinations_r17__Type : Set :=
  make__CSI_MultiTRP_SupportedCombinations_r17__Type {
    CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17 : CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Type ;
    CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17 : Z ;
    CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17 : Z ;
}.
Definition CSI_MultiTRP_SupportedCombinations_r17__list := (
 Nor CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Type CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__cond ::
 Nor Z CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__cond ::
 Nor Z CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__cond ::
 nil).
Definition CSI_MultiTRP_SupportedCombinations_r17__cond z := 
  CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__cond (CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17 z) /\
  CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__cond (CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17 z) /\
  CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__cond (CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17 z) /\
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
Definition CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Format : T_Format CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__nat__Format CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F1 CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F2 CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F1F2 CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__F2F1.

Opaque CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__cond CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Format.

Definition CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__Format : T_Format Z CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__cond :=
 ranged_int_format (2) (64) CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__helper1 CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__helper2.

Opaque CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__cond CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__Format.

Definition CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__Format : T_Format Z CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__cond :=
 ranged_int_format (2) (256) CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__helper1 CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__helper2.

Opaque CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__cond CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__Format.


Definition CSI_MultiTRP_SupportedCombinations_r17__Format_Type := Eval cbn in seq_format_prod CSI_MultiTRP_SupportedCombinations_r17__list.
Definition CSI_MultiTRP_SupportedCombinations_r17__Format_list : CSI_MultiTRP_SupportedCombinations_r17__Format_Type :=
  (CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17__Format, (CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17__Format, (CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17__Format, unit_format))).
Definition CSI_MultiTRP_SupportedCombinations_r17__list__Format := (*Eval compute in *) seq_format CSI_MultiTRP_SupportedCombinations_r17__list CSI_MultiTRP_SupportedCombinations_r17__Format_list.
Definition CSI_MultiTRP_SupportedCombinations_r17__F1 z :=
  (CSI_MultiTRP_SupportedCombinations_r17__maxNumTx_Ports_r17 z, (CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumCMR_r17 z, (CSI_MultiTRP_SupportedCombinations_r17__maxTotalNumTx_PortsNZP_CSI_RS_r17 z, tt))).
Definition CSI_MultiTRP_SupportedCombinations_r17__F2 (y : seq_type CSI_MultiTRP_SupportedCombinations_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__CSI_MultiTRP_SupportedCombinations_r17__Type i0 i1 i2
  end.
Lemma CSI_MultiTRP_SupportedCombinations_r17__F1F2_cond (z : CSI_MultiTRP_SupportedCombinations_r17__Type)
  : CSI_MultiTRP_SupportedCombinations_r17__cond z ->
  (seq_cond CSI_MultiTRP_SupportedCombinations_r17__list (CSI_MultiTRP_SupportedCombinations_r17__F1 z)).
intro H. unfold CSI_MultiTRP_SupportedCombinations_r17__cond in H. simpl. auto. Qed.
Lemma CSI_MultiTRP_SupportedCombinations_r17__F1F2_cond2 (z : CSI_MultiTRP_SupportedCombinations_r17__Type)
 : CSI_MultiTRP_SupportedCombinations_r17__F2 (CSI_MultiTRP_SupportedCombinations_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_MultiTRP_SupportedCombinations_r17__F2F1_cond (y : seq_type CSI_MultiTRP_SupportedCombinations_r17__list)
  : seq_cond CSI_MultiTRP_SupportedCombinations_r17__list y ->
 (CSI_MultiTRP_SupportedCombinations_r17__cond (CSI_MultiTRP_SupportedCombinations_r17__F2 y)) /\  CSI_MultiTRP_SupportedCombinations_r17__F1 (CSI_MultiTRP_SupportedCombinations_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_MultiTRP_SupportedCombinations_r17__cond. simpl in *. auto.
 - simpl. unfold CSI_MultiTRP_SupportedCombinations_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_MultiTRP_SupportedCombinations_r17__Format : T_Format CSI_MultiTRP_SupportedCombinations_r17__Type CSI_MultiTRP_SupportedCombinations_r17__cond :=
        proj2_format  CSI_MultiTRP_SupportedCombinations_r17__cond CSI_MultiTRP_SupportedCombinations_r17__list__Format
    CSI_MultiTRP_SupportedCombinations_r17__F1 CSI_MultiTRP_SupportedCombinations_r17__F2 CSI_MultiTRP_SupportedCombinations_r17__F1F2_cond  CSI_MultiTRP_SupportedCombinations_r17__F1F2_cond2 CSI_MultiTRP_SupportedCombinations_r17__F2F1_cond.
Opaque CSI_MultiTRP_SupportedCombinations_r17__cond CSI_MultiTRP_SupportedCombinations_r17__Format.

