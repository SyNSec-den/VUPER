Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__Type := Z.
Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__cond := (fun z => (1 <= z <= 64)%Z).
Lemma CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__Type := Z.
Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__cond := (fun z => (2 <= z <= 256)%Z).
Inductive CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Type : Set :=
 | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n1
 | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n2
 | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n4
 | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n8
 | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n16
 | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n32
.
Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__cond := (fun (_ : CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Type) => True).
Lemma CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__nat__helper.

Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F1 t :=
  match t with
  | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n1 => 0
  | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n2 => 1
  | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n4 => 2
  | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n8 => 3
  | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n16 => 4
  | CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n32 => 5
  end.
Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F2 n :=
  match n with
  | 0 => CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n1
  | 1 => CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n2
  | 2 => CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n4
  | 3 => CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n8
  | 4 => CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n16
  | 5 => CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n32
  | _ => CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__n1
  end.
Lemma CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F1F2 : forall x : CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Type, (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F1 x <= 5) /\ CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F2 (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F1 x) = x. imp_solve. Qed.
Lemma CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F2F1 : forall (y : nat) (H : y <= 5), CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F1 (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F2 y) = y. enum_solve H y. Qed.

Lemma CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__helper1 : (1 <= 64)%Z.  lia. Qed.
Lemma CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__helper2 : to_bit_sz (Z.to_nat (64 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (64 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__Type := Z.
Definition CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__cond := (fun z => (1 <= z <= 64)%Z).
Lemma CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__helper1 : (2 <= 256)%Z.  lia. Qed.
Lemma CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__helper2 : to_bit_sz (Z.to_nat (256 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (256 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__Type := Z.
Definition CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__cond := (fun z => (2 <= z <= 256)%Z).
Record CSI_RS_IM_ReceptionForFeedback__Type : Set :=
  make__CSI_RS_IM_ReceptionForFeedback__Type {
    CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC : Z ;
    CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC : Z ;
    CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC : CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Type ;
    CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC : Z ;
    CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC : Z ;
}.
Definition CSI_RS_IM_ReceptionForFeedback__list := (
 Nor Z CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__cond ::
 Nor Z CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__cond ::
 Nor CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Type CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__cond ::
 Nor Z CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__cond ::
 Nor Z CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__cond ::
 nil).
Definition CSI_RS_IM_ReceptionForFeedback__cond z := 
  CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__cond (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC z) /\
  CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__cond (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC z) /\
  CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__cond (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC z) /\
  CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__cond (CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC z) /\
  CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__cond (CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC z) /\
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
Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__Format : T_Format Z CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__cond :=
 ranged_int_format (1) (64) CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__helper1 CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__helper2.

Opaque CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__cond CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__Format.

Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__Format : T_Format Z CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__cond :=
 ranged_int_format (2) (256) CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__helper1 CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__helper2.

Opaque CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__cond CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__Format.

Definition CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Format : T_Format CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__nat__Format CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F1 CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F2 CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F1F2 CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__F2F1.

Opaque CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__cond CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Format.

Definition CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__Format : T_Format Z CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__cond :=
 ranged_int_format (1) (64) CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__helper1 CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__helper2.

Opaque CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__cond CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__Format.

Definition CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__Format : T_Format Z CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__cond :=
 ranged_int_format (2) (256) CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__helper1 CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__helper2.

Opaque CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__cond CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__Format.


Definition CSI_RS_IM_ReceptionForFeedback__Format_Type := Eval cbn in seq_format_prod CSI_RS_IM_ReceptionForFeedback__list.
Definition CSI_RS_IM_ReceptionForFeedback__Format_list : CSI_RS_IM_ReceptionForFeedback__Format_Type :=
  (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC__Format, (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC__Format, (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC__Format, (CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC__Format, (CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC__Format, unit_format))))).
Definition CSI_RS_IM_ReceptionForFeedback__list__Format := (*Eval compute in *) seq_format CSI_RS_IM_ReceptionForFeedback__list CSI_RS_IM_ReceptionForFeedback__Format_list.
Definition CSI_RS_IM_ReceptionForFeedback__F1 z :=
  (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberNZP_CSI_RS_PerCC z, (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberPortsAcrossNZP_CSI_RS_PerCC z, (CSI_RS_IM_ReceptionForFeedback__maxConfigNumberCSI_IM_PerCC z, (CSI_RS_IM_ReceptionForFeedback__maxNumberSimultaneousNZP_CSI_RS_PerCC z, (CSI_RS_IM_ReceptionForFeedback__totalNumberPortsSimultaneousNZP_CSI_RS_PerCC z, tt))))).
Definition CSI_RS_IM_ReceptionForFeedback__F2 (y : seq_type CSI_RS_IM_ReceptionForFeedback__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__CSI_RS_IM_ReceptionForFeedback__Type i0 i1 i2 i3 i4
  end.
Lemma CSI_RS_IM_ReceptionForFeedback__F1F2_cond (z : CSI_RS_IM_ReceptionForFeedback__Type)
  : CSI_RS_IM_ReceptionForFeedback__cond z ->
  (seq_cond CSI_RS_IM_ReceptionForFeedback__list (CSI_RS_IM_ReceptionForFeedback__F1 z)).
intro H. unfold CSI_RS_IM_ReceptionForFeedback__cond in H. simpl. auto. Qed.
Lemma CSI_RS_IM_ReceptionForFeedback__F1F2_cond2 (z : CSI_RS_IM_ReceptionForFeedback__Type)
 : CSI_RS_IM_ReceptionForFeedback__F2 (CSI_RS_IM_ReceptionForFeedback__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CSI_RS_IM_ReceptionForFeedback__F2F1_cond (y : seq_type CSI_RS_IM_ReceptionForFeedback__list)
  : seq_cond CSI_RS_IM_ReceptionForFeedback__list y ->
 (CSI_RS_IM_ReceptionForFeedback__cond (CSI_RS_IM_ReceptionForFeedback__F2 y)) /\  CSI_RS_IM_ReceptionForFeedback__F1 (CSI_RS_IM_ReceptionForFeedback__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CSI_RS_IM_ReceptionForFeedback__cond. simpl in *. auto.
 - simpl. unfold CSI_RS_IM_ReceptionForFeedback__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CSI_RS_IM_ReceptionForFeedback__Format : T_Format CSI_RS_IM_ReceptionForFeedback__Type CSI_RS_IM_ReceptionForFeedback__cond :=
        proj2_format  CSI_RS_IM_ReceptionForFeedback__cond CSI_RS_IM_ReceptionForFeedback__list__Format
    CSI_RS_IM_ReceptionForFeedback__F1 CSI_RS_IM_ReceptionForFeedback__F2 CSI_RS_IM_ReceptionForFeedback__F1F2_cond  CSI_RS_IM_ReceptionForFeedback__F1F2_cond2 CSI_RS_IM_ReceptionForFeedback__F2F1_cond.
Opaque CSI_RS_IM_ReceptionForFeedback__cond CSI_RS_IM_ReceptionForFeedback__Format.

