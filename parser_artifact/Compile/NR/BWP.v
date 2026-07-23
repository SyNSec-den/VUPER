Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma BWP__locationAndBandwidth__helper1 : (0 <= 37949)%Z.  lia. Qed.
Lemma BWP__locationAndBandwidth__helper2 : to_bit_sz (Z.to_nat (37949 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (37949 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply BWP__locationAndBandwidth__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition BWP__locationAndBandwidth__Type := Z.
Definition BWP__locationAndBandwidth__cond := (fun z => (0 <= z <= 37949)%Z).
Require Import NR.SubcarrierSpacing.

Opaque SubcarrierSpacing__cond SubcarrierSpacing__Format.

Inductive BWP__cyclicPrefix__Type : Set :=
 | BWP__cyclicPrefix__extended
.
Definition BWP__cyclicPrefix__cond := (fun (_ : BWP__cyclicPrefix__Type) => True).
Lemma BWP__cyclicPrefix__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BWP__cyclicPrefix__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BWP__cyclicPrefix__nat__helper.

Definition BWP__cyclicPrefix__F1 t :=
  match t with
  | BWP__cyclicPrefix__extended => 0
  end.
Definition BWP__cyclicPrefix__F2 n :=
  match n with
  | 0 => BWP__cyclicPrefix__extended
  | _ => BWP__cyclicPrefix__extended
  end.
Lemma BWP__cyclicPrefix__F1F2 : forall x : BWP__cyclicPrefix__Type, (BWP__cyclicPrefix__F1 x <= 0) /\ BWP__cyclicPrefix__F2 (BWP__cyclicPrefix__F1 x) = x. imp_solve. Qed.
Lemma BWP__cyclicPrefix__F2F1 : forall (y : nat) (H : y <= 0), BWP__cyclicPrefix__F1 (BWP__cyclicPrefix__F2 y) = y. enum_solve H y. Qed.

Record BWP__Type : Set :=
  make__BWP__Type {
    BWP__locationAndBandwidth : Z ;
    BWP__subcarrierSpacing : SubcarrierSpacing__Type ;
    BWP__cyclicPrefix : option BWP__cyclicPrefix__Type ;
}.
Definition BWP__list := (
 Nor Z BWP__locationAndBandwidth__cond ::
 Nor SubcarrierSpacing__Type SubcarrierSpacing__cond ::
 Opt BWP__cyclicPrefix__Type BWP__cyclicPrefix__cond ::
 nil).
Definition BWP__cond z := 
  BWP__locationAndBandwidth__cond (BWP__locationAndBandwidth z) /\
  SubcarrierSpacing__cond (BWP__subcarrierSpacing z) /\
  opt_cond BWP__cyclicPrefix__cond (BWP__cyclicPrefix z) /\
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
Definition BWP__locationAndBandwidth__Format : T_Format Z BWP__locationAndBandwidth__cond :=
 ranged_int_format (0) (37949) BWP__locationAndBandwidth__helper1 BWP__locationAndBandwidth__helper2.

Opaque BWP__locationAndBandwidth__cond BWP__locationAndBandwidth__Format.

Definition BWP__cyclicPrefix__Format : T_Format BWP__cyclicPrefix__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BWP__cyclicPrefix__nat__Format BWP__cyclicPrefix__F1 BWP__cyclicPrefix__F2 BWP__cyclicPrefix__F1F2 BWP__cyclicPrefix__F2F1.

Opaque BWP__cyclicPrefix__cond BWP__cyclicPrefix__Format.


Definition BWP__Format_Type := Eval cbn in seq_format_prod BWP__list.
Definition BWP__Format_list : BWP__Format_Type :=
  (BWP__locationAndBandwidth__Format, (SubcarrierSpacing__Format, (BWP__cyclicPrefix__Format, unit_format))).
Definition BWP__list__Format := (*Eval compute in *) seq_format BWP__list BWP__Format_list.
Definition BWP__F1 z :=
  (BWP__locationAndBandwidth z, (BWP__subcarrierSpacing z, (BWP__cyclicPrefix z, tt))).
Definition BWP__F2 (y : seq_type BWP__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BWP__Type i0 i1 i2
  end.
Lemma BWP__F1F2_cond (z : BWP__Type)
  : BWP__cond z ->
  (seq_cond BWP__list (BWP__F1 z)).
intro H. unfold BWP__cond in H. simpl. auto. Qed.
Lemma BWP__F1F2_cond2 (z : BWP__Type)
 : BWP__F2 (BWP__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BWP__F2F1_cond (y : seq_type BWP__list)
  : seq_cond BWP__list y ->
 (BWP__cond (BWP__F2 y)) /\  BWP__F1 (BWP__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BWP__cond. simpl in *. auto.
 - simpl. unfold BWP__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BWP__Format : T_Format BWP__Type BWP__cond :=
        proj2_format  BWP__cond BWP__list__Format
    BWP__F1 BWP__F2 BWP__F1F2_cond  BWP__F1F2_cond2 BWP__F2F1_cond.
Opaque BWP__cond BWP__Format.

