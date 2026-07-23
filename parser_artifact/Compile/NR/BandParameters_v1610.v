Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Type : Set :=
 | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2
 | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t1r4
 | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t2r2_t2r4
 | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t2r2_t1r4_t2r4
 | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t2r2
 | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t2r2_t4r4
.
Definition BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__cond := (fun (_ : BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Type) => True).
Lemma BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__nat__helper.

Definition BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F1 t :=
  match t with
  | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2 => 0
  | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t1r4 => 1
  | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t2r2_t2r4 => 2
  | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t2r2_t1r4_t2r4 => 3
  | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t2r2 => 4
  | BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t2r2_t4r4 => 5
  end.
Definition BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F2 n :=
  match n with
  | 0 => BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2
  | 1 => BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t1r4
  | 2 => BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t2r2_t2r4
  | 3 => BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2_t2r2_t1r4_t2r4
  | 4 => BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t2r2
  | 5 => BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t2r2_t4r4
  | _ => BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__t1r1_t1r2
  end.
Lemma BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F1F2 : forall x : BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Type, (BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F1 x <= 5) /\ BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F2 (BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F1 x) = x. imp_solve. Qed.
Lemma BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F2F1 : forall (y : nat) (H : y <= 5), BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F1 (BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F2 y) = y. enum_solve H y. Qed.

Record BandParameters_v1610__srs_TxSwitch_v1610__Type : Set :=
  make__BandParameters_v1610__srs_TxSwitch_v1610__Type {
    BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610 : BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Type ;
}.
Definition BandParameters_v1610__srs_TxSwitch_v1610__list := (
 Nor BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Type BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__cond ::
 nil).
Definition BandParameters_v1610__srs_TxSwitch_v1610__cond z := 
  BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__cond (BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610 z) /\
  True.

Record BandParameters_v1610__Type : Set :=
  make__BandParameters_v1610__Type {
    BandParameters_v1610__srs_TxSwitch_v1610 : option BandParameters_v1610__srs_TxSwitch_v1610__Type ;
}.
Definition BandParameters_v1610__list := (
 Opt BandParameters_v1610__srs_TxSwitch_v1610__Type BandParameters_v1610__srs_TxSwitch_v1610__cond ::
 nil).
Definition BandParameters_v1610__cond z := 
  opt_cond BandParameters_v1610__srs_TxSwitch_v1610__cond (BandParameters_v1610__srs_TxSwitch_v1610 z) /\
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
Definition BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Format : T_Format BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__nat__Format BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F1 BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F2 BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F1F2 BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__F2F1.

Opaque BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__cond BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Format.


Definition BandParameters_v1610__srs_TxSwitch_v1610__Format_Type := Eval cbn in seq_format_prod BandParameters_v1610__srs_TxSwitch_v1610__list.
Definition BandParameters_v1610__srs_TxSwitch_v1610__Format_list : BandParameters_v1610__srs_TxSwitch_v1610__Format_Type :=
  (BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610__Format, unit_format).
Definition BandParameters_v1610__srs_TxSwitch_v1610__list__Format := (*Eval compute in *) seq_format BandParameters_v1610__srs_TxSwitch_v1610__list BandParameters_v1610__srs_TxSwitch_v1610__Format_list.
Definition BandParameters_v1610__srs_TxSwitch_v1610__F1 z :=
  (BandParameters_v1610__srs_TxSwitch_v1610__supportedSRS_TxPortSwitch_v1610 z, tt).
Definition BandParameters_v1610__srs_TxSwitch_v1610__F2 (y : seq_type BandParameters_v1610__srs_TxSwitch_v1610__list) :=
  match y with
  | (i0, _)=>
    make__BandParameters_v1610__srs_TxSwitch_v1610__Type i0
  end.
Lemma BandParameters_v1610__srs_TxSwitch_v1610__F1F2_cond (z : BandParameters_v1610__srs_TxSwitch_v1610__Type)
  : BandParameters_v1610__srs_TxSwitch_v1610__cond z ->
  (seq_cond BandParameters_v1610__srs_TxSwitch_v1610__list (BandParameters_v1610__srs_TxSwitch_v1610__F1 z)).
intro H. unfold BandParameters_v1610__srs_TxSwitch_v1610__cond in H. simpl. auto. Qed.
Lemma BandParameters_v1610__srs_TxSwitch_v1610__F1F2_cond2 (z : BandParameters_v1610__srs_TxSwitch_v1610__Type)
 : BandParameters_v1610__srs_TxSwitch_v1610__F2 (BandParameters_v1610__srs_TxSwitch_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters_v1610__srs_TxSwitch_v1610__F2F1_cond (y : seq_type BandParameters_v1610__srs_TxSwitch_v1610__list)
  : seq_cond BandParameters_v1610__srs_TxSwitch_v1610__list y ->
 (BandParameters_v1610__srs_TxSwitch_v1610__cond (BandParameters_v1610__srs_TxSwitch_v1610__F2 y)) /\  BandParameters_v1610__srs_TxSwitch_v1610__F1 (BandParameters_v1610__srs_TxSwitch_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters_v1610__srs_TxSwitch_v1610__cond. simpl in *. auto.
 - simpl. unfold BandParameters_v1610__srs_TxSwitch_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters_v1610__srs_TxSwitch_v1610__Format : T_Format BandParameters_v1610__srs_TxSwitch_v1610__Type BandParameters_v1610__srs_TxSwitch_v1610__cond :=
        proj2_format  BandParameters_v1610__srs_TxSwitch_v1610__cond BandParameters_v1610__srs_TxSwitch_v1610__list__Format
    BandParameters_v1610__srs_TxSwitch_v1610__F1 BandParameters_v1610__srs_TxSwitch_v1610__F2 BandParameters_v1610__srs_TxSwitch_v1610__F1F2_cond  BandParameters_v1610__srs_TxSwitch_v1610__F1F2_cond2 BandParameters_v1610__srs_TxSwitch_v1610__F2F1_cond.
Opaque BandParameters_v1610__srs_TxSwitch_v1610__cond BandParameters_v1610__srs_TxSwitch_v1610__Format.


Definition BandParameters_v1610__Format_Type := Eval cbn in seq_format_prod BandParameters_v1610__list.
Definition BandParameters_v1610__Format_list : BandParameters_v1610__Format_Type :=
  (BandParameters_v1610__srs_TxSwitch_v1610__Format, unit_format).
Definition BandParameters_v1610__list__Format := (*Eval compute in *) seq_format BandParameters_v1610__list BandParameters_v1610__Format_list.
Definition BandParameters_v1610__F1 z :=
  (BandParameters_v1610__srs_TxSwitch_v1610 z, tt).
Definition BandParameters_v1610__F2 (y : seq_type BandParameters_v1610__list) :=
  match y with
  | (i0, _)=>
    make__BandParameters_v1610__Type i0
  end.
Lemma BandParameters_v1610__F1F2_cond (z : BandParameters_v1610__Type)
  : BandParameters_v1610__cond z ->
  (seq_cond BandParameters_v1610__list (BandParameters_v1610__F1 z)).
intro H. unfold BandParameters_v1610__cond in H. simpl. auto. Qed.
Lemma BandParameters_v1610__F1F2_cond2 (z : BandParameters_v1610__Type)
 : BandParameters_v1610__F2 (BandParameters_v1610__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParameters_v1610__F2F1_cond (y : seq_type BandParameters_v1610__list)
  : seq_cond BandParameters_v1610__list y ->
 (BandParameters_v1610__cond (BandParameters_v1610__F2 y)) /\  BandParameters_v1610__F1 (BandParameters_v1610__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParameters_v1610__cond. simpl in *. auto.
 - simpl. unfold BandParameters_v1610__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParameters_v1610__Format : T_Format BandParameters_v1610__Type BandParameters_v1610__cond :=
        proj2_format  BandParameters_v1610__cond BandParameters_v1610__list__Format
    BandParameters_v1610__F1 BandParameters_v1610__F2 BandParameters_v1610__F1F2_cond  BandParameters_v1610__F1F2_cond2 BandParameters_v1610__F2F1_cond.
Opaque BandParameters_v1610__cond BandParameters_v1610__Format.

