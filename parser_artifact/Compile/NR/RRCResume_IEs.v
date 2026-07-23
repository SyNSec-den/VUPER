Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RadioBearerConfig.

Opaque RadioBearerConfig__cond RadioBearerConfig__Format.

Require Import NR.MeasConfig.

Opaque MeasConfig__cond MeasConfig__Format.

Inductive RRCResume_IEs__fullConfig__Type : Set :=
 | RRCResume_IEs__fullConfig__true
.
Definition RRCResume_IEs__fullConfig__cond := (fun (_ : RRCResume_IEs__fullConfig__Type) => True).
Lemma RRCResume_IEs__fullConfig__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RRCResume_IEs__fullConfig__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 RRCResume_IEs__fullConfig__nat__helper.

Definition RRCResume_IEs__fullConfig__F1 t :=
  match t with
  | RRCResume_IEs__fullConfig__true => 0
  end.
Definition RRCResume_IEs__fullConfig__F2 n :=
  match n with
  | 0 => RRCResume_IEs__fullConfig__true
  | _ => RRCResume_IEs__fullConfig__true
  end.
Lemma RRCResume_IEs__fullConfig__F1F2 : forall x : RRCResume_IEs__fullConfig__Type, (RRCResume_IEs__fullConfig__F1 x <= 0) /\ RRCResume_IEs__fullConfig__F2 (RRCResume_IEs__fullConfig__F1 x) = x. imp_solve. Qed.
Lemma RRCResume_IEs__fullConfig__F2F1 : forall (y : nat) (H : y <= 0), RRCResume_IEs__fullConfig__F1 (RRCResume_IEs__fullConfig__F2 y) = y. enum_solve H y. Qed.

Require Import NR.RRCResume_v1560_IEs.

Opaque RRCResume_v1560_IEs__cond RRCResume_v1560_IEs__Format.

Record RRCResume_IEs__Type : Set :=
  make__RRCResume_IEs__Type {
    RRCResume_IEs__radioBearerConfig : option RadioBearerConfig__Type ;
    RRCResume_IEs__masterCellGroup : option octet_string ;
    RRCResume_IEs__measConfig : option MeasConfig__Type ;
    RRCResume_IEs__fullConfig : option RRCResume_IEs__fullConfig__Type ;
    RRCResume_IEs__lateNonCriticalExtension : option octet_string ;
    RRCResume_IEs__nonCriticalExtension : option RRCResume_v1560_IEs__Type ;
}.
Definition RRCResume_IEs__list := (
 Opt RadioBearerConfig__Type RadioBearerConfig__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt MeasConfig__Type MeasConfig__cond ::
 Opt RRCResume_IEs__fullConfig__Type RRCResume_IEs__fullConfig__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt RRCResume_v1560_IEs__Type RRCResume_v1560_IEs__cond ::
 nil).
Definition RRCResume_IEs__cond z := 
  opt_cond RadioBearerConfig__cond (RRCResume_IEs__radioBearerConfig z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCResume_IEs__masterCellGroup z) /\
  opt_cond MeasConfig__cond (RRCResume_IEs__measConfig z) /\
  opt_cond RRCResume_IEs__fullConfig__cond (RRCResume_IEs__fullConfig z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (RRCResume_IEs__lateNonCriticalExtension z) /\
  opt_cond RRCResume_v1560_IEs__cond (RRCResume_IEs__nonCriticalExtension z) /\
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
Definition RRCResume_IEs__fullConfig__Format : T_Format RRCResume_IEs__fullConfig__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RRCResume_IEs__fullConfig__nat__Format RRCResume_IEs__fullConfig__F1 RRCResume_IEs__fullConfig__F2 RRCResume_IEs__fullConfig__F1F2 RRCResume_IEs__fullConfig__F2F1.

Opaque RRCResume_IEs__fullConfig__cond RRCResume_IEs__fullConfig__Format.


Definition RRCResume_IEs__Format_Type := Eval cbn in seq_format_prod RRCResume_IEs__list.
Definition RRCResume_IEs__Format_list : RRCResume_IEs__Format_Type :=
  (RadioBearerConfig__Format, (octet_string_nc__Format, (MeasConfig__Format, (RRCResume_IEs__fullConfig__Format, (octet_string_nc__Format, (RRCResume_v1560_IEs__Format, unit_format)))))).
Definition RRCResume_IEs__list__Format := (*Eval compute in *) seq_format RRCResume_IEs__list RRCResume_IEs__Format_list.
Definition RRCResume_IEs__F1 z :=
  (RRCResume_IEs__radioBearerConfig z, (RRCResume_IEs__masterCellGroup z, (RRCResume_IEs__measConfig z, (RRCResume_IEs__fullConfig z, (RRCResume_IEs__lateNonCriticalExtension z, (RRCResume_IEs__nonCriticalExtension z, tt)))))).
Definition RRCResume_IEs__F2 (y : seq_type RRCResume_IEs__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, _))))))=>
    make__RRCResume_IEs__Type i0 i1 i2 i3 i4 i5
  end.
Lemma RRCResume_IEs__F1F2_cond (z : RRCResume_IEs__Type)
  : RRCResume_IEs__cond z ->
  (seq_cond RRCResume_IEs__list (RRCResume_IEs__F1 z)).
intro H. unfold RRCResume_IEs__cond in H. simpl. auto. Qed.
Lemma RRCResume_IEs__F1F2_cond2 (z : RRCResume_IEs__Type)
 : RRCResume_IEs__F2 (RRCResume_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma RRCResume_IEs__F2F1_cond (y : seq_type RRCResume_IEs__list)
  : seq_cond RRCResume_IEs__list y ->
 (RRCResume_IEs__cond (RRCResume_IEs__F2 y)) /\  RRCResume_IEs__F1 (RRCResume_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold RRCResume_IEs__cond. simpl in *. auto.
 - simpl. unfold RRCResume_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition RRCResume_IEs__Format : T_Format RRCResume_IEs__Type RRCResume_IEs__cond :=
        proj2_format  RRCResume_IEs__cond RRCResume_IEs__list__Format
    RRCResume_IEs__F1 RRCResume_IEs__F2 RRCResume_IEs__F1F2_cond  RRCResume_IEs__F1F2_cond2 RRCResume_IEs__F2F1_cond.
Opaque RRCResume_IEs__cond RRCResume_IEs__Format.

