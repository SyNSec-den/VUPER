Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SN_FieldLengthAM.

Opaque SN_FieldLengthAM__cond SN_FieldLengthAM__Format.

Require Import NR.T_PollRetransmit.

Opaque T_PollRetransmit__cond T_PollRetransmit__Format.

Require Import NR.PollPDU.

Opaque PollPDU__cond PollPDU__Format.

Require Import NR.PollByte.

Opaque PollByte__cond PollByte__Format.

Inductive UL_AM_RLC__maxRetxThreshold__Type : Set :=
 | UL_AM_RLC__maxRetxThreshold__t1
 | UL_AM_RLC__maxRetxThreshold__t2
 | UL_AM_RLC__maxRetxThreshold__t3
 | UL_AM_RLC__maxRetxThreshold__t4
 | UL_AM_RLC__maxRetxThreshold__t6
 | UL_AM_RLC__maxRetxThreshold__t8
 | UL_AM_RLC__maxRetxThreshold__t16
 | UL_AM_RLC__maxRetxThreshold__t32
.
Definition UL_AM_RLC__maxRetxThreshold__cond := (fun (_ : UL_AM_RLC__maxRetxThreshold__Type) => True).
Lemma UL_AM_RLC__maxRetxThreshold__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UL_AM_RLC__maxRetxThreshold__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 UL_AM_RLC__maxRetxThreshold__nat__helper.

Definition UL_AM_RLC__maxRetxThreshold__F1 t :=
  match t with
  | UL_AM_RLC__maxRetxThreshold__t1 => 0
  | UL_AM_RLC__maxRetxThreshold__t2 => 1
  | UL_AM_RLC__maxRetxThreshold__t3 => 2
  | UL_AM_RLC__maxRetxThreshold__t4 => 3
  | UL_AM_RLC__maxRetxThreshold__t6 => 4
  | UL_AM_RLC__maxRetxThreshold__t8 => 5
  | UL_AM_RLC__maxRetxThreshold__t16 => 6
  | UL_AM_RLC__maxRetxThreshold__t32 => 7
  end.
Definition UL_AM_RLC__maxRetxThreshold__F2 n :=
  match n with
  | 0 => UL_AM_RLC__maxRetxThreshold__t1
  | 1 => UL_AM_RLC__maxRetxThreshold__t2
  | 2 => UL_AM_RLC__maxRetxThreshold__t3
  | 3 => UL_AM_RLC__maxRetxThreshold__t4
  | 4 => UL_AM_RLC__maxRetxThreshold__t6
  | 5 => UL_AM_RLC__maxRetxThreshold__t8
  | 6 => UL_AM_RLC__maxRetxThreshold__t16
  | 7 => UL_AM_RLC__maxRetxThreshold__t32
  | _ => UL_AM_RLC__maxRetxThreshold__t1
  end.
Lemma UL_AM_RLC__maxRetxThreshold__F1F2 : forall x : UL_AM_RLC__maxRetxThreshold__Type, (UL_AM_RLC__maxRetxThreshold__F1 x <= 7) /\ UL_AM_RLC__maxRetxThreshold__F2 (UL_AM_RLC__maxRetxThreshold__F1 x) = x. imp_solve. Qed.
Lemma UL_AM_RLC__maxRetxThreshold__F2F1 : forall (y : nat) (H : y <= 7), UL_AM_RLC__maxRetxThreshold__F1 (UL_AM_RLC__maxRetxThreshold__F2 y) = y. enum_solve H y. Qed.

Record UL_AM_RLC__Type : Set :=
  make__UL_AM_RLC__Type {
    UL_AM_RLC__sn_FieldLength : option SN_FieldLengthAM__Type ;
    UL_AM_RLC__t_PollRetransmit : T_PollRetransmit__Type ;
    UL_AM_RLC__pollPDU : PollPDU__Type ;
    UL_AM_RLC__pollByte : PollByte__Type ;
    UL_AM_RLC__maxRetxThreshold : UL_AM_RLC__maxRetxThreshold__Type ;
}.
Definition UL_AM_RLC__list := (
 Opt SN_FieldLengthAM__Type SN_FieldLengthAM__cond ::
 Nor T_PollRetransmit__Type T_PollRetransmit__cond ::
 Nor PollPDU__Type PollPDU__cond ::
 Nor PollByte__Type PollByte__cond ::
 Nor UL_AM_RLC__maxRetxThreshold__Type UL_AM_RLC__maxRetxThreshold__cond ::
 nil).
Definition UL_AM_RLC__cond z := 
  opt_cond SN_FieldLengthAM__cond (UL_AM_RLC__sn_FieldLength z) /\
  T_PollRetransmit__cond (UL_AM_RLC__t_PollRetransmit z) /\
  PollPDU__cond (UL_AM_RLC__pollPDU z) /\
  PollByte__cond (UL_AM_RLC__pollByte z) /\
  UL_AM_RLC__maxRetxThreshold__cond (UL_AM_RLC__maxRetxThreshold z) /\
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
Definition UL_AM_RLC__maxRetxThreshold__Format : T_Format UL_AM_RLC__maxRetxThreshold__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UL_AM_RLC__maxRetxThreshold__nat__Format UL_AM_RLC__maxRetxThreshold__F1 UL_AM_RLC__maxRetxThreshold__F2 UL_AM_RLC__maxRetxThreshold__F1F2 UL_AM_RLC__maxRetxThreshold__F2F1.

Opaque UL_AM_RLC__maxRetxThreshold__cond UL_AM_RLC__maxRetxThreshold__Format.


Definition UL_AM_RLC__Format_Type := Eval cbn in seq_format_prod UL_AM_RLC__list.
Definition UL_AM_RLC__Format_list : UL_AM_RLC__Format_Type :=
  (SN_FieldLengthAM__Format, (T_PollRetransmit__Format, (PollPDU__Format, (PollByte__Format, (UL_AM_RLC__maxRetxThreshold__Format, unit_format))))).
Definition UL_AM_RLC__list__Format := (*Eval compute in *) seq_format UL_AM_RLC__list UL_AM_RLC__Format_list.
Definition UL_AM_RLC__F1 z :=
  (UL_AM_RLC__sn_FieldLength z, (UL_AM_RLC__t_PollRetransmit z, (UL_AM_RLC__pollPDU z, (UL_AM_RLC__pollByte z, (UL_AM_RLC__maxRetxThreshold z, tt))))).
Definition UL_AM_RLC__F2 (y : seq_type UL_AM_RLC__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__UL_AM_RLC__Type i0 i1 i2 i3 i4
  end.
Lemma UL_AM_RLC__F1F2_cond (z : UL_AM_RLC__Type)
  : UL_AM_RLC__cond z ->
  (seq_cond UL_AM_RLC__list (UL_AM_RLC__F1 z)).
intro H. unfold UL_AM_RLC__cond in H. simpl. auto. Qed.
Lemma UL_AM_RLC__F1F2_cond2 (z : UL_AM_RLC__Type)
 : UL_AM_RLC__F2 (UL_AM_RLC__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UL_AM_RLC__F2F1_cond (y : seq_type UL_AM_RLC__list)
  : seq_cond UL_AM_RLC__list y ->
 (UL_AM_RLC__cond (UL_AM_RLC__F2 y)) /\  UL_AM_RLC__F1 (UL_AM_RLC__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UL_AM_RLC__cond. simpl in *. auto.
 - simpl. unfold UL_AM_RLC__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UL_AM_RLC__Format : T_Format UL_AM_RLC__Type UL_AM_RLC__cond :=
        proj2_format  UL_AM_RLC__cond UL_AM_RLC__list__Format
    UL_AM_RLC__F1 UL_AM_RLC__F2 UL_AM_RLC__F1F2_cond  UL_AM_RLC__F1F2_cond2 UL_AM_RLC__F2F1_cond.
Opaque UL_AM_RLC__cond UL_AM_RLC__Format.

