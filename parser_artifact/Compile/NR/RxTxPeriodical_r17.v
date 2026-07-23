Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.RxTxReportInterval_r17.

Opaque RxTxReportInterval_r17__cond RxTxReportInterval_r17__Format.

Inductive RxTxPeriodical_r17__reportAmount_r17__Type : Set :=
 | RxTxPeriodical_r17__reportAmount_r17__r1
 | RxTxPeriodical_r17__reportAmount_r17__infinity
 | RxTxPeriodical_r17__reportAmount_r17__spare6
 | RxTxPeriodical_r17__reportAmount_r17__spare5
 | RxTxPeriodical_r17__reportAmount_r17__spare4
 | RxTxPeriodical_r17__reportAmount_r17__spare3
 | RxTxPeriodical_r17__reportAmount_r17__spare2
 | RxTxPeriodical_r17__reportAmount_r17__spare1
.
Definition RxTxPeriodical_r17__reportAmount_r17__cond := (fun (_ : RxTxPeriodical_r17__reportAmount_r17__Type) => True).
Lemma RxTxPeriodical_r17__reportAmount_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RxTxPeriodical_r17__reportAmount_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 RxTxPeriodical_r17__reportAmount_r17__nat__helper.

Definition RxTxPeriodical_r17__reportAmount_r17__F1 t :=
  match t with
  | RxTxPeriodical_r17__reportAmount_r17__r1 => 0
  | RxTxPeriodical_r17__reportAmount_r17__infinity => 1
  | RxTxPeriodical_r17__reportAmount_r17__spare6 => 2
  | RxTxPeriodical_r17__reportAmount_r17__spare5 => 3
  | RxTxPeriodical_r17__reportAmount_r17__spare4 => 4
  | RxTxPeriodical_r17__reportAmount_r17__spare3 => 5
  | RxTxPeriodical_r17__reportAmount_r17__spare2 => 6
  | RxTxPeriodical_r17__reportAmount_r17__spare1 => 7
  end.
Definition RxTxPeriodical_r17__reportAmount_r17__F2 n :=
  match n with
  | 0 => RxTxPeriodical_r17__reportAmount_r17__r1
  | 1 => RxTxPeriodical_r17__reportAmount_r17__infinity
  | 2 => RxTxPeriodical_r17__reportAmount_r17__spare6
  | 3 => RxTxPeriodical_r17__reportAmount_r17__spare5
  | 4 => RxTxPeriodical_r17__reportAmount_r17__spare4
  | 5 => RxTxPeriodical_r17__reportAmount_r17__spare3
  | 6 => RxTxPeriodical_r17__reportAmount_r17__spare2
  | 7 => RxTxPeriodical_r17__reportAmount_r17__spare1
  | _ => RxTxPeriodical_r17__reportAmount_r17__r1
  end.
Lemma RxTxPeriodical_r17__reportAmount_r17__F1F2 : forall x : RxTxPeriodical_r17__reportAmount_r17__Type, (RxTxPeriodical_r17__reportAmount_r17__F1 x <= 7) /\ RxTxPeriodical_r17__reportAmount_r17__F2 (RxTxPeriodical_r17__reportAmount_r17__F1 x) = x. imp_solve. Qed.
Lemma RxTxPeriodical_r17__reportAmount_r17__F2F1 : forall (y : nat) (H : y <= 7), RxTxPeriodical_r17__reportAmount_r17__F1 (RxTxPeriodical_r17__reportAmount_r17__F2 y) = y. enum_solve H y. Qed.

Record RxTxPeriodical_r17__Type : Set :=
  make__RxTxPeriodical_r17__Type {
    RxTxPeriodical_r17__rxTxReportInterval_r17 : option RxTxReportInterval_r17__Type ;
    RxTxPeriodical_r17__reportAmount_r17 : RxTxPeriodical_r17__reportAmount_r17__Type ;
}.
Definition RxTxPeriodical_r17__root_list : list seq_elem := (
 Opt RxTxReportInterval_r17__Type RxTxReportInterval_r17__cond ::
 Nor RxTxPeriodical_r17__reportAmount_r17__Type RxTxPeriodical_r17__reportAmount_r17__cond ::
 nil).
Definition RxTxPeriodical_r17__ext_list : list typ := (
  nil).
Definition RxTxPeriodical_r17__cond (z : RxTxPeriodical_r17__Type) := 
(  opt_cond RxTxReportInterval_r17__cond (RxTxPeriodical_r17__rxTxReportInterval_r17 z) /\
  RxTxPeriodical_r17__reportAmount_r17__cond (RxTxPeriodical_r17__reportAmount_r17 z) /\
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
Definition RxTxPeriodical_r17__reportAmount_r17__Format : T_Format RxTxPeriodical_r17__reportAmount_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RxTxPeriodical_r17__reportAmount_r17__nat__Format RxTxPeriodical_r17__reportAmount_r17__F1 RxTxPeriodical_r17__reportAmount_r17__F2 RxTxPeriodical_r17__reportAmount_r17__F1F2 RxTxPeriodical_r17__reportAmount_r17__F2F1.

Opaque RxTxPeriodical_r17__reportAmount_r17__cond RxTxPeriodical_r17__reportAmount_r17__Format.


Definition RxTxPeriodical_r17__root_Format_Type := Eval cbn in seq_format_prod RxTxPeriodical_r17__root_list.
Definition RxTxPeriodical_r17__root_Format_list : RxTxPeriodical_r17__root_Format_Type :=
  (RxTxReportInterval_r17__Format, (RxTxPeriodical_r17__reportAmount_r17__Format, unit_format)).

Definition RxTxPeriodical_r17__ext_Format_Type := Eval cbn in get_formats RxTxPeriodical_r17__ext_list.
Definition RxTxPeriodical_r17__ext_Format_list : RxTxPeriodical_r17__ext_Format_Type :=
  unit__Format.

Definition RxTxPeriodical_r17__list_type : Set := (seq_type RxTxPeriodical_r17__root_list) * (seq_ext_type RxTxPeriodical_r17__ext_list).
Definition RxTxPeriodical_r17__list_cond (z : RxTxPeriodical_r17__list_type) : Prop :=
        (seq_cond RxTxPeriodical_r17__root_list (fst z)) /\ (seq_ext_cond RxTxPeriodical_r17__ext_list (snd z)).
Definition RxTxPeriodical_r17__list_format : T_Format RxTxPeriodical_r17__list_type RxTxPeriodical_r17__list_cond :=
 (* Eval compute in *) seq_ext_format RxTxPeriodical_r17__root_list RxTxPeriodical_r17__root_Format_list RxTxPeriodical_r17__ext_list RxTxPeriodical_r17__ext_Format_list.

Opaque RxTxPeriodical_r17__list_format.
Definition RxTxPeriodical_r17__F1 (z : RxTxPeriodical_r17__Type) : RxTxPeriodical_r17__list_type :=
  (((RxTxPeriodical_r17__rxTxReportInterval_r17 z, (RxTxPeriodical_r17__reportAmount_r17 z, tt))), (
tt)).
Definition RxTxPeriodical_r17__F2 (y : RxTxPeriodical_r17__list_type) : RxTxPeriodical_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__RxTxPeriodical_r17__Type j0 j1
  end.
Definition RxTxPeriodical_r17__helper1 : (forall a : RxTxPeriodical_r17__Type, RxTxPeriodical_r17__cond a -> RxTxPeriodical_r17__list_cond (RxTxPeriodical_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RxTxPeriodical_r17__helper2 : (forall a : RxTxPeriodical_r17__Type, RxTxPeriodical_r17__F2 (RxTxPeriodical_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RxTxPeriodical_r17__helper3 : (forall b : RxTxPeriodical_r17__list_type, RxTxPeriodical_r17__list_cond b -> RxTxPeriodical_r17__cond (RxTxPeriodical_r17__F2 b) /\ RxTxPeriodical_r17__F1 (RxTxPeriodical_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RxTxPeriodical_r17__cond, RxTxPeriodical_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RxTxPeriodical_r17__Format : T_Format RxTxPeriodical_r17__Type RxTxPeriodical_r17__cond :=
 proj2_format RxTxPeriodical_r17__cond RxTxPeriodical_r17__list_format  RxTxPeriodical_r17__F1 RxTxPeriodical_r17__F2 RxTxPeriodical_r17__helper1 RxTxPeriodical_r17__helper2 RxTxPeriodical_r17__helper3.

Opaque RxTxPeriodical_r17__cond RxTxPeriodical_r17__Format.

