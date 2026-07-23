Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.ReportInterval.

Opaque ReportInterval__cond ReportInterval__Format.

Inductive SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Type : Set :=
 | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r1
 | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r2
 | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r4
 | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r8
 | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r16
 | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r32
 | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r64
 | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__infinity
.
Definition SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__cond := (fun (_ : SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Type) => True).
Lemma SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__nat__helper.

Definition SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F1 t :=
  match t with
  | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r1 => 0
  | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r2 => 1
  | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r4 => 2
  | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r8 => 3
  | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r16 => 4
  | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r32 => 5
  | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r64 => 6
  | SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__infinity => 7
  end.
Definition SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F2 n :=
  match n with
  | 0 => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r1
  | 1 => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r2
  | 2 => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r4
  | 3 => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r8
  | 4 => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r16
  | 5 => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r32
  | 6 => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r64
  | 7 => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__infinity
  | _ => SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__r1
  end.
Lemma SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F1F2 : forall x : SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Type, (SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F1 x <= 7) /\ SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F2 (SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F1 x) = x. imp_solve. Qed.
Lemma SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F2F1 : forall (y : nat) (H : y <= 7), SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F1 (SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SL_MeasReportQuantity_r16.

Opaque SL_MeasReportQuantity_r16__cond SL_MeasReportQuantity_r16__Format.

Require Import NR.SL_RS_Type_r16.

Opaque SL_RS_Type_r16__cond SL_RS_Type_r16__Format.

Record SL_PeriodicalReportConfig_r16__Type : Set :=
  make__SL_PeriodicalReportConfig_r16__Type {
    SL_PeriodicalReportConfig_r16__sl_ReportInterval_r16 : ReportInterval__Type ;
    SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16 : SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Type ;
    SL_PeriodicalReportConfig_r16__sl_ReportQuantity_r16 : SL_MeasReportQuantity_r16__Type ;
    SL_PeriodicalReportConfig_r16__sl_RS_Type_r16 : SL_RS_Type_r16__Type ;
}.
Definition SL_PeriodicalReportConfig_r16__root_list : list seq_elem := (
 Nor ReportInterval__Type ReportInterval__cond ::
 Nor SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Type SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__cond ::
 Nor SL_MeasReportQuantity_r16__Type SL_MeasReportQuantity_r16__cond ::
 Nor SL_RS_Type_r16__Type SL_RS_Type_r16__cond ::
 nil).
Definition SL_PeriodicalReportConfig_r16__ext_list : list typ := (
  nil).
Definition SL_PeriodicalReportConfig_r16__cond (z : SL_PeriodicalReportConfig_r16__Type) := 
(  ReportInterval__cond (SL_PeriodicalReportConfig_r16__sl_ReportInterval_r16 z) /\
  SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__cond (SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16 z) /\
  SL_MeasReportQuantity_r16__cond (SL_PeriodicalReportConfig_r16__sl_ReportQuantity_r16 z) /\
  SL_RS_Type_r16__cond (SL_PeriodicalReportConfig_r16__sl_RS_Type_r16 z) /\
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
Definition SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Format : T_Format SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__nat__Format SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F1 SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F2 SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F1F2 SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__F2F1.

Opaque SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__cond SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Format.


Definition SL_PeriodicalReportConfig_r16__root_Format_Type := Eval cbn in seq_format_prod SL_PeriodicalReportConfig_r16__root_list.
Definition SL_PeriodicalReportConfig_r16__root_Format_list : SL_PeriodicalReportConfig_r16__root_Format_Type :=
  (ReportInterval__Format, (SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16__Format, (SL_MeasReportQuantity_r16__Format, (SL_RS_Type_r16__Format, unit_format)))).

Definition SL_PeriodicalReportConfig_r16__ext_Format_Type := Eval cbn in get_formats SL_PeriodicalReportConfig_r16__ext_list.
Definition SL_PeriodicalReportConfig_r16__ext_Format_list : SL_PeriodicalReportConfig_r16__ext_Format_Type :=
  unit__Format.

Definition SL_PeriodicalReportConfig_r16__list_type : Set := (seq_type SL_PeriodicalReportConfig_r16__root_list) * (seq_ext_type SL_PeriodicalReportConfig_r16__ext_list).
Definition SL_PeriodicalReportConfig_r16__list_cond (z : SL_PeriodicalReportConfig_r16__list_type) : Prop :=
        (seq_cond SL_PeriodicalReportConfig_r16__root_list (fst z)) /\ (seq_ext_cond SL_PeriodicalReportConfig_r16__ext_list (snd z)).
Definition SL_PeriodicalReportConfig_r16__list_format : T_Format SL_PeriodicalReportConfig_r16__list_type SL_PeriodicalReportConfig_r16__list_cond :=
 (* Eval compute in *) seq_ext_format SL_PeriodicalReportConfig_r16__root_list SL_PeriodicalReportConfig_r16__root_Format_list SL_PeriodicalReportConfig_r16__ext_list SL_PeriodicalReportConfig_r16__ext_Format_list.

Opaque SL_PeriodicalReportConfig_r16__list_format.
Definition SL_PeriodicalReportConfig_r16__F1 (z : SL_PeriodicalReportConfig_r16__Type) : SL_PeriodicalReportConfig_r16__list_type :=
  (((SL_PeriodicalReportConfig_r16__sl_ReportInterval_r16 z, (SL_PeriodicalReportConfig_r16__sl_ReportAmount_r16 z, (SL_PeriodicalReportConfig_r16__sl_ReportQuantity_r16 z, (SL_PeriodicalReportConfig_r16__sl_RS_Type_r16 z, tt))))), (
tt)).
Definition SL_PeriodicalReportConfig_r16__F2 (y : SL_PeriodicalReportConfig_r16__list_type) : SL_PeriodicalReportConfig_r16__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__SL_PeriodicalReportConfig_r16__Type j0 j1 j2 j3
  end.
Definition SL_PeriodicalReportConfig_r16__helper1 : (forall a : SL_PeriodicalReportConfig_r16__Type, SL_PeriodicalReportConfig_r16__cond a -> SL_PeriodicalReportConfig_r16__list_cond (SL_PeriodicalReportConfig_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SL_PeriodicalReportConfig_r16__helper2 : (forall a : SL_PeriodicalReportConfig_r16__Type, SL_PeriodicalReportConfig_r16__F2 (SL_PeriodicalReportConfig_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SL_PeriodicalReportConfig_r16__helper3 : (forall b : SL_PeriodicalReportConfig_r16__list_type, SL_PeriodicalReportConfig_r16__list_cond b -> SL_PeriodicalReportConfig_r16__cond (SL_PeriodicalReportConfig_r16__F2 b) /\ SL_PeriodicalReportConfig_r16__F1 (SL_PeriodicalReportConfig_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SL_PeriodicalReportConfig_r16__cond, SL_PeriodicalReportConfig_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SL_PeriodicalReportConfig_r16__Format : T_Format SL_PeriodicalReportConfig_r16__Type SL_PeriodicalReportConfig_r16__cond :=
 proj2_format SL_PeriodicalReportConfig_r16__cond SL_PeriodicalReportConfig_r16__list_format  SL_PeriodicalReportConfig_r16__F1 SL_PeriodicalReportConfig_r16__F2 SL_PeriodicalReportConfig_r16__helper1 SL_PeriodicalReportConfig_r16__helper2 SL_PeriodicalReportConfig_r16__helper3.

Opaque SL_PeriodicalReportConfig_r16__cond SL_PeriodicalReportConfig_r16__Format.

