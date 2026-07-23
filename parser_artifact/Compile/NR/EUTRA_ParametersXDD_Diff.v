Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Type : Set :=
 | EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__supported
.
Definition EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__cond := (fun (_ : EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Type) => True).
Lemma EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__nat__helper.

Definition EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F1 t :=
  match t with
  | EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__supported => 0
  end.
Definition EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F2 n :=
  match n with
  | 0 => EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__supported
  | _ => EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__supported
  end.
Lemma EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F1F2 : forall x : EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Type, (EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F1 x <= 0) /\ EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F2 (EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F1 x) = x. imp_solve. Qed.
Lemma EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F2F1 : forall (y : nat) (H : y <= 0), EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F1 (EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F2 y) = y. enum_solve H y. Qed.

Record EUTRA_ParametersXDD_Diff__Type : Set :=
  make__EUTRA_ParametersXDD_Diff__Type {
    EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA : option EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Type ;
}.
Definition EUTRA_ParametersXDD_Diff__root_list : list seq_elem := (
 Opt EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Type EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__cond ::
 nil).
Definition EUTRA_ParametersXDD_Diff__ext_list : list typ := (
  nil).
Definition EUTRA_ParametersXDD_Diff__cond (z : EUTRA_ParametersXDD_Diff__Type) := 
(  opt_cond EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__cond (EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA z) /\
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
Definition EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Format : T_Format EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Type (fun _ => True) :=
(* Eval compute in *) proj3_format EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__nat__Format EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F1 EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F2 EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F1F2 EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__F2F1.

Opaque EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__cond EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Format.


Definition EUTRA_ParametersXDD_Diff__root_Format_Type := Eval cbn in seq_format_prod EUTRA_ParametersXDD_Diff__root_list.
Definition EUTRA_ParametersXDD_Diff__root_Format_list : EUTRA_ParametersXDD_Diff__root_Format_Type :=
  (EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA__Format, unit_format).

Definition EUTRA_ParametersXDD_Diff__ext_Format_Type := Eval cbn in get_formats EUTRA_ParametersXDD_Diff__ext_list.
Definition EUTRA_ParametersXDD_Diff__ext_Format_list : EUTRA_ParametersXDD_Diff__ext_Format_Type :=
  unit__Format.

Definition EUTRA_ParametersXDD_Diff__list_type : Set := (seq_type EUTRA_ParametersXDD_Diff__root_list) * (seq_ext_type EUTRA_ParametersXDD_Diff__ext_list).
Definition EUTRA_ParametersXDD_Diff__list_cond (z : EUTRA_ParametersXDD_Diff__list_type) : Prop :=
        (seq_cond EUTRA_ParametersXDD_Diff__root_list (fst z)) /\ (seq_ext_cond EUTRA_ParametersXDD_Diff__ext_list (snd z)).
Definition EUTRA_ParametersXDD_Diff__list_format : T_Format EUTRA_ParametersXDD_Diff__list_type EUTRA_ParametersXDD_Diff__list_cond :=
 (* Eval compute in *) seq_ext_format EUTRA_ParametersXDD_Diff__root_list EUTRA_ParametersXDD_Diff__root_Format_list EUTRA_ParametersXDD_Diff__ext_list EUTRA_ParametersXDD_Diff__ext_Format_list.

Opaque EUTRA_ParametersXDD_Diff__list_format.
Definition EUTRA_ParametersXDD_Diff__F1 (z : EUTRA_ParametersXDD_Diff__Type) : EUTRA_ParametersXDD_Diff__list_type :=
  (((EUTRA_ParametersXDD_Diff__rsrqMeasWidebandEUTRA z, tt)), (
tt)).
Definition EUTRA_ParametersXDD_Diff__F2 (y : EUTRA_ParametersXDD_Diff__list_type) : EUTRA_ParametersXDD_Diff__Type :=
  match y with
  | ((j0, _), _)=>
    make__EUTRA_ParametersXDD_Diff__Type j0
  end.
Definition EUTRA_ParametersXDD_Diff__helper1 : (forall a : EUTRA_ParametersXDD_Diff__Type, EUTRA_ParametersXDD_Diff__cond a -> EUTRA_ParametersXDD_Diff__list_cond (EUTRA_ParametersXDD_Diff__F1 a)).
                     intros. destruct a. auto. Qed.
Definition EUTRA_ParametersXDD_Diff__helper2 : (forall a : EUTRA_ParametersXDD_Diff__Type, EUTRA_ParametersXDD_Diff__F2 (EUTRA_ParametersXDD_Diff__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition EUTRA_ParametersXDD_Diff__helper3 : (forall b : EUTRA_ParametersXDD_Diff__list_type, EUTRA_ParametersXDD_Diff__list_cond b -> EUTRA_ParametersXDD_Diff__cond (EUTRA_ParametersXDD_Diff__F2 b) /\ EUTRA_ParametersXDD_Diff__F1 (EUTRA_ParametersXDD_Diff__F2 b) = b).
                     intros. destruct b as [y y1]. unfold EUTRA_ParametersXDD_Diff__cond, EUTRA_ParametersXDD_Diff__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition EUTRA_ParametersXDD_Diff__Format : T_Format EUTRA_ParametersXDD_Diff__Type EUTRA_ParametersXDD_Diff__cond :=
 proj2_format EUTRA_ParametersXDD_Diff__cond EUTRA_ParametersXDD_Diff__list_format  EUTRA_ParametersXDD_Diff__F1 EUTRA_ParametersXDD_Diff__F2 EUTRA_ParametersXDD_Diff__helper1 EUTRA_ParametersXDD_Diff__helper2 EUTRA_ParametersXDD_Diff__helper3.

Opaque EUTRA_ParametersXDD_Diff__cond EUTRA_ParametersXDD_Diff__Format.

