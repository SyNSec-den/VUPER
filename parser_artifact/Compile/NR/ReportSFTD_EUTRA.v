Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Record ReportSFTD_EUTRA__Type : Set :=
  make__ReportSFTD_EUTRA__Type {
    ReportSFTD_EUTRA__reportSFTD_Meas : bool ;
    ReportSFTD_EUTRA__reportRSRP : bool ;
}.
Definition ReportSFTD_EUTRA__root_list : list seq_elem := (
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 nil).
Definition ReportSFTD_EUTRA__ext_list : list typ := (
  nil).
Definition ReportSFTD_EUTRA__cond (z : ReportSFTD_EUTRA__Type) := 
(  (fun _ => True) (ReportSFTD_EUTRA__reportSFTD_Meas z) /\
  (fun _ => True) (ReportSFTD_EUTRA__reportRSRP z) /\
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

Definition ReportSFTD_EUTRA__root_Format_Type := Eval cbn in seq_format_prod ReportSFTD_EUTRA__root_list.
Definition ReportSFTD_EUTRA__root_Format_list : ReportSFTD_EUTRA__root_Format_Type :=
  (bool__Format, (bool__Format, unit_format)).

Definition ReportSFTD_EUTRA__ext_Format_Type := Eval cbn in get_formats ReportSFTD_EUTRA__ext_list.
Definition ReportSFTD_EUTRA__ext_Format_list : ReportSFTD_EUTRA__ext_Format_Type :=
  unit__Format.

Definition ReportSFTD_EUTRA__list_type : Set := (seq_type ReportSFTD_EUTRA__root_list) * (seq_ext_type ReportSFTD_EUTRA__ext_list).
Definition ReportSFTD_EUTRA__list_cond (z : ReportSFTD_EUTRA__list_type) : Prop :=
        (seq_cond ReportSFTD_EUTRA__root_list (fst z)) /\ (seq_ext_cond ReportSFTD_EUTRA__ext_list (snd z)).
Definition ReportSFTD_EUTRA__list_format : T_Format ReportSFTD_EUTRA__list_type ReportSFTD_EUTRA__list_cond :=
 (* Eval compute in *) seq_ext_format ReportSFTD_EUTRA__root_list ReportSFTD_EUTRA__root_Format_list ReportSFTD_EUTRA__ext_list ReportSFTD_EUTRA__ext_Format_list.

Opaque ReportSFTD_EUTRA__list_format.
Definition ReportSFTD_EUTRA__F1 (z : ReportSFTD_EUTRA__Type) : ReportSFTD_EUTRA__list_type :=
  (((ReportSFTD_EUTRA__reportSFTD_Meas z, (ReportSFTD_EUTRA__reportRSRP z, tt))), (
tt)).
Definition ReportSFTD_EUTRA__F2 (y : ReportSFTD_EUTRA__list_type) : ReportSFTD_EUTRA__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__ReportSFTD_EUTRA__Type j0 j1
  end.
Definition ReportSFTD_EUTRA__helper1 : (forall a : ReportSFTD_EUTRA__Type, ReportSFTD_EUTRA__cond a -> ReportSFTD_EUTRA__list_cond (ReportSFTD_EUTRA__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ReportSFTD_EUTRA__helper2 : (forall a : ReportSFTD_EUTRA__Type, ReportSFTD_EUTRA__F2 (ReportSFTD_EUTRA__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ReportSFTD_EUTRA__helper3 : (forall b : ReportSFTD_EUTRA__list_type, ReportSFTD_EUTRA__list_cond b -> ReportSFTD_EUTRA__cond (ReportSFTD_EUTRA__F2 b) /\ ReportSFTD_EUTRA__F1 (ReportSFTD_EUTRA__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ReportSFTD_EUTRA__cond, ReportSFTD_EUTRA__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ReportSFTD_EUTRA__Format : T_Format ReportSFTD_EUTRA__Type ReportSFTD_EUTRA__cond :=
 proj2_format ReportSFTD_EUTRA__cond ReportSFTD_EUTRA__list_format  ReportSFTD_EUTRA__F1 ReportSFTD_EUTRA__F2 ReportSFTD_EUTRA__helper1 ReportSFTD_EUTRA__helper2 ReportSFTD_EUTRA__helper3.

Opaque ReportSFTD_EUTRA__cond ReportSFTD_EUTRA__Format.

