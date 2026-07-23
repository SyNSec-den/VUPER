Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.

Inductive SL_MeasReportQuantity_r16__root__Type : Set := | SL_MeasReportQuantity_r16__root__sl_RSRP_r16 : bool -> SL_MeasReportQuantity_r16__root__Type.
Definition SL_MeasReportQuantity_r16__root__cond (c : SL_MeasReportQuantity_r16__root__Type) := 
  match c with
  | SL_MeasReportQuantity_r16__root__sl_RSRP_r16 t => (fun _ => True) t 
  end.


Definition SL_MeasReportQuantity_r16__ext__Type : Set := Empty_set.
Definition SL_MeasReportQuantity_r16__ext__cond (c : SL_MeasReportQuantity_r16__ext__Type) := True.
Definition SL_MeasReportQuantity_r16__Type : Set := SL_MeasReportQuantity_r16__root__Type + SL_MeasReportQuantity_r16__ext__Type.
Definition SL_MeasReportQuantity_r16__cond :=
  sum_cond SL_MeasReportQuantity_r16__root__cond SL_MeasReportQuantity_r16__ext__cond.

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
Definition SL_MeasReportQuantity_r16__root__F1 (z : SL_MeasReportQuantity_r16__root__Type) : bool := 
  match z with
  | SL_MeasReportQuantity_r16__root__sl_RSRP_r16 t => t
  end.
Definition SL_MeasReportQuantity_r16__root__F2 (y : bool) : SL_MeasReportQuantity_r16__root__Type := SL_MeasReportQuantity_r16__root__sl_RSRP_r16 y.

Definition SL_MeasReportQuantity_r16__root__helper2 : (forall z : SL_MeasReportQuantity_r16__root__Type, SL_MeasReportQuantity_r16__root__cond z -> (fun _ => True) (SL_MeasReportQuantity_r16__root__F1 z)).
Proof. intros. destruct z; auto. Qed.
Definition SL_MeasReportQuantity_r16__root__helper3 : (forall z : SL_MeasReportQuantity_r16__root__Type, SL_MeasReportQuantity_r16__root__F2 (SL_MeasReportQuantity_r16__root__F1 z) = z).
Proof. intros. destruct z; auto. Qed.
Definition SL_MeasReportQuantity_r16__root__helper4 : (forall y : bool, (fun _ => True) y -> SL_MeasReportQuantity_r16__root__cond (SL_MeasReportQuantity_r16__root__F2 y) /\  SL_MeasReportQuantity_r16__root__F1 (SL_MeasReportQuantity_r16__root__F2 y) = y).
Proof. intros. destruct y; auto. Qed.
Definition SL_MeasReportQuantity_r16__root__Format : T_Format SL_MeasReportQuantity_r16__root__Type SL_MeasReportQuantity_r16__root__cond :=
  proj2_format SL_MeasReportQuantity_r16__root__cond bool__Format SL_MeasReportQuantity_r16__root__F1 SL_MeasReportQuantity_r16__root__F2 SL_MeasReportQuantity_r16__root__helper2 SL_MeasReportQuantity_r16__root__helper3 SL_MeasReportQuantity_r16__root__helper4.
Opaque SL_MeasReportQuantity_r16__root__cond SL_MeasReportQuantity_r16__root__Format.

Definition SL_MeasReportQuantity_r16__ext__Format : T_Format SL_MeasReportQuantity_r16__ext__Type SL_MeasReportQuantity_r16__ext__cond := empty_format.
Opaque SL_MeasReportQuantity_r16__ext__cond SL_MeasReportQuantity_r16__ext__Format.

Definition SL_MeasReportQuantity_r16__Format : T_Format SL_MeasReportQuantity_r16__Type SL_MeasReportQuantity_r16__cond := sum_format SL_MeasReportQuantity_r16__root__Format SL_MeasReportQuantity_r16__ext__Format.
Opaque SL_MeasReportQuantity_r16__cond SL_MeasReportQuantity_r16__Format.

