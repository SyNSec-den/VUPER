Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Type : Set :=
 | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf0
 | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf10
 | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf20
 | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf50
 | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf100
 | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf200
 | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf500
 | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf1000
.
Definition MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__cond := (fun (_ : MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Type) => True).
Lemma MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__nat__helper.

Definition MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F1 t :=
  match t with
  | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf0 => 0
  | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf10 => 1
  | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf20 => 2
  | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf50 => 3
  | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf100 => 4
  | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf200 => 5
  | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf500 => 6
  | MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf1000 => 7
  end.
Definition MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F2 n :=
  match n with
  | 0 => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf0
  | 1 => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf10
  | 2 => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf20
  | 3 => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf50
  | 4 => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf100
  | 5 => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf200
  | 6 => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf500
  | 7 => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf1000
  | _ => MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__sf0
  end.
Lemma MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F1F2 : forall x : MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Type, (MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F1 x <= 7) /\ MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F2 (MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F1 x) = x. imp_solve. Qed.
Lemma MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F2F1 : forall (y : nat) (H : y <= 7), MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F1 (MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F2 y) = y. enum_solve H y. Qed.

Inductive MPE_Config_FR2_r16__mpe_Threshold_r16__Type : Set :=
 | MPE_Config_FR2_r16__mpe_Threshold_r16__dB3
 | MPE_Config_FR2_r16__mpe_Threshold_r16__dB6
 | MPE_Config_FR2_r16__mpe_Threshold_r16__dB9
 | MPE_Config_FR2_r16__mpe_Threshold_r16__dB12
.
Definition MPE_Config_FR2_r16__mpe_Threshold_r16__cond := (fun (_ : MPE_Config_FR2_r16__mpe_Threshold_r16__Type) => True).
Lemma MPE_Config_FR2_r16__mpe_Threshold_r16__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MPE_Config_FR2_r16__mpe_Threshold_r16__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 MPE_Config_FR2_r16__mpe_Threshold_r16__nat__helper.

Definition MPE_Config_FR2_r16__mpe_Threshold_r16__F1 t :=
  match t with
  | MPE_Config_FR2_r16__mpe_Threshold_r16__dB3 => 0
  | MPE_Config_FR2_r16__mpe_Threshold_r16__dB6 => 1
  | MPE_Config_FR2_r16__mpe_Threshold_r16__dB9 => 2
  | MPE_Config_FR2_r16__mpe_Threshold_r16__dB12 => 3
  end.
Definition MPE_Config_FR2_r16__mpe_Threshold_r16__F2 n :=
  match n with
  | 0 => MPE_Config_FR2_r16__mpe_Threshold_r16__dB3
  | 1 => MPE_Config_FR2_r16__mpe_Threshold_r16__dB6
  | 2 => MPE_Config_FR2_r16__mpe_Threshold_r16__dB9
  | 3 => MPE_Config_FR2_r16__mpe_Threshold_r16__dB12
  | _ => MPE_Config_FR2_r16__mpe_Threshold_r16__dB3
  end.
Lemma MPE_Config_FR2_r16__mpe_Threshold_r16__F1F2 : forall x : MPE_Config_FR2_r16__mpe_Threshold_r16__Type, (MPE_Config_FR2_r16__mpe_Threshold_r16__F1 x <= 3) /\ MPE_Config_FR2_r16__mpe_Threshold_r16__F2 (MPE_Config_FR2_r16__mpe_Threshold_r16__F1 x) = x. imp_solve. Qed.
Lemma MPE_Config_FR2_r16__mpe_Threshold_r16__F2F1 : forall (y : nat) (H : y <= 3), MPE_Config_FR2_r16__mpe_Threshold_r16__F1 (MPE_Config_FR2_r16__mpe_Threshold_r16__F2 y) = y. enum_solve H y. Qed.

Record MPE_Config_FR2_r16__Type : Set :=
  make__MPE_Config_FR2_r16__Type {
    MPE_Config_FR2_r16__mpe_ProhibitTimer_r16 : MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Type ;
    MPE_Config_FR2_r16__mpe_Threshold_r16 : MPE_Config_FR2_r16__mpe_Threshold_r16__Type ;
}.
Definition MPE_Config_FR2_r16__list := (
 Nor MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Type MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__cond ::
 Nor MPE_Config_FR2_r16__mpe_Threshold_r16__Type MPE_Config_FR2_r16__mpe_Threshold_r16__cond ::
 nil).
Definition MPE_Config_FR2_r16__cond z := 
  MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__cond (MPE_Config_FR2_r16__mpe_ProhibitTimer_r16 z) /\
  MPE_Config_FR2_r16__mpe_Threshold_r16__cond (MPE_Config_FR2_r16__mpe_Threshold_r16 z) /\
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
Definition MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Format : T_Format MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__nat__Format MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F1 MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F2 MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F1F2 MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__F2F1.

Opaque MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__cond MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Format.

Definition MPE_Config_FR2_r16__mpe_Threshold_r16__Format : T_Format MPE_Config_FR2_r16__mpe_Threshold_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MPE_Config_FR2_r16__mpe_Threshold_r16__nat__Format MPE_Config_FR2_r16__mpe_Threshold_r16__F1 MPE_Config_FR2_r16__mpe_Threshold_r16__F2 MPE_Config_FR2_r16__mpe_Threshold_r16__F1F2 MPE_Config_FR2_r16__mpe_Threshold_r16__F2F1.

Opaque MPE_Config_FR2_r16__mpe_Threshold_r16__cond MPE_Config_FR2_r16__mpe_Threshold_r16__Format.


Definition MPE_Config_FR2_r16__Format_Type := Eval cbn in seq_format_prod MPE_Config_FR2_r16__list.
Definition MPE_Config_FR2_r16__Format_list : MPE_Config_FR2_r16__Format_Type :=
  (MPE_Config_FR2_r16__mpe_ProhibitTimer_r16__Format, (MPE_Config_FR2_r16__mpe_Threshold_r16__Format, unit_format)).
Definition MPE_Config_FR2_r16__list__Format := (*Eval compute in *) seq_format MPE_Config_FR2_r16__list MPE_Config_FR2_r16__Format_list.
Definition MPE_Config_FR2_r16__F1 z :=
  (MPE_Config_FR2_r16__mpe_ProhibitTimer_r16 z, (MPE_Config_FR2_r16__mpe_Threshold_r16 z, tt)).
Definition MPE_Config_FR2_r16__F2 (y : seq_type MPE_Config_FR2_r16__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MPE_Config_FR2_r16__Type i0 i1
  end.
Lemma MPE_Config_FR2_r16__F1F2_cond (z : MPE_Config_FR2_r16__Type)
  : MPE_Config_FR2_r16__cond z ->
  (seq_cond MPE_Config_FR2_r16__list (MPE_Config_FR2_r16__F1 z)).
intro H. unfold MPE_Config_FR2_r16__cond in H. simpl. auto. Qed.
Lemma MPE_Config_FR2_r16__F1F2_cond2 (z : MPE_Config_FR2_r16__Type)
 : MPE_Config_FR2_r16__F2 (MPE_Config_FR2_r16__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MPE_Config_FR2_r16__F2F1_cond (y : seq_type MPE_Config_FR2_r16__list)
  : seq_cond MPE_Config_FR2_r16__list y ->
 (MPE_Config_FR2_r16__cond (MPE_Config_FR2_r16__F2 y)) /\  MPE_Config_FR2_r16__F1 (MPE_Config_FR2_r16__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MPE_Config_FR2_r16__cond. simpl in *. auto.
 - simpl. unfold MPE_Config_FR2_r16__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MPE_Config_FR2_r16__Format : T_Format MPE_Config_FR2_r16__Type MPE_Config_FR2_r16__cond :=
        proj2_format  MPE_Config_FR2_r16__cond MPE_Config_FR2_r16__list__Format
    MPE_Config_FR2_r16__F1 MPE_Config_FR2_r16__F2 MPE_Config_FR2_r16__F1F2_cond  MPE_Config_FR2_r16__F1F2_cond2 MPE_Config_FR2_r16__F2F1_cond.
Opaque MPE_Config_FR2_r16__cond MPE_Config_FR2_r16__Format.

