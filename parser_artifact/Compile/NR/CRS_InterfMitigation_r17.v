Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Type : Set :=
 | CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__supported
.
Definition CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__cond := (fun (_ : CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Type) => True).
Lemma CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__nat__helper.

Definition CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F1 t :=
  match t with
  | CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__supported => 0
  end.
Definition CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F2 n :=
  match n with
  | 0 => CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__supported
  | _ => CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__supported
  end.
Lemma CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F1F2 : forall x : CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Type, (CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F1 x <= 0) /\ CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F2 (CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F1 x) = x. imp_solve. Qed.
Lemma CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F2F1 : forall (y : nat) (H : y <= 0), CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F1 (CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Type : Set :=
 | CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__supported
.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__cond := (fun (_ : CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Type) => True).
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__nat__helper.

Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F1 t :=
  match t with
  | CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__supported => 0
  end.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F2 n :=
  match n with
  | 0 => CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__supported
  | _ => CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__supported
  end.
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F1F2 : forall x : CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Type, (CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F1 x <= 0) /\ CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F2 (CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F1 x) = x. imp_solve. Qed.
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F2F1 : forall (y : nat) (H : y <= 0), CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F1 (CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Type : Set :=
 | CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__supported
.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__cond := (fun (_ : CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Type) => True).
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__nat__helper.

Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F1 t :=
  match t with
  | CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__supported => 0
  end.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F2 n :=
  match n with
  | 0 => CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__supported
  | _ => CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__supported
  end.
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F1F2 : forall x : CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Type, (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F1 x <= 0) /\ CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F2 (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F1 x) = x. imp_solve. Qed.
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F2F1 : forall (y : nat) (H : y <= 0), CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F1 (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Type : Set :=
 | CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__supported
.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__cond := (fun (_ : CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Type) => True).
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__nat__helper.

Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F1 t :=
  match t with
  | CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__supported => 0
  end.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F2 n :=
  match n with
  | 0 => CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__supported
  | _ => CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__supported
  end.
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F1F2 : forall x : CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Type, (CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F1 x <= 0) /\ CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F2 (CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F1 x) = x. imp_solve. Qed.
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F2F1 : forall (y : nat) (H : y <= 0), CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F1 (CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F2 y) = y. enum_solve H y. Qed.

Inductive CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Type : Set :=
 | CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__supported
.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__cond := (fun (_ : CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Type) => True).
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__nat__helper.

Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F1 t :=
  match t with
  | CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__supported => 0
  end.
Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F2 n :=
  match n with
  | 0 => CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__supported
  | _ => CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__supported
  end.
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F1F2 : forall x : CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Type, (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F1 x <= 0) /\ CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F2 (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F1 x) = x. imp_solve. Qed.
Lemma CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F2F1 : forall (y : nat) (H : y <= 0), CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F1 (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F2 y) = y. enum_solve H y. Qed.

Record CRS_InterfMitigation_r17__Type : Set :=
  make__CRS_InterfMitigation_r17__Type {
    CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17 : option CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Type ;
    CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17 : option CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Type ;
    CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17 : option CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Type ;
    CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17 : option CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Type ;
    CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17 : option CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Type ;
}.
Definition CRS_InterfMitigation_r17__list := (
 Opt CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Type CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__cond ::
 Opt CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Type CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__cond ::
 Opt CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Type CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__cond ::
 Opt CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Type CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__cond ::
 Opt CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Type CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__cond ::
 nil).
Definition CRS_InterfMitigation_r17__cond z := 
  opt_cond CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__cond (CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17 z) /\
  opt_cond CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__cond (CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17 z) /\
  opt_cond CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__cond (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17 z) /\
  opt_cond CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__cond (CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17 z) /\
  opt_cond CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__cond (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17 z) /\
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
Definition CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Format : T_Format CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__nat__Format CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F1 CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F2 CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F1F2 CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__F2F1.

Opaque CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__cond CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Format.

Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Format : T_Format CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__nat__Format CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F1 CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F2 CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F1F2 CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__F2F1.

Opaque CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__cond CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Format.

Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Format : T_Format CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__nat__Format CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F1 CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F2 CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F1F2 CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__F2F1.

Opaque CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__cond CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Format.

Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Format : T_Format CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__nat__Format CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F1 CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F2 CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F1F2 CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__F2F1.

Opaque CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__cond CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Format.

Definition CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Format : T_Format CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__nat__Format CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F1 CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F2 CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F1F2 CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__F2F1.

Opaque CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__cond CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Format.


Definition CRS_InterfMitigation_r17__Format_Type := Eval cbn in seq_format_prod CRS_InterfMitigation_r17__list.
Definition CRS_InterfMitigation_r17__Format_list : CRS_InterfMitigation_r17__Format_Type :=
  (CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17__Format, (CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17__Format, (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17__Format, (CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17__Format, (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17__Format, unit_format))))).
Definition CRS_InterfMitigation_r17__list__Format := (*Eval compute in *) seq_format CRS_InterfMitigation_r17__list CRS_InterfMitigation_r17__Format_list.
Definition CRS_InterfMitigation_r17__F1 z :=
  (CRS_InterfMitigation_r17__crs_IM_DSS_15kHzSCS_r17 z, (CRS_InterfMitigation_r17__crs_IM_nonDSS_15kHzSCS_r17 z, (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_15kHzSCS_r17 z, (CRS_InterfMitigation_r17__crs_IM_nonDSS_30kHzSCS_r17 z, (CRS_InterfMitigation_r17__crs_IM_nonDSS_NWA_30kHzSCS_r17 z, tt))))).
Definition CRS_InterfMitigation_r17__F2 (y : seq_type CRS_InterfMitigation_r17__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__CRS_InterfMitigation_r17__Type i0 i1 i2 i3 i4
  end.
Lemma CRS_InterfMitigation_r17__F1F2_cond (z : CRS_InterfMitigation_r17__Type)
  : CRS_InterfMitigation_r17__cond z ->
  (seq_cond CRS_InterfMitigation_r17__list (CRS_InterfMitigation_r17__F1 z)).
intro H. unfold CRS_InterfMitigation_r17__cond in H. simpl. auto. Qed.
Lemma CRS_InterfMitigation_r17__F1F2_cond2 (z : CRS_InterfMitigation_r17__Type)
 : CRS_InterfMitigation_r17__F2 (CRS_InterfMitigation_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CRS_InterfMitigation_r17__F2F1_cond (y : seq_type CRS_InterfMitigation_r17__list)
  : seq_cond CRS_InterfMitigation_r17__list y ->
 (CRS_InterfMitigation_r17__cond (CRS_InterfMitigation_r17__F2 y)) /\  CRS_InterfMitigation_r17__F1 (CRS_InterfMitigation_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CRS_InterfMitigation_r17__cond. simpl in *. auto.
 - simpl. unfold CRS_InterfMitigation_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CRS_InterfMitigation_r17__Format : T_Format CRS_InterfMitigation_r17__Type CRS_InterfMitigation_r17__cond :=
        proj2_format  CRS_InterfMitigation_r17__cond CRS_InterfMitigation_r17__list__Format
    CRS_InterfMitigation_r17__F1 CRS_InterfMitigation_r17__F2 CRS_InterfMitigation_r17__F1F2_cond  CRS_InterfMitigation_r17__F1F2_cond2 CRS_InterfMitigation_r17__F2F1_cond.
Opaque CRS_InterfMitigation_r17__cond CRS_InterfMitigation_r17__Format.

