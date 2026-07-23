Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NRDC_Parameters_v15c0.

Opaque NRDC_Parameters_v15c0__cond NRDC_Parameters_v15c0__Format.

Inductive UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Type : Set :=
 | UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__true
.
Definition UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__cond := (fun (_ : UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Type) => True).
Lemma UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__nat__helper.

Definition UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F1 t :=
  match t with
  | UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__true => 0
  end.
Definition UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F2 n :=
  match n with
  | 0 => UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__true
  | _ => UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__true
  end.
Lemma UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F1F2 : forall x : UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Type, (UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F1 x <= 0) /\ UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F2 (UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F1 x) = x. imp_solve. Qed.
Lemma UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F2F1 : forall (y : nat) (H : y <= 0), UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F1 (UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F2 y) = y. enum_solve H y. Qed.

Require Import NR.UE_NR_Capability_v15g0.

Opaque UE_NR_Capability_v15g0__cond UE_NR_Capability_v15g0__Format.

Record UE_NR_Capability_v15c0__Type : Set :=
  make__UE_NR_Capability_v15c0__Type {
    UE_NR_Capability_v15c0__nrdc_Parameters_v15c0 : option NRDC_Parameters_v15c0__Type ;
    UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req : option UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Type ;
    UE_NR_Capability_v15c0__nonCriticalExtension : option UE_NR_Capability_v15g0__Type ;
}.
Definition UE_NR_Capability_v15c0__list := (
 Opt NRDC_Parameters_v15c0__Type NRDC_Parameters_v15c0__cond ::
 Opt UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Type UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__cond ::
 Opt UE_NR_Capability_v15g0__Type UE_NR_Capability_v15g0__cond ::
 nil).
Definition UE_NR_Capability_v15c0__cond z := 
  opt_cond NRDC_Parameters_v15c0__cond (UE_NR_Capability_v15c0__nrdc_Parameters_v15c0 z) /\
  opt_cond UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__cond (UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req z) /\
  opt_cond UE_NR_Capability_v15g0__cond (UE_NR_Capability_v15c0__nonCriticalExtension z) /\
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
Definition UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Format : T_Format UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Type (fun _ => True) :=
(* Eval compute in *) proj3_format UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__nat__Format UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F1 UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F2 UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F1F2 UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__F2F1.

Opaque UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__cond UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Format.


Definition UE_NR_Capability_v15c0__Format_Type := Eval cbn in seq_format_prod UE_NR_Capability_v15c0__list.
Definition UE_NR_Capability_v15c0__Format_list : UE_NR_Capability_v15c0__Format_Type :=
  (NRDC_Parameters_v15c0__Format, (UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req__Format, (UE_NR_Capability_v15g0__Format, unit_format))).
Definition UE_NR_Capability_v15c0__list__Format := (*Eval compute in *) seq_format UE_NR_Capability_v15c0__list UE_NR_Capability_v15c0__Format_list.
Definition UE_NR_Capability_v15c0__F1 z :=
  (UE_NR_Capability_v15c0__nrdc_Parameters_v15c0 z, (UE_NR_Capability_v15c0__partialFR2_FallbackRX_Req z, (UE_NR_Capability_v15c0__nonCriticalExtension z, tt))).
Definition UE_NR_Capability_v15c0__F2 (y : seq_type UE_NR_Capability_v15c0__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__UE_NR_Capability_v15c0__Type i0 i1 i2
  end.
Lemma UE_NR_Capability_v15c0__F1F2_cond (z : UE_NR_Capability_v15c0__Type)
  : UE_NR_Capability_v15c0__cond z ->
  (seq_cond UE_NR_Capability_v15c0__list (UE_NR_Capability_v15c0__F1 z)).
intro H. unfold UE_NR_Capability_v15c0__cond in H. simpl. auto. Qed.
Lemma UE_NR_Capability_v15c0__F1F2_cond2 (z : UE_NR_Capability_v15c0__Type)
 : UE_NR_Capability_v15c0__F2 (UE_NR_Capability_v15c0__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma UE_NR_Capability_v15c0__F2F1_cond (y : seq_type UE_NR_Capability_v15c0__list)
  : seq_cond UE_NR_Capability_v15c0__list y ->
 (UE_NR_Capability_v15c0__cond (UE_NR_Capability_v15c0__F2 y)) /\  UE_NR_Capability_v15c0__F1 (UE_NR_Capability_v15c0__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold UE_NR_Capability_v15c0__cond. simpl in *. auto.
 - simpl. unfold UE_NR_Capability_v15c0__F1. simpl. destruct_all_unit. auto.   Qed.
Definition UE_NR_Capability_v15c0__Format : T_Format UE_NR_Capability_v15c0__Type UE_NR_Capability_v15c0__cond :=
        proj2_format  UE_NR_Capability_v15c0__cond UE_NR_Capability_v15c0__list__Format
    UE_NR_Capability_v15c0__F1 UE_NR_Capability_v15c0__F2 UE_NR_Capability_v15c0__F1F2_cond  UE_NR_Capability_v15c0__F1F2_cond2 UE_NR_Capability_v15c0__F2F1_cond.
Opaque UE_NR_Capability_v15c0__cond UE_NR_Capability_v15c0__Format.

