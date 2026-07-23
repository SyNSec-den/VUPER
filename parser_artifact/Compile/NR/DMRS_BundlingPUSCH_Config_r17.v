Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Type : Set :=
 | DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__enabled
.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__cond := (fun (_ : DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Type) => True).
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__nat__helper.

Definition DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F1 t :=
  match t with
  | DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__enabled => 0
  end.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F2 n :=
  match n with
  | 0 => DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__enabled
  | _ => DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__enabled
  end.
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F1F2 : forall x : DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Type, (DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F1 x <= 0) /\ DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F2 (DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F1 x) = x. imp_solve. Qed.
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F2F1 : forall (y : nat) (H : y <= 0), DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F1 (DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F2 y) = y. enum_solve H y. Qed.

Lemma DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__helper1 : (2 <= 32)%Z.  lia. Qed.
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__helper2 : to_bit_sz (Z.to_nat (32 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__Type := Z.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__cond := (fun z => (2 <= z <= 32)%Z).
Inductive DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Type : Set :=
 | DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__enabled
.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__cond := (fun (_ : DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Type) => True).
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__nat__helper.

Definition DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F1 t :=
  match t with
  | DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__enabled => 0
  end.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F2 n :=
  match n with
  | 0 => DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__enabled
  | _ => DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__enabled
  end.
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F1F2 : forall x : DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Type, (DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F1 x <= 0) /\ DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F2 (DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F1 x) = x. imp_solve. Qed.
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F2F1 : forall (y : nat) (H : y <= 0), DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F1 (DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F2 y) = y. enum_solve H y. Qed.

Inductive DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Type : Set :=
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s2
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s4
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s5
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s6
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s8
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s10
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s12
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s14
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s16
 | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s20
.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__cond := (fun (_ : DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Type) => True).
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__nat__helper : to_bit_sz 9 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__nat__Format : T_Format nat (fun z => (z <= 9)) :=
  nat_enum_format 9 DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__nat__helper.

Definition DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F1 t :=
  match t with
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s2 => 0
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s4 => 1
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s5 => 2
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s6 => 3
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s8 => 4
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s10 => 5
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s12 => 6
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s14 => 7
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s16 => 8
  | DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s20 => 9
  end.
Definition DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F2 n :=
  match n with
  | 0 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s2
  | 1 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s4
  | 2 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s5
  | 3 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s6
  | 4 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s8
  | 5 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s10
  | 6 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s12
  | 7 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s14
  | 8 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s16
  | 9 => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s20
  | _ => DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__s2
  end.
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F1F2 : forall x : DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Type, (DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F1 x <= 9) /\ DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F2 (DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F1 x) = x. imp_solve. Qed.
Lemma DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F2F1 : forall (y : nat) (H : y <= 9), DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F1 (DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F2 y) = y. enum_solve H y. Qed.

Record DMRS_BundlingPUSCH_Config_r17__Type : Set :=
  make__DMRS_BundlingPUSCH_Config_r17__Type {
    DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17 : option DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Type ;
    DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17 : option Z ;
    DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17 : option DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Type ;
    DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17 : option DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Type ;
}.
Definition DMRS_BundlingPUSCH_Config_r17__root_list : list seq_elem := (
 Opt DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Type DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__cond ::
 Opt Z DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__cond ::
 Opt DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Type DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__cond ::
 Opt DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Type DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__cond ::
 nil).
Definition DMRS_BundlingPUSCH_Config_r17__ext_list : list typ := (
  nil).
Definition DMRS_BundlingPUSCH_Config_r17__cond (z : DMRS_BundlingPUSCH_Config_r17__Type) := 
(  opt_cond DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__cond (DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17 z) /\
  opt_cond DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__cond (DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17 z) /\
  opt_cond DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__cond (DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17 z) /\
  opt_cond DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__cond (DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17 z) /\
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
Definition DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Format : T_Format DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__nat__Format DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F1 DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F2 DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F1F2 DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__F2F1.

Opaque DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__cond DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Format.

Definition DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__Format : T_Format Z DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__cond :=
 ranged_int_format (2) (32) DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__helper1 DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__helper2.

Opaque DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__cond DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__Format.

Definition DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Format : T_Format DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__nat__Format DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F1 DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F2 DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F1F2 DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__F2F1.

Opaque DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__cond DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Format.

Definition DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Format : T_Format DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__nat__Format DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F1 DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F2 DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F1F2 DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__F2F1.

Opaque DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__cond DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Format.


Definition DMRS_BundlingPUSCH_Config_r17__root_Format_Type := Eval cbn in seq_format_prod DMRS_BundlingPUSCH_Config_r17__root_list.
Definition DMRS_BundlingPUSCH_Config_r17__root_Format_list : DMRS_BundlingPUSCH_Config_r17__root_Format_Type :=
  (DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17__Format, (DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17__Format, (DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17__Format, (DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17__Format, unit_format)))).

Definition DMRS_BundlingPUSCH_Config_r17__ext_Format_Type := Eval cbn in get_formats DMRS_BundlingPUSCH_Config_r17__ext_list.
Definition DMRS_BundlingPUSCH_Config_r17__ext_Format_list : DMRS_BundlingPUSCH_Config_r17__ext_Format_Type :=
  unit__Format.

Definition DMRS_BundlingPUSCH_Config_r17__list_type : Set := (seq_type DMRS_BundlingPUSCH_Config_r17__root_list) * (seq_ext_type DMRS_BundlingPUSCH_Config_r17__ext_list).
Definition DMRS_BundlingPUSCH_Config_r17__list_cond (z : DMRS_BundlingPUSCH_Config_r17__list_type) : Prop :=
        (seq_cond DMRS_BundlingPUSCH_Config_r17__root_list (fst z)) /\ (seq_ext_cond DMRS_BundlingPUSCH_Config_r17__ext_list (snd z)).
Definition DMRS_BundlingPUSCH_Config_r17__list_format : T_Format DMRS_BundlingPUSCH_Config_r17__list_type DMRS_BundlingPUSCH_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format DMRS_BundlingPUSCH_Config_r17__root_list DMRS_BundlingPUSCH_Config_r17__root_Format_list DMRS_BundlingPUSCH_Config_r17__ext_list DMRS_BundlingPUSCH_Config_r17__ext_Format_list.

Opaque DMRS_BundlingPUSCH_Config_r17__list_format.
Definition DMRS_BundlingPUSCH_Config_r17__F1 (z : DMRS_BundlingPUSCH_Config_r17__Type) : DMRS_BundlingPUSCH_Config_r17__list_type :=
  (((DMRS_BundlingPUSCH_Config_r17__pusch_DMRS_Bundling_r17 z, (DMRS_BundlingPUSCH_Config_r17__pusch_TimeDomainWindowLength_r17 z, (DMRS_BundlingPUSCH_Config_r17__pusch_WindowRestart_r17 z, (DMRS_BundlingPUSCH_Config_r17__pusch_FrequencyHoppingInterval_r17 z, tt))))), (
tt)).
Definition DMRS_BundlingPUSCH_Config_r17__F2 (y : DMRS_BundlingPUSCH_Config_r17__list_type) : DMRS_BundlingPUSCH_Config_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__DMRS_BundlingPUSCH_Config_r17__Type j0 j1 j2 j3
  end.
Definition DMRS_BundlingPUSCH_Config_r17__helper1 : (forall a : DMRS_BundlingPUSCH_Config_r17__Type, DMRS_BundlingPUSCH_Config_r17__cond a -> DMRS_BundlingPUSCH_Config_r17__list_cond (DMRS_BundlingPUSCH_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition DMRS_BundlingPUSCH_Config_r17__helper2 : (forall a : DMRS_BundlingPUSCH_Config_r17__Type, DMRS_BundlingPUSCH_Config_r17__F2 (DMRS_BundlingPUSCH_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition DMRS_BundlingPUSCH_Config_r17__helper3 : (forall b : DMRS_BundlingPUSCH_Config_r17__list_type, DMRS_BundlingPUSCH_Config_r17__list_cond b -> DMRS_BundlingPUSCH_Config_r17__cond (DMRS_BundlingPUSCH_Config_r17__F2 b) /\ DMRS_BundlingPUSCH_Config_r17__F1 (DMRS_BundlingPUSCH_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold DMRS_BundlingPUSCH_Config_r17__cond, DMRS_BundlingPUSCH_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition DMRS_BundlingPUSCH_Config_r17__Format : T_Format DMRS_BundlingPUSCH_Config_r17__Type DMRS_BundlingPUSCH_Config_r17__cond :=
 proj2_format DMRS_BundlingPUSCH_Config_r17__cond DMRS_BundlingPUSCH_Config_r17__list_format  DMRS_BundlingPUSCH_Config_r17__F1 DMRS_BundlingPUSCH_Config_r17__F2 DMRS_BundlingPUSCH_Config_r17__helper1 DMRS_BundlingPUSCH_Config_r17__helper2 DMRS_BundlingPUSCH_Config_r17__helper3.

Opaque DMRS_BundlingPUSCH_Config_r17__cond DMRS_BundlingPUSCH_Config_r17__Format.

