Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma WLAN_RTT_r16__rttValue_r16__helper1 : (0 <= 16777215)%Z.  lia. Qed.
Lemma WLAN_RTT_r16__rttValue_r16__helper2 : to_bit_sz (Z.to_nat (16777215 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16777215 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply WLAN_RTT_r16__rttValue_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition WLAN_RTT_r16__rttValue_r16__Type := Z.
Definition WLAN_RTT_r16__rttValue_r16__cond := (fun z => (0 <= z <= 16777215)%Z).
Inductive WLAN_RTT_r16__rttUnits_r16__root__Type : Set :=
 | WLAN_RTT_r16__rttUnits_r16__root__microseconds
 | WLAN_RTT_r16__rttUnits_r16__root__hundredsofnanoseconds
 | WLAN_RTT_r16__rttUnits_r16__root__tensofnanoseconds
 | WLAN_RTT_r16__rttUnits_r16__root__nanoseconds
 | WLAN_RTT_r16__rttUnits_r16__root__tenthsofnanoseconds
.
Definition WLAN_RTT_r16__rttUnits_r16__root__cond := (fun (_ : WLAN_RTT_r16__rttUnits_r16__root__Type) => True).
Lemma WLAN_RTT_r16__rttUnits_r16__root__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition WLAN_RTT_r16__rttUnits_r16__root__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 WLAN_RTT_r16__rttUnits_r16__root__nat__helper.

Definition WLAN_RTT_r16__rttUnits_r16__root__F1 t :=
  match t with
  | WLAN_RTT_r16__rttUnits_r16__root__microseconds => 0
  | WLAN_RTT_r16__rttUnits_r16__root__hundredsofnanoseconds => 1
  | WLAN_RTT_r16__rttUnits_r16__root__tensofnanoseconds => 2
  | WLAN_RTT_r16__rttUnits_r16__root__nanoseconds => 3
  | WLAN_RTT_r16__rttUnits_r16__root__tenthsofnanoseconds => 4
  end.
Definition WLAN_RTT_r16__rttUnits_r16__root__F2 n :=
  match n with
  | 0 => WLAN_RTT_r16__rttUnits_r16__root__microseconds
  | 1 => WLAN_RTT_r16__rttUnits_r16__root__hundredsofnanoseconds
  | 2 => WLAN_RTT_r16__rttUnits_r16__root__tensofnanoseconds
  | 3 => WLAN_RTT_r16__rttUnits_r16__root__nanoseconds
  | 4 => WLAN_RTT_r16__rttUnits_r16__root__tenthsofnanoseconds
  | _ => WLAN_RTT_r16__rttUnits_r16__root__microseconds
  end.
Lemma WLAN_RTT_r16__rttUnits_r16__root__F1F2 : forall x : WLAN_RTT_r16__rttUnits_r16__root__Type, (WLAN_RTT_r16__rttUnits_r16__root__F1 x <= 4) /\ WLAN_RTT_r16__rttUnits_r16__root__F2 (WLAN_RTT_r16__rttUnits_r16__root__F1 x) = x. imp_solve. Qed.
Lemma WLAN_RTT_r16__rttUnits_r16__root__F2F1 : forall (y : nat) (H : y <= 4), WLAN_RTT_r16__rttUnits_r16__root__F1 (WLAN_RTT_r16__rttUnits_r16__root__F2 y) = y. enum_solve H y. Qed.

Definition WLAN_RTT_r16__rttUnits_r16__ext__Type : Set := Empty_set.
Definition WLAN_RTT_r16__rttUnits_r16__ext__cond := (fun (_ : WLAN_RTT_r16__rttUnits_r16__ext__Type) => True).
Definition WLAN_RTT_r16__rttUnits_r16__Type : Set := WLAN_RTT_r16__rttUnits_r16__root__Type + WLAN_RTT_r16__rttUnits_r16__ext__Type.
Definition WLAN_RTT_r16__rttUnits_r16__cond := sum_cond WLAN_RTT_r16__rttUnits_r16__root__cond WLAN_RTT_r16__rttUnits_r16__ext__cond.

Lemma WLAN_RTT_r16__rttAccuracy_r16__helper1 : (0 <= 255)%Z.  lia. Qed.
Lemma WLAN_RTT_r16__rttAccuracy_r16__helper2 : to_bit_sz (Z.to_nat (255 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (255 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply WLAN_RTT_r16__rttAccuracy_r16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition WLAN_RTT_r16__rttAccuracy_r16__Type := Z.
Definition WLAN_RTT_r16__rttAccuracy_r16__cond := (fun z => (0 <= z <= 255)%Z).
Record WLAN_RTT_r16__Type : Set :=
  make__WLAN_RTT_r16__Type {
    WLAN_RTT_r16__rttValue_r16 : Z ;
    WLAN_RTT_r16__rttUnits_r16 : WLAN_RTT_r16__rttUnits_r16__Type ;
    WLAN_RTT_r16__rttAccuracy_r16 : option Z ;
}.
Definition WLAN_RTT_r16__root_list : list seq_elem := (
 Nor Z WLAN_RTT_r16__rttValue_r16__cond ::
 Nor WLAN_RTT_r16__rttUnits_r16__Type WLAN_RTT_r16__rttUnits_r16__cond ::
 Opt Z WLAN_RTT_r16__rttAccuracy_r16__cond ::
 nil).
Definition WLAN_RTT_r16__ext_list : list typ := (
  nil).
Definition WLAN_RTT_r16__cond (z : WLAN_RTT_r16__Type) := 
(  WLAN_RTT_r16__rttValue_r16__cond (WLAN_RTT_r16__rttValue_r16 z) /\
  WLAN_RTT_r16__rttUnits_r16__cond (WLAN_RTT_r16__rttUnits_r16 z) /\
  opt_cond WLAN_RTT_r16__rttAccuracy_r16__cond (WLAN_RTT_r16__rttAccuracy_r16 z) /\
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
Definition WLAN_RTT_r16__rttValue_r16__Format : T_Format Z WLAN_RTT_r16__rttValue_r16__cond :=
 ranged_int_format (0) (16777215) WLAN_RTT_r16__rttValue_r16__helper1 WLAN_RTT_r16__rttValue_r16__helper2.

Opaque WLAN_RTT_r16__rttValue_r16__cond WLAN_RTT_r16__rttValue_r16__Format.

Definition WLAN_RTT_r16__rttUnits_r16__root__Format : T_Format WLAN_RTT_r16__rttUnits_r16__root__Type (fun _ => True) :=
(* Eval compute in *)proj3_format WLAN_RTT_r16__rttUnits_r16__root__nat__Format WLAN_RTT_r16__rttUnits_r16__root__F1 WLAN_RTT_r16__rttUnits_r16__root__F2 WLAN_RTT_r16__rttUnits_r16__root__F1F2 WLAN_RTT_r16__rttUnits_r16__root__F2F1.

Opaque WLAN_RTT_r16__rttUnits_r16__root__cond WLAN_RTT_r16__rttUnits_r16__root__Format.

Definition WLAN_RTT_r16__rttUnits_r16__ext__Format : T_Format WLAN_RTT_r16__rttUnits_r16__ext__Type WLAN_RTT_r16__rttUnits_r16__ext__cond := empty_format.

Opaque WLAN_RTT_r16__rttUnits_r16__ext__cond WLAN_RTT_r16__rttUnits_r16__ext__Format.

Definition WLAN_RTT_r16__rttUnits_r16__Format : T_Format WLAN_RTT_r16__rttUnits_r16__Type WLAN_RTT_r16__rttUnits_r16__cond := sum_format WLAN_RTT_r16__rttUnits_r16__root__Format WLAN_RTT_r16__rttUnits_r16__ext__Format.
Opaque WLAN_RTT_r16__rttUnits_r16__cond WLAN_RTT_r16__rttUnits_r16__Format.

Opaque WLAN_RTT_r16__rttUnits_r16__cond WLAN_RTT_r16__rttUnits_r16__Format.

Definition WLAN_RTT_r16__rttAccuracy_r16__Format : T_Format Z WLAN_RTT_r16__rttAccuracy_r16__cond :=
 ranged_int_format (0) (255) WLAN_RTT_r16__rttAccuracy_r16__helper1 WLAN_RTT_r16__rttAccuracy_r16__helper2.

Opaque WLAN_RTT_r16__rttAccuracy_r16__cond WLAN_RTT_r16__rttAccuracy_r16__Format.


Definition WLAN_RTT_r16__root_Format_Type := Eval cbn in seq_format_prod WLAN_RTT_r16__root_list.
Definition WLAN_RTT_r16__root_Format_list : WLAN_RTT_r16__root_Format_Type :=
  (WLAN_RTT_r16__rttValue_r16__Format, (WLAN_RTT_r16__rttUnits_r16__Format, (WLAN_RTT_r16__rttAccuracy_r16__Format, unit_format))).

Definition WLAN_RTT_r16__ext_Format_Type := Eval cbn in get_formats WLAN_RTT_r16__ext_list.
Definition WLAN_RTT_r16__ext_Format_list : WLAN_RTT_r16__ext_Format_Type :=
  unit__Format.

Definition WLAN_RTT_r16__list_type : Set := (seq_type WLAN_RTT_r16__root_list) * (seq_ext_type WLAN_RTT_r16__ext_list).
Definition WLAN_RTT_r16__list_cond (z : WLAN_RTT_r16__list_type) : Prop :=
        (seq_cond WLAN_RTT_r16__root_list (fst z)) /\ (seq_ext_cond WLAN_RTT_r16__ext_list (snd z)).
Definition WLAN_RTT_r16__list_format : T_Format WLAN_RTT_r16__list_type WLAN_RTT_r16__list_cond :=
 (* Eval compute in *) seq_ext_format WLAN_RTT_r16__root_list WLAN_RTT_r16__root_Format_list WLAN_RTT_r16__ext_list WLAN_RTT_r16__ext_Format_list.

Opaque WLAN_RTT_r16__list_format.
Definition WLAN_RTT_r16__F1 (z : WLAN_RTT_r16__Type) : WLAN_RTT_r16__list_type :=
  (((WLAN_RTT_r16__rttValue_r16 z, (WLAN_RTT_r16__rttUnits_r16 z, (WLAN_RTT_r16__rttAccuracy_r16 z, tt)))), (
tt)).
Definition WLAN_RTT_r16__F2 (y : WLAN_RTT_r16__list_type) : WLAN_RTT_r16__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__WLAN_RTT_r16__Type j0 j1 j2
  end.
Definition WLAN_RTT_r16__helper1 : (forall a : WLAN_RTT_r16__Type, WLAN_RTT_r16__cond a -> WLAN_RTT_r16__list_cond (WLAN_RTT_r16__F1 a)).
                     intros. destruct a. auto. Qed.
Definition WLAN_RTT_r16__helper2 : (forall a : WLAN_RTT_r16__Type, WLAN_RTT_r16__F2 (WLAN_RTT_r16__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition WLAN_RTT_r16__helper3 : (forall b : WLAN_RTT_r16__list_type, WLAN_RTT_r16__list_cond b -> WLAN_RTT_r16__cond (WLAN_RTT_r16__F2 b) /\ WLAN_RTT_r16__F1 (WLAN_RTT_r16__F2 b) = b).
                     intros. destruct b as [y y1]. unfold WLAN_RTT_r16__cond, WLAN_RTT_r16__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition WLAN_RTT_r16__Format : T_Format WLAN_RTT_r16__Type WLAN_RTT_r16__cond :=
 proj2_format WLAN_RTT_r16__cond WLAN_RTT_r16__list_format  WLAN_RTT_r16__F1 WLAN_RTT_r16__F2 WLAN_RTT_r16__helper1 WLAN_RTT_r16__helper2 WLAN_RTT_r16__helper3.

Opaque WLAN_RTT_r16__cond WLAN_RTT_r16__Format.

