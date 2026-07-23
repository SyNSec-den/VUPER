Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive TAR_Config_r17__offsetThresholdTA_r17__Type : Set :=
 | TAR_Config_r17__offsetThresholdTA_r17__ms0dot5
 | TAR_Config_r17__offsetThresholdTA_r17__ms1
 | TAR_Config_r17__offsetThresholdTA_r17__ms2
 | TAR_Config_r17__offsetThresholdTA_r17__ms3
 | TAR_Config_r17__offsetThresholdTA_r17__ms4
 | TAR_Config_r17__offsetThresholdTA_r17__ms5
 | TAR_Config_r17__offsetThresholdTA_r17__ms6
 | TAR_Config_r17__offsetThresholdTA_r17__ms7
 | TAR_Config_r17__offsetThresholdTA_r17__ms8
 | TAR_Config_r17__offsetThresholdTA_r17__ms9
 | TAR_Config_r17__offsetThresholdTA_r17__ms10
 | TAR_Config_r17__offsetThresholdTA_r17__ms11
 | TAR_Config_r17__offsetThresholdTA_r17__ms12
 | TAR_Config_r17__offsetThresholdTA_r17__ms13
 | TAR_Config_r17__offsetThresholdTA_r17__ms14
 | TAR_Config_r17__offsetThresholdTA_r17__ms15
 | TAR_Config_r17__offsetThresholdTA_r17__spare13
 | TAR_Config_r17__offsetThresholdTA_r17__spare12
 | TAR_Config_r17__offsetThresholdTA_r17__spare11
 | TAR_Config_r17__offsetThresholdTA_r17__spare10
 | TAR_Config_r17__offsetThresholdTA_r17__spare9
 | TAR_Config_r17__offsetThresholdTA_r17__spare8
 | TAR_Config_r17__offsetThresholdTA_r17__spare7
 | TAR_Config_r17__offsetThresholdTA_r17__spare6
 | TAR_Config_r17__offsetThresholdTA_r17__spare5
 | TAR_Config_r17__offsetThresholdTA_r17__spare4
 | TAR_Config_r17__offsetThresholdTA_r17__spare3
 | TAR_Config_r17__offsetThresholdTA_r17__spare2
 | TAR_Config_r17__offsetThresholdTA_r17__spare1
.
Definition TAR_Config_r17__offsetThresholdTA_r17__cond := (fun (_ : TAR_Config_r17__offsetThresholdTA_r17__Type) => True).
Lemma TAR_Config_r17__offsetThresholdTA_r17__nat__helper : to_bit_sz 28 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition TAR_Config_r17__offsetThresholdTA_r17__nat__Format : T_Format nat (fun z => (z <= 28)) :=
  nat_enum_format 28 TAR_Config_r17__offsetThresholdTA_r17__nat__helper.

Definition TAR_Config_r17__offsetThresholdTA_r17__F1 t :=
  match t with
  | TAR_Config_r17__offsetThresholdTA_r17__ms0dot5 => 0
  | TAR_Config_r17__offsetThresholdTA_r17__ms1 => 1
  | TAR_Config_r17__offsetThresholdTA_r17__ms2 => 2
  | TAR_Config_r17__offsetThresholdTA_r17__ms3 => 3
  | TAR_Config_r17__offsetThresholdTA_r17__ms4 => 4
  | TAR_Config_r17__offsetThresholdTA_r17__ms5 => 5
  | TAR_Config_r17__offsetThresholdTA_r17__ms6 => 6
  | TAR_Config_r17__offsetThresholdTA_r17__ms7 => 7
  | TAR_Config_r17__offsetThresholdTA_r17__ms8 => 8
  | TAR_Config_r17__offsetThresholdTA_r17__ms9 => 9
  | TAR_Config_r17__offsetThresholdTA_r17__ms10 => 10
  | TAR_Config_r17__offsetThresholdTA_r17__ms11 => 11
  | TAR_Config_r17__offsetThresholdTA_r17__ms12 => 12
  | TAR_Config_r17__offsetThresholdTA_r17__ms13 => 13
  | TAR_Config_r17__offsetThresholdTA_r17__ms14 => 14
  | TAR_Config_r17__offsetThresholdTA_r17__ms15 => 15
  | TAR_Config_r17__offsetThresholdTA_r17__spare13 => 16
  | TAR_Config_r17__offsetThresholdTA_r17__spare12 => 17
  | TAR_Config_r17__offsetThresholdTA_r17__spare11 => 18
  | TAR_Config_r17__offsetThresholdTA_r17__spare10 => 19
  | TAR_Config_r17__offsetThresholdTA_r17__spare9 => 20
  | TAR_Config_r17__offsetThresholdTA_r17__spare8 => 21
  | TAR_Config_r17__offsetThresholdTA_r17__spare7 => 22
  | TAR_Config_r17__offsetThresholdTA_r17__spare6 => 23
  | TAR_Config_r17__offsetThresholdTA_r17__spare5 => 24
  | TAR_Config_r17__offsetThresholdTA_r17__spare4 => 25
  | TAR_Config_r17__offsetThresholdTA_r17__spare3 => 26
  | TAR_Config_r17__offsetThresholdTA_r17__spare2 => 27
  | TAR_Config_r17__offsetThresholdTA_r17__spare1 => 28
  end.
Definition TAR_Config_r17__offsetThresholdTA_r17__F2 n :=
  match n with
  | 0 => TAR_Config_r17__offsetThresholdTA_r17__ms0dot5
  | 1 => TAR_Config_r17__offsetThresholdTA_r17__ms1
  | 2 => TAR_Config_r17__offsetThresholdTA_r17__ms2
  | 3 => TAR_Config_r17__offsetThresholdTA_r17__ms3
  | 4 => TAR_Config_r17__offsetThresholdTA_r17__ms4
  | 5 => TAR_Config_r17__offsetThresholdTA_r17__ms5
  | 6 => TAR_Config_r17__offsetThresholdTA_r17__ms6
  | 7 => TAR_Config_r17__offsetThresholdTA_r17__ms7
  | 8 => TAR_Config_r17__offsetThresholdTA_r17__ms8
  | 9 => TAR_Config_r17__offsetThresholdTA_r17__ms9
  | 10 => TAR_Config_r17__offsetThresholdTA_r17__ms10
  | 11 => TAR_Config_r17__offsetThresholdTA_r17__ms11
  | 12 => TAR_Config_r17__offsetThresholdTA_r17__ms12
  | 13 => TAR_Config_r17__offsetThresholdTA_r17__ms13
  | 14 => TAR_Config_r17__offsetThresholdTA_r17__ms14
  | 15 => TAR_Config_r17__offsetThresholdTA_r17__ms15
  | 16 => TAR_Config_r17__offsetThresholdTA_r17__spare13
  | 17 => TAR_Config_r17__offsetThresholdTA_r17__spare12
  | 18 => TAR_Config_r17__offsetThresholdTA_r17__spare11
  | 19 => TAR_Config_r17__offsetThresholdTA_r17__spare10
  | 20 => TAR_Config_r17__offsetThresholdTA_r17__spare9
  | 21 => TAR_Config_r17__offsetThresholdTA_r17__spare8
  | 22 => TAR_Config_r17__offsetThresholdTA_r17__spare7
  | 23 => TAR_Config_r17__offsetThresholdTA_r17__spare6
  | 24 => TAR_Config_r17__offsetThresholdTA_r17__spare5
  | 25 => TAR_Config_r17__offsetThresholdTA_r17__spare4
  | 26 => TAR_Config_r17__offsetThresholdTA_r17__spare3
  | 27 => TAR_Config_r17__offsetThresholdTA_r17__spare2
  | 28 => TAR_Config_r17__offsetThresholdTA_r17__spare1
  | _ => TAR_Config_r17__offsetThresholdTA_r17__ms0dot5
  end.
Lemma TAR_Config_r17__offsetThresholdTA_r17__F1F2 : forall x : TAR_Config_r17__offsetThresholdTA_r17__Type, (TAR_Config_r17__offsetThresholdTA_r17__F1 x <= 28) /\ TAR_Config_r17__offsetThresholdTA_r17__F2 (TAR_Config_r17__offsetThresholdTA_r17__F1 x) = x. imp_solve. Qed.
Lemma TAR_Config_r17__offsetThresholdTA_r17__F2F1 : forall (y : nat) (H : y <= 28), TAR_Config_r17__offsetThresholdTA_r17__F1 (TAR_Config_r17__offsetThresholdTA_r17__F2 y) = y. enum_solve H y. Qed.

Inductive TAR_Config_r17__timingAdvanceSR_r17__Type : Set :=
 | TAR_Config_r17__timingAdvanceSR_r17__enabled
.
Definition TAR_Config_r17__timingAdvanceSR_r17__cond := (fun (_ : TAR_Config_r17__timingAdvanceSR_r17__Type) => True).
Lemma TAR_Config_r17__timingAdvanceSR_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition TAR_Config_r17__timingAdvanceSR_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 TAR_Config_r17__timingAdvanceSR_r17__nat__helper.

Definition TAR_Config_r17__timingAdvanceSR_r17__F1 t :=
  match t with
  | TAR_Config_r17__timingAdvanceSR_r17__enabled => 0
  end.
Definition TAR_Config_r17__timingAdvanceSR_r17__F2 n :=
  match n with
  | 0 => TAR_Config_r17__timingAdvanceSR_r17__enabled
  | _ => TAR_Config_r17__timingAdvanceSR_r17__enabled
  end.
Lemma TAR_Config_r17__timingAdvanceSR_r17__F1F2 : forall x : TAR_Config_r17__timingAdvanceSR_r17__Type, (TAR_Config_r17__timingAdvanceSR_r17__F1 x <= 0) /\ TAR_Config_r17__timingAdvanceSR_r17__F2 (TAR_Config_r17__timingAdvanceSR_r17__F1 x) = x. imp_solve. Qed.
Lemma TAR_Config_r17__timingAdvanceSR_r17__F2F1 : forall (y : nat) (H : y <= 0), TAR_Config_r17__timingAdvanceSR_r17__F1 (TAR_Config_r17__timingAdvanceSR_r17__F2 y) = y. enum_solve H y. Qed.

Record TAR_Config_r17__Type : Set :=
  make__TAR_Config_r17__Type {
    TAR_Config_r17__offsetThresholdTA_r17 : option TAR_Config_r17__offsetThresholdTA_r17__Type ;
    TAR_Config_r17__timingAdvanceSR_r17 : option TAR_Config_r17__timingAdvanceSR_r17__Type ;
}.
Definition TAR_Config_r17__root_list : list seq_elem := (
 Opt TAR_Config_r17__offsetThresholdTA_r17__Type TAR_Config_r17__offsetThresholdTA_r17__cond ::
 Opt TAR_Config_r17__timingAdvanceSR_r17__Type TAR_Config_r17__timingAdvanceSR_r17__cond ::
 nil).
Definition TAR_Config_r17__ext_list : list typ := (
  nil).
Definition TAR_Config_r17__cond (z : TAR_Config_r17__Type) := 
(  opt_cond TAR_Config_r17__offsetThresholdTA_r17__cond (TAR_Config_r17__offsetThresholdTA_r17 z) /\
  opt_cond TAR_Config_r17__timingAdvanceSR_r17__cond (TAR_Config_r17__timingAdvanceSR_r17 z) /\
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
Definition TAR_Config_r17__offsetThresholdTA_r17__Format : T_Format TAR_Config_r17__offsetThresholdTA_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format TAR_Config_r17__offsetThresholdTA_r17__nat__Format TAR_Config_r17__offsetThresholdTA_r17__F1 TAR_Config_r17__offsetThresholdTA_r17__F2 TAR_Config_r17__offsetThresholdTA_r17__F1F2 TAR_Config_r17__offsetThresholdTA_r17__F2F1.

Opaque TAR_Config_r17__offsetThresholdTA_r17__cond TAR_Config_r17__offsetThresholdTA_r17__Format.

Definition TAR_Config_r17__timingAdvanceSR_r17__Format : T_Format TAR_Config_r17__timingAdvanceSR_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format TAR_Config_r17__timingAdvanceSR_r17__nat__Format TAR_Config_r17__timingAdvanceSR_r17__F1 TAR_Config_r17__timingAdvanceSR_r17__F2 TAR_Config_r17__timingAdvanceSR_r17__F1F2 TAR_Config_r17__timingAdvanceSR_r17__F2F1.

Opaque TAR_Config_r17__timingAdvanceSR_r17__cond TAR_Config_r17__timingAdvanceSR_r17__Format.


Definition TAR_Config_r17__root_Format_Type := Eval cbn in seq_format_prod TAR_Config_r17__root_list.
Definition TAR_Config_r17__root_Format_list : TAR_Config_r17__root_Format_Type :=
  (TAR_Config_r17__offsetThresholdTA_r17__Format, (TAR_Config_r17__timingAdvanceSR_r17__Format, unit_format)).

Definition TAR_Config_r17__ext_Format_Type := Eval cbn in get_formats TAR_Config_r17__ext_list.
Definition TAR_Config_r17__ext_Format_list : TAR_Config_r17__ext_Format_Type :=
  unit__Format.

Definition TAR_Config_r17__list_type : Set := (seq_type TAR_Config_r17__root_list) * (seq_ext_type TAR_Config_r17__ext_list).
Definition TAR_Config_r17__list_cond (z : TAR_Config_r17__list_type) : Prop :=
        (seq_cond TAR_Config_r17__root_list (fst z)) /\ (seq_ext_cond TAR_Config_r17__ext_list (snd z)).
Definition TAR_Config_r17__list_format : T_Format TAR_Config_r17__list_type TAR_Config_r17__list_cond :=
 (* Eval compute in *) seq_ext_format TAR_Config_r17__root_list TAR_Config_r17__root_Format_list TAR_Config_r17__ext_list TAR_Config_r17__ext_Format_list.

Opaque TAR_Config_r17__list_format.
Definition TAR_Config_r17__F1 (z : TAR_Config_r17__Type) : TAR_Config_r17__list_type :=
  (((TAR_Config_r17__offsetThresholdTA_r17 z, (TAR_Config_r17__timingAdvanceSR_r17 z, tt))), (
tt)).
Definition TAR_Config_r17__F2 (y : TAR_Config_r17__list_type) : TAR_Config_r17__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__TAR_Config_r17__Type j0 j1
  end.
Definition TAR_Config_r17__helper1 : (forall a : TAR_Config_r17__Type, TAR_Config_r17__cond a -> TAR_Config_r17__list_cond (TAR_Config_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition TAR_Config_r17__helper2 : (forall a : TAR_Config_r17__Type, TAR_Config_r17__F2 (TAR_Config_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition TAR_Config_r17__helper3 : (forall b : TAR_Config_r17__list_type, TAR_Config_r17__list_cond b -> TAR_Config_r17__cond (TAR_Config_r17__F2 b) /\ TAR_Config_r17__F1 (TAR_Config_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold TAR_Config_r17__cond, TAR_Config_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition TAR_Config_r17__Format : T_Format TAR_Config_r17__Type TAR_Config_r17__cond :=
 proj2_format TAR_Config_r17__cond TAR_Config_r17__list_format  TAR_Config_r17__F1 TAR_Config_r17__F2 TAR_Config_r17__helper1 TAR_Config_r17__helper2 TAR_Config_r17__helper3.

Opaque TAR_Config_r17__cond TAR_Config_r17__Format.

