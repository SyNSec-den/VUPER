Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Type : Set :=
 | HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__true
.
Definition HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__cond := (fun (_ : HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Type) => True).
Lemma HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__nat__helper.

Definition HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F1 t :=
  match t with
  | HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__true => 0
  end.
Definition HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F2 n :=
  match n with
  | 0 => HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__true
  | _ => HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__true
  end.
Lemma HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F1F2 : forall x : HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Type, (HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F1 x <= 0) /\ HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F2 (HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F1 x) = x. imp_solve. Qed.
Lemma HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F2F1 : forall (y : nat) (H : y <= 0), HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F1 (HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F2 y) = y. enum_solve H y. Qed.

Inductive HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Type : Set :=
 | HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__true
.
Definition HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__cond := (fun (_ : HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Type) => True).
Lemma HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__nat__helper.

Definition HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F1 t :=
  match t with
  | HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__true => 0
  end.
Definition HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F2 n :=
  match n with
  | 0 => HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__true
  | _ => HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__true
  end.
Lemma HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F1F2 : forall x : HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Type, (HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F1 x <= 0) /\ HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F2 (HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F1 x) = x. imp_solve. Qed.
Lemma HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F2F1 : forall (y : nat) (H : y <= 0), HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F1 (HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F2 y) = y. enum_solve H y. Qed.

Inductive HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Type : Set :=
 | HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__true
.
Definition HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__cond := (fun (_ : HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Type) => True).
Lemma HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__nat__helper.

Definition HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F1 t :=
  match t with
  | HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__true => 0
  end.
Definition HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F2 n :=
  match n with
  | 0 => HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__true
  | _ => HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__true
  end.
Lemma HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F1F2 : forall x : HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Type, (HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F1 x <= 0) /\ HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F2 (HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F1 x) = x. imp_solve. Qed.
Lemma HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F2F1 : forall (y : nat) (H : y <= 0), HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F1 (HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F2 y) = y. enum_solve H y. Qed.

Record HighSpeedConfig_v1700__Type : Set :=
  make__HighSpeedConfig_v1700__Type {
    HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17 : option HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Type ;
    HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17 : option HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Type ;
    HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17 : option HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Type ;
}.
Definition HighSpeedConfig_v1700__root_list : list seq_elem := (
 Opt HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Type HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__cond ::
 Opt HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Type HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__cond ::
 Opt HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Type HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__cond ::
 nil).
Definition HighSpeedConfig_v1700__ext_list : list typ := (
  nil).
Definition HighSpeedConfig_v1700__cond (z : HighSpeedConfig_v1700__Type) := 
(  opt_cond HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__cond (HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17 z) /\
  opt_cond HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__cond (HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17 z) /\
  opt_cond HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__cond (HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17 z) /\
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
Definition HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Format : T_Format HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__nat__Format HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F1 HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F2 HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F1F2 HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__F2F1.

Opaque HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__cond HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Format.

Definition HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Format : T_Format HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__nat__Format HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F1 HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F2 HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F1F2 HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__F2F1.

Opaque HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__cond HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Format.

Definition HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Format : T_Format HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__nat__Format HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F1 HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F2 HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F1F2 HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__F2F1.

Opaque HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__cond HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Format.


Definition HighSpeedConfig_v1700__root_Format_Type := Eval cbn in seq_format_prod HighSpeedConfig_v1700__root_list.
Definition HighSpeedConfig_v1700__root_Format_list : HighSpeedConfig_v1700__root_Format_Type :=
  (HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17__Format, (HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17__Format, (HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17__Format, unit_format))).

Definition HighSpeedConfig_v1700__ext_Format_Type := Eval cbn in get_formats HighSpeedConfig_v1700__ext_list.
Definition HighSpeedConfig_v1700__ext_Format_list : HighSpeedConfig_v1700__ext_Format_Type :=
  unit__Format.

Definition HighSpeedConfig_v1700__list_type : Set := (seq_type HighSpeedConfig_v1700__root_list) * (seq_ext_type HighSpeedConfig_v1700__ext_list).
Definition HighSpeedConfig_v1700__list_cond (z : HighSpeedConfig_v1700__list_type) : Prop :=
        (seq_cond HighSpeedConfig_v1700__root_list (fst z)) /\ (seq_ext_cond HighSpeedConfig_v1700__ext_list (snd z)).
Definition HighSpeedConfig_v1700__list_format : T_Format HighSpeedConfig_v1700__list_type HighSpeedConfig_v1700__list_cond :=
 (* Eval compute in *) seq_ext_format HighSpeedConfig_v1700__root_list HighSpeedConfig_v1700__root_Format_list HighSpeedConfig_v1700__ext_list HighSpeedConfig_v1700__ext_Format_list.

Opaque HighSpeedConfig_v1700__list_format.
Definition HighSpeedConfig_v1700__F1 (z : HighSpeedConfig_v1700__Type) : HighSpeedConfig_v1700__list_type :=
  (((HighSpeedConfig_v1700__highSpeedMeasCA_Scell_r17 z, (HighSpeedConfig_v1700__highSpeedMeasInterFreq_r17 z, (HighSpeedConfig_v1700__highSpeedDemodCA_Scell_r17 z, tt)))), (
tt)).
Definition HighSpeedConfig_v1700__F2 (y : HighSpeedConfig_v1700__list_type) : HighSpeedConfig_v1700__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__HighSpeedConfig_v1700__Type j0 j1 j2
  end.
Definition HighSpeedConfig_v1700__helper1 : (forall a : HighSpeedConfig_v1700__Type, HighSpeedConfig_v1700__cond a -> HighSpeedConfig_v1700__list_cond (HighSpeedConfig_v1700__F1 a)).
                     intros. destruct a. auto. Qed.
Definition HighSpeedConfig_v1700__helper2 : (forall a : HighSpeedConfig_v1700__Type, HighSpeedConfig_v1700__F2 (HighSpeedConfig_v1700__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition HighSpeedConfig_v1700__helper3 : (forall b : HighSpeedConfig_v1700__list_type, HighSpeedConfig_v1700__list_cond b -> HighSpeedConfig_v1700__cond (HighSpeedConfig_v1700__F2 b) /\ HighSpeedConfig_v1700__F1 (HighSpeedConfig_v1700__F2 b) = b).
                     intros. destruct b as [y y1]. unfold HighSpeedConfig_v1700__cond, HighSpeedConfig_v1700__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition HighSpeedConfig_v1700__Format : T_Format HighSpeedConfig_v1700__Type HighSpeedConfig_v1700__cond :=
 proj2_format HighSpeedConfig_v1700__cond HighSpeedConfig_v1700__list_format  HighSpeedConfig_v1700__F1 HighSpeedConfig_v1700__F2 HighSpeedConfig_v1700__helper1 HighSpeedConfig_v1700__helper2 HighSpeedConfig_v1700__helper3.

Opaque HighSpeedConfig_v1700__cond HighSpeedConfig_v1700__Format.

