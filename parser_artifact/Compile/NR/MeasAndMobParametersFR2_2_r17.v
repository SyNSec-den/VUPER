Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Type : Set :=
 | MeasAndMobParametersFR2_2_r17__handoverInterF_r17__supported
.
Definition MeasAndMobParametersFR2_2_r17__handoverInterF_r17__cond := (fun (_ : MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Type) => True).
Lemma MeasAndMobParametersFR2_2_r17__handoverInterF_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFR2_2_r17__handoverInterF_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFR2_2_r17__handoverInterF_r17__nat__helper.

Definition MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F1 t :=
  match t with
  | MeasAndMobParametersFR2_2_r17__handoverInterF_r17__supported => 0
  end.
Definition MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFR2_2_r17__handoverInterF_r17__supported
  | _ => MeasAndMobParametersFR2_2_r17__handoverInterF_r17__supported
  end.
Lemma MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F1F2 : forall x : MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Type, (MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F1 x <= 0) /\ MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F2 (MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F1 (MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Type : Set :=
 | MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__supported
.
Definition MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__cond := (fun (_ : MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Type) => True).
Lemma MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__nat__helper.

Definition MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F1 t :=
  match t with
  | MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__supported => 0
  end.
Definition MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__supported
  | _ => MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__supported
  end.
Lemma MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F1F2 : forall x : MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Type, (MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F1 x <= 0) /\ MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F2 (MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F1 (MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Type : Set :=
 | MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__supported
.
Definition MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__cond := (fun (_ : MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Type) => True).
Lemma MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__nat__helper.

Definition MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F1 t :=
  match t with
  | MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__supported => 0
  end.
Definition MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__supported
  | _ => MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__supported
  end.
Lemma MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F1F2 : forall x : MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Type, (MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F1 x <= 0) /\ MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F2 (MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F1 (MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Type : Set :=
 | MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__supported
.
Definition MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__cond := (fun (_ : MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Type) => True).
Lemma MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__nat__helper.

Definition MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F1 t :=
  match t with
  | MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__supported => 0
  end.
Definition MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F2 n :=
  match n with
  | 0 => MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__supported
  | _ => MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__supported
  end.
Lemma MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F1F2 : forall x : MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Type, (MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F1 x <= 0) /\ MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F2 (MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F1 x) = x. imp_solve. Qed.
Lemma MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F2F1 : forall (y : nat) (H : y <= 0), MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F1 (MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F2 y) = y. enum_solve H y. Qed.

Record MeasAndMobParametersFR2_2_r17__Type : Set :=
  make__MeasAndMobParametersFR2_2_r17__Type {
    MeasAndMobParametersFR2_2_r17__handoverInterF_r17 : option MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Type ;
    MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17 : option MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Type ;
    MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17 : option MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Type ;
    MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17 : option MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Type ;
}.
Definition MeasAndMobParametersFR2_2_r17__root_list : list seq_elem := (
 Opt MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Type MeasAndMobParametersFR2_2_r17__handoverInterF_r17__cond ::
 Opt MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Type MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__cond ::
 Opt MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Type MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__cond ::
 Opt MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Type MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__cond ::
 nil).
Definition MeasAndMobParametersFR2_2_r17__ext_list : list typ := (
  nil).
Definition MeasAndMobParametersFR2_2_r17__cond (z : MeasAndMobParametersFR2_2_r17__Type) := 
(  opt_cond MeasAndMobParametersFR2_2_r17__handoverInterF_r17__cond (MeasAndMobParametersFR2_2_r17__handoverInterF_r17 z) /\
  opt_cond MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__cond (MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17 z) /\
  opt_cond MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__cond (MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17 z) /\
  opt_cond MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__cond (MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17 z) /\
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
Definition MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Format : T_Format MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFR2_2_r17__handoverInterF_r17__nat__Format MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F1 MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F2 MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F1F2 MeasAndMobParametersFR2_2_r17__handoverInterF_r17__F2F1.

Opaque MeasAndMobParametersFR2_2_r17__handoverInterF_r17__cond MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Format.

Definition MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Format : T_Format MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__nat__Format MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F1 MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F2 MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F1F2 MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__F2F1.

Opaque MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__cond MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Format.

Definition MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Format : T_Format MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__nat__Format MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F1 MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F2 MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F1F2 MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__F2F1.

Opaque MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__cond MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Format.

Definition MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Format : T_Format MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__nat__Format MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F1 MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F2 MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F1F2 MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__F2F1.

Opaque MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__cond MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Format.


Definition MeasAndMobParametersFR2_2_r17__root_Format_Type := Eval cbn in seq_format_prod MeasAndMobParametersFR2_2_r17__root_list.
Definition MeasAndMobParametersFR2_2_r17__root_Format_list : MeasAndMobParametersFR2_2_r17__root_Format_Type :=
  (MeasAndMobParametersFR2_2_r17__handoverInterF_r17__Format, (MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17__Format, (MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17__Format, (MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17__Format, unit_format)))).

Definition MeasAndMobParametersFR2_2_r17__ext_Format_Type := Eval cbn in get_formats MeasAndMobParametersFR2_2_r17__ext_list.
Definition MeasAndMobParametersFR2_2_r17__ext_Format_list : MeasAndMobParametersFR2_2_r17__ext_Format_Type :=
  unit__Format.

Definition MeasAndMobParametersFR2_2_r17__list_type : Set := (seq_type MeasAndMobParametersFR2_2_r17__root_list) * (seq_ext_type MeasAndMobParametersFR2_2_r17__ext_list).
Definition MeasAndMobParametersFR2_2_r17__list_cond (z : MeasAndMobParametersFR2_2_r17__list_type) : Prop :=
        (seq_cond MeasAndMobParametersFR2_2_r17__root_list (fst z)) /\ (seq_ext_cond MeasAndMobParametersFR2_2_r17__ext_list (snd z)).
Definition MeasAndMobParametersFR2_2_r17__list_format : T_Format MeasAndMobParametersFR2_2_r17__list_type MeasAndMobParametersFR2_2_r17__list_cond :=
 (* Eval compute in *) seq_ext_format MeasAndMobParametersFR2_2_r17__root_list MeasAndMobParametersFR2_2_r17__root_Format_list MeasAndMobParametersFR2_2_r17__ext_list MeasAndMobParametersFR2_2_r17__ext_Format_list.

Opaque MeasAndMobParametersFR2_2_r17__list_format.
Definition MeasAndMobParametersFR2_2_r17__F1 (z : MeasAndMobParametersFR2_2_r17__Type) : MeasAndMobParametersFR2_2_r17__list_type :=
  (((MeasAndMobParametersFR2_2_r17__handoverInterF_r17 z, (MeasAndMobParametersFR2_2_r17__handoverLTE_EPC_r17 z, (MeasAndMobParametersFR2_2_r17__handoverLTE_5GC_r17 z, (MeasAndMobParametersFR2_2_r17__idleInactiveNR_MeasReport_r17 z, tt))))), (
tt)).
Definition MeasAndMobParametersFR2_2_r17__F2 (y : MeasAndMobParametersFR2_2_r17__list_type) : MeasAndMobParametersFR2_2_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__MeasAndMobParametersFR2_2_r17__Type j0 j1 j2 j3
  end.
Definition MeasAndMobParametersFR2_2_r17__helper1 : (forall a : MeasAndMobParametersFR2_2_r17__Type, MeasAndMobParametersFR2_2_r17__cond a -> MeasAndMobParametersFR2_2_r17__list_cond (MeasAndMobParametersFR2_2_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasAndMobParametersFR2_2_r17__helper2 : (forall a : MeasAndMobParametersFR2_2_r17__Type, MeasAndMobParametersFR2_2_r17__F2 (MeasAndMobParametersFR2_2_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasAndMobParametersFR2_2_r17__helper3 : (forall b : MeasAndMobParametersFR2_2_r17__list_type, MeasAndMobParametersFR2_2_r17__list_cond b -> MeasAndMobParametersFR2_2_r17__cond (MeasAndMobParametersFR2_2_r17__F2 b) /\ MeasAndMobParametersFR2_2_r17__F1 (MeasAndMobParametersFR2_2_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasAndMobParametersFR2_2_r17__cond, MeasAndMobParametersFR2_2_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasAndMobParametersFR2_2_r17__Format : T_Format MeasAndMobParametersFR2_2_r17__Type MeasAndMobParametersFR2_2_r17__cond :=
 proj2_format MeasAndMobParametersFR2_2_r17__cond MeasAndMobParametersFR2_2_r17__list_format  MeasAndMobParametersFR2_2_r17__F1 MeasAndMobParametersFR2_2_r17__F2 MeasAndMobParametersFR2_2_r17__helper1 MeasAndMobParametersFR2_2_r17__helper2 MeasAndMobParametersFR2_2_r17__helper3.

Opaque MeasAndMobParametersFR2_2_r17__cond MeasAndMobParametersFR2_2_r17__Format.

