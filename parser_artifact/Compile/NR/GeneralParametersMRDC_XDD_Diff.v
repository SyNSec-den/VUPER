Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Type : Set :=
 | GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__supported
.
Definition GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__cond := (fun (_ : GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Type) => True).
Lemma GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__nat__helper.

Definition GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F1 t :=
  match t with
  | GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__supported => 0
  end.
Definition GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F2 n :=
  match n with
  | 0 => GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__supported
  | _ => GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__supported
  end.
Lemma GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F1F2 : forall x : GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Type, (GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F1 x <= 0) /\ GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F2 (GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F1 x) = x. imp_solve. Qed.
Lemma GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F2F1 : forall (y : nat) (H : y <= 0), GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F1 (GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F2 y) = y. enum_solve H y. Qed.

Inductive GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Type : Set :=
 | GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__supported
.
Definition GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__cond := (fun (_ : GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Type) => True).
Lemma GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__nat__helper.

Definition GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F1 t :=
  match t with
  | GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__supported => 0
  end.
Definition GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F2 n :=
  match n with
  | 0 => GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__supported
  | _ => GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__supported
  end.
Lemma GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F1F2 : forall x : GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Type, (GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F1 x <= 0) /\ GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F2 (GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F1 x) = x. imp_solve. Qed.
Lemma GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F2F1 : forall (y : nat) (H : y <= 0), GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F1 (GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F2 y) = y. enum_solve H y. Qed.

Inductive GeneralParametersMRDC_XDD_Diff__srb3__Type : Set :=
 | GeneralParametersMRDC_XDD_Diff__srb3__supported
.
Definition GeneralParametersMRDC_XDD_Diff__srb3__cond := (fun (_ : GeneralParametersMRDC_XDD_Diff__srb3__Type) => True).
Lemma GeneralParametersMRDC_XDD_Diff__srb3__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GeneralParametersMRDC_XDD_Diff__srb3__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 GeneralParametersMRDC_XDD_Diff__srb3__nat__helper.

Definition GeneralParametersMRDC_XDD_Diff__srb3__F1 t :=
  match t with
  | GeneralParametersMRDC_XDD_Diff__srb3__supported => 0
  end.
Definition GeneralParametersMRDC_XDD_Diff__srb3__F2 n :=
  match n with
  | 0 => GeneralParametersMRDC_XDD_Diff__srb3__supported
  | _ => GeneralParametersMRDC_XDD_Diff__srb3__supported
  end.
Lemma GeneralParametersMRDC_XDD_Diff__srb3__F1F2 : forall x : GeneralParametersMRDC_XDD_Diff__srb3__Type, (GeneralParametersMRDC_XDD_Diff__srb3__F1 x <= 0) /\ GeneralParametersMRDC_XDD_Diff__srb3__F2 (GeneralParametersMRDC_XDD_Diff__srb3__F1 x) = x. imp_solve. Qed.
Lemma GeneralParametersMRDC_XDD_Diff__srb3__F2F1 : forall (y : nat) (H : y <= 0), GeneralParametersMRDC_XDD_Diff__srb3__F1 (GeneralParametersMRDC_XDD_Diff__srb3__F2 y) = y. enum_solve H y. Qed.

Inductive GeneralParametersMRDC_XDD_Diff__dummy__Type : Set :=
 | GeneralParametersMRDC_XDD_Diff__dummy__supported
.
Definition GeneralParametersMRDC_XDD_Diff__dummy__cond := (fun (_ : GeneralParametersMRDC_XDD_Diff__dummy__Type) => True).
Lemma GeneralParametersMRDC_XDD_Diff__dummy__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition GeneralParametersMRDC_XDD_Diff__dummy__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 GeneralParametersMRDC_XDD_Diff__dummy__nat__helper.

Definition GeneralParametersMRDC_XDD_Diff__dummy__F1 t :=
  match t with
  | GeneralParametersMRDC_XDD_Diff__dummy__supported => 0
  end.
Definition GeneralParametersMRDC_XDD_Diff__dummy__F2 n :=
  match n with
  | 0 => GeneralParametersMRDC_XDD_Diff__dummy__supported
  | _ => GeneralParametersMRDC_XDD_Diff__dummy__supported
  end.
Lemma GeneralParametersMRDC_XDD_Diff__dummy__F1F2 : forall x : GeneralParametersMRDC_XDD_Diff__dummy__Type, (GeneralParametersMRDC_XDD_Diff__dummy__F1 x <= 0) /\ GeneralParametersMRDC_XDD_Diff__dummy__F2 (GeneralParametersMRDC_XDD_Diff__dummy__F1 x) = x. imp_solve. Qed.
Lemma GeneralParametersMRDC_XDD_Diff__dummy__F2F1 : forall (y : nat) (H : y <= 0), GeneralParametersMRDC_XDD_Diff__dummy__F1 (GeneralParametersMRDC_XDD_Diff__dummy__F2 y) = y. enum_solve H y. Qed.

Record GeneralParametersMRDC_XDD_Diff__Type : Set :=
  make__GeneralParametersMRDC_XDD_Diff__Type {
    GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path : option GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Type ;
    GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG : option GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Type ;
    GeneralParametersMRDC_XDD_Diff__srb3 : option GeneralParametersMRDC_XDD_Diff__srb3__Type ;
    GeneralParametersMRDC_XDD_Diff__dummy : option GeneralParametersMRDC_XDD_Diff__dummy__Type ;
}.
Definition GeneralParametersMRDC_XDD_Diff__root_list : list seq_elem := (
 Opt GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Type GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__cond ::
 Opt GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Type GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__cond ::
 Opt GeneralParametersMRDC_XDD_Diff__srb3__Type GeneralParametersMRDC_XDD_Diff__srb3__cond ::
 Opt GeneralParametersMRDC_XDD_Diff__dummy__Type GeneralParametersMRDC_XDD_Diff__dummy__cond ::
 nil).
Definition GeneralParametersMRDC_XDD_Diff__ext_list : list typ := (
  nil).
Definition GeneralParametersMRDC_XDD_Diff__cond (z : GeneralParametersMRDC_XDD_Diff__Type) := 
(  opt_cond GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__cond (GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path z) /\
  opt_cond GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__cond (GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG z) /\
  opt_cond GeneralParametersMRDC_XDD_Diff__srb3__cond (GeneralParametersMRDC_XDD_Diff__srb3 z) /\
  opt_cond GeneralParametersMRDC_XDD_Diff__dummy__cond (GeneralParametersMRDC_XDD_Diff__dummy z) /\
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
Definition GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Format : T_Format GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__nat__Format GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F1 GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F2 GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F1F2 GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__F2F1.

Opaque GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__cond GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Format.

Definition GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Format : T_Format GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__nat__Format GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F1 GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F2 GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F1F2 GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__F2F1.

Opaque GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__cond GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Format.

Definition GeneralParametersMRDC_XDD_Diff__srb3__Format : T_Format GeneralParametersMRDC_XDD_Diff__srb3__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GeneralParametersMRDC_XDD_Diff__srb3__nat__Format GeneralParametersMRDC_XDD_Diff__srb3__F1 GeneralParametersMRDC_XDD_Diff__srb3__F2 GeneralParametersMRDC_XDD_Diff__srb3__F1F2 GeneralParametersMRDC_XDD_Diff__srb3__F2F1.

Opaque GeneralParametersMRDC_XDD_Diff__srb3__cond GeneralParametersMRDC_XDD_Diff__srb3__Format.

Definition GeneralParametersMRDC_XDD_Diff__dummy__Format : T_Format GeneralParametersMRDC_XDD_Diff__dummy__Type (fun _ => True) :=
(* Eval compute in *) proj3_format GeneralParametersMRDC_XDD_Diff__dummy__nat__Format GeneralParametersMRDC_XDD_Diff__dummy__F1 GeneralParametersMRDC_XDD_Diff__dummy__F2 GeneralParametersMRDC_XDD_Diff__dummy__F1F2 GeneralParametersMRDC_XDD_Diff__dummy__F2F1.

Opaque GeneralParametersMRDC_XDD_Diff__dummy__cond GeneralParametersMRDC_XDD_Diff__dummy__Format.


Definition GeneralParametersMRDC_XDD_Diff__root_Format_Type := Eval cbn in seq_format_prod GeneralParametersMRDC_XDD_Diff__root_list.
Definition GeneralParametersMRDC_XDD_Diff__root_Format_list : GeneralParametersMRDC_XDD_Diff__root_Format_Type :=
  (GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path__Format, (GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG__Format, (GeneralParametersMRDC_XDD_Diff__srb3__Format, (GeneralParametersMRDC_XDD_Diff__dummy__Format, unit_format)))).

Definition GeneralParametersMRDC_XDD_Diff__ext_Format_Type := Eval cbn in get_formats GeneralParametersMRDC_XDD_Diff__ext_list.
Definition GeneralParametersMRDC_XDD_Diff__ext_Format_list : GeneralParametersMRDC_XDD_Diff__ext_Format_Type :=
  unit__Format.

Definition GeneralParametersMRDC_XDD_Diff__list_type : Set := (seq_type GeneralParametersMRDC_XDD_Diff__root_list) * (seq_ext_type GeneralParametersMRDC_XDD_Diff__ext_list).
Definition GeneralParametersMRDC_XDD_Diff__list_cond (z : GeneralParametersMRDC_XDD_Diff__list_type) : Prop :=
        (seq_cond GeneralParametersMRDC_XDD_Diff__root_list (fst z)) /\ (seq_ext_cond GeneralParametersMRDC_XDD_Diff__ext_list (snd z)).
Definition GeneralParametersMRDC_XDD_Diff__list_format : T_Format GeneralParametersMRDC_XDD_Diff__list_type GeneralParametersMRDC_XDD_Diff__list_cond :=
 (* Eval compute in *) seq_ext_format GeneralParametersMRDC_XDD_Diff__root_list GeneralParametersMRDC_XDD_Diff__root_Format_list GeneralParametersMRDC_XDD_Diff__ext_list GeneralParametersMRDC_XDD_Diff__ext_Format_list.

Opaque GeneralParametersMRDC_XDD_Diff__list_format.
Definition GeneralParametersMRDC_XDD_Diff__F1 (z : GeneralParametersMRDC_XDD_Diff__Type) : GeneralParametersMRDC_XDD_Diff__list_type :=
  (((GeneralParametersMRDC_XDD_Diff__splitSRB_WithOneUL_Path z, (GeneralParametersMRDC_XDD_Diff__splitDRB_withUL_Both_MCG_SCG z, (GeneralParametersMRDC_XDD_Diff__srb3 z, (GeneralParametersMRDC_XDD_Diff__dummy z, tt))))), (
tt)).
Definition GeneralParametersMRDC_XDD_Diff__F2 (y : GeneralParametersMRDC_XDD_Diff__list_type) : GeneralParametersMRDC_XDD_Diff__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), _)=>
    make__GeneralParametersMRDC_XDD_Diff__Type j0 j1 j2 j3
  end.
Definition GeneralParametersMRDC_XDD_Diff__helper1 : (forall a : GeneralParametersMRDC_XDD_Diff__Type, GeneralParametersMRDC_XDD_Diff__cond a -> GeneralParametersMRDC_XDD_Diff__list_cond (GeneralParametersMRDC_XDD_Diff__F1 a)).
                     intros. destruct a. auto. Qed.
Definition GeneralParametersMRDC_XDD_Diff__helper2 : (forall a : GeneralParametersMRDC_XDD_Diff__Type, GeneralParametersMRDC_XDD_Diff__F2 (GeneralParametersMRDC_XDD_Diff__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition GeneralParametersMRDC_XDD_Diff__helper3 : (forall b : GeneralParametersMRDC_XDD_Diff__list_type, GeneralParametersMRDC_XDD_Diff__list_cond b -> GeneralParametersMRDC_XDD_Diff__cond (GeneralParametersMRDC_XDD_Diff__F2 b) /\ GeneralParametersMRDC_XDD_Diff__F1 (GeneralParametersMRDC_XDD_Diff__F2 b) = b).
                     intros. destruct b as [y y1]. unfold GeneralParametersMRDC_XDD_Diff__cond, GeneralParametersMRDC_XDD_Diff__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition GeneralParametersMRDC_XDD_Diff__Format : T_Format GeneralParametersMRDC_XDD_Diff__Type GeneralParametersMRDC_XDD_Diff__cond :=
 proj2_format GeneralParametersMRDC_XDD_Diff__cond GeneralParametersMRDC_XDD_Diff__list_format  GeneralParametersMRDC_XDD_Diff__F1 GeneralParametersMRDC_XDD_Diff__F2 GeneralParametersMRDC_XDD_Diff__helper1 GeneralParametersMRDC_XDD_Diff__helper2 GeneralParametersMRDC_XDD_Diff__helper3.

Opaque GeneralParametersMRDC_XDD_Diff__cond GeneralParametersMRDC_XDD_Diff__Format.

