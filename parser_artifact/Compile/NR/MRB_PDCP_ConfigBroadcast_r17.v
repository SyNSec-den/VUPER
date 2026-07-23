Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Type : Set :=
 | MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__len12bits
.
Definition MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__cond := (fun (_ : MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Type) => True).
Lemma MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__nat__helper.

Definition MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F1 t :=
  match t with
  | MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__len12bits => 0
  end.
Definition MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F2 n :=
  match n with
  | 0 => MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__len12bits
  | _ => MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__len12bits
  end.
Lemma MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F1F2 : forall x : MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Type, (MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F1 x <= 0) /\ MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F2 (MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F1 x) = x. imp_solve. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F2F1 : forall (y : nat) (H : y <= 0), MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F1 (MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F2 y) = y. enum_solve H y. Qed.

Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__Type := Z.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond := (fun z => (1 <= z <= 16)%Z).
Transparent MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__dft_helper : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond 15. unfold MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond. lia. Qed.
Opaque MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond.
Record MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Type : Set :=
  make__MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Type {
    MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0000_r17 : bool ;
    MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0001_r17 : bool ;
    MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0002_r17 : bool ;
}.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list := (
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 nil).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond z := 
  (fun _ => True) (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0000_r17 z) /\
  (fun _ => True) (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0001_r17 z) /\
  (fun _ => True) (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0002_r17 z) /\
  True.

Record MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type : Set :=
  make__MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type {
    MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17 : Z ;
    MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17 : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Type ;
}.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list := (
 Dft Z MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond 15%Z MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__dft_helper Z.eq_dec ::
 Nor MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond ::
 nil).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond z := 
  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17 z) /\
  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17 z) /\
  True.


Inductive MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type : Set :=
  | MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__notUsed : unit -> MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type
  | MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type -> MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type
.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond ::
 nil).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__cond (c : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type) := 
  match c with
  | MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__notUsed t => (fun _ => True) t 
  | MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc t => MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond t 
  end.

Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__len_helper1 : to_bit_sz (length MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__len_helper2 : 2 <= length2 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list.
 simpl. lia. Qed.
Inductive MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Type : Set :=
 | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1
 | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms10
 | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms40
 | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms160
 | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms500
 | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1000
 | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1250
 | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms2750
.
Definition MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__cond := (fun (_ : MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Type) => True).
Lemma MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__nat__helper.

Definition MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F1 t :=
  match t with
  | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1 => 0
  | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms10 => 1
  | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms40 => 2
  | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms160 => 3
  | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms500 => 4
  | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1000 => 5
  | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1250 => 6
  | MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms2750 => 7
  end.
Definition MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F2 n :=
  match n with
  | 0 => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1
  | 1 => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms10
  | 2 => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms40
  | 3 => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms160
  | 4 => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms500
  | 5 => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1000
  | 6 => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1250
  | 7 => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms2750
  | _ => MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__ms1
  end.
Lemma MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F1F2 : forall x : MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Type, (MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F1 x <= 7) /\ MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F2 (MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F1 x) = x. imp_solve. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F2F1 : forall (y : nat) (H : y <= 7), MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F1 (MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F2 y) = y. enum_solve H y. Qed.

Record MRB_PDCP_ConfigBroadcast_r17__Type : Set :=
  make__MRB_PDCP_ConfigBroadcast_r17__Type {
    MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17 : option MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Type ;
    MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17 : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type ;
    MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17 : option MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Type ;
}.
Definition MRB_PDCP_ConfigBroadcast_r17__list := (
 Opt MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Type MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__cond ::
 Nor MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__cond ::
 Opt MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Type MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__cond ::
 nil).
Definition MRB_PDCP_ConfigBroadcast_r17__cond z := 
  opt_cond MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__cond (MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17 z) /\
  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__cond (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17 z) /\
  opt_cond MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__cond (MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17 z) /\
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
Definition MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Format : T_Format MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__nat__Format MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F1 MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F2 MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F1F2 MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__F2F1.

Opaque MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__cond MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Format.

Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__Format : T_Format Z MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond :=
 ranged_int_format (1) (16) MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__helper1 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__helper2.

Opaque MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__Format.


Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Format_Type := Eval cbn in seq_format_prod MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Format_list : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Format_Type :=
  (bool__Format, (bool__Format, (bool__Format, unit_format))).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list__Format := (*Eval compute in *) seq_format MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Format_list.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1 z :=
  (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0000_r17 z, (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0001_r17 z, (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__profile0x0002_r17 z, tt))).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F2 (y : seq_type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Type i0 i1 i2
  end.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1F2_cond (z : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Type)
  : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond z ->
  (seq_cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1 z)).
intro H. unfold MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond in H. simpl. auto. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1F2_cond2 (z : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Type)
 : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F2 (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F2F1_cond (y : seq_type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list)
  : seq_cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list y ->
 (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F2 y)) /\  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1 (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond. simpl in *. auto.
 - simpl. unfold MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Format : T_Format MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond :=
        proj2_format  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__list__Format
    MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F2 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1F2_cond  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F1F2_cond2 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__F2F1_cond.
Opaque MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Format.


Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Format_Type := Eval cbn in seq_format_prod MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Format_list : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Format_Type :=
  (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17__Format, (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17__Format, unit_format)).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list__Format := (*Eval compute in *) seq_format MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Format_list.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1 z :=
  (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__maxCID_r17 z, (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__profiles_r17 z, tt)).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F2 (y : seq_type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list) :=
  match y with
  | (i0, (i1, _))=>
    make__MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type i0 i1
  end.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1F2_cond (z : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type)
  : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond z ->
  (seq_cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1 z)).
intro H. unfold MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond in H. simpl. auto. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1F2_cond2 (z : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type)
 : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F2 (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F2F1_cond (y : seq_type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list)
  : seq_cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list y ->
 (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F2 y)) /\  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1 (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond. simpl in *. auto.
 - simpl. unfold MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Format : T_Format MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond :=
        proj2_format  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__list__Format
    MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F2 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1F2_cond  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F1F2_cond2 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__F2F1_cond.
Opaque MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Format.


Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Format_Type := Eval cbn in get_formats MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Format_list : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Format_Type :=
  (unit__Format, (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Format, unit__Format)).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list__Format := Eval compute in choice_format MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__len_helper1 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__len_helper2  MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Format_list.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F1 (z : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type) : (choice MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list) :=
  match z with
   | MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__notUsed t => existT _ 0 t
  | MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc t => existT _ 1 t
  end.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__g := (fun n => typ_set (get_nth_typ MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list n)).
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F2 (y : choice MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list) : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__g n -> MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type) with
    | 0 => fun (t : unit) => MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__notUsed t 
    | 1 => fun (t : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc__Type) => MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__rohc t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type with end) n0
           end t0).

Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__helper2 :  forall (y : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type), MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__cond y -> choice_cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__helper3 :  forall (y : MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type), MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F2 (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__helper4 : (forall b : choice MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list, choice_cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list b -> MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__cond (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F2 b) /\ MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F1 (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F1 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F2.
Definition MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Format : T_Format MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Type MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__cond :=
  (* Eval compute in *) proj2_format MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__list__Format MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F1 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__F2 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__helper2 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__helper3 MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__helper4.
Opaque MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__cond MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Format.

Definition MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Format : T_Format MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__nat__Format MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F1 MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F2 MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F1F2 MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__F2F1.

Opaque MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__cond MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Format.


Definition MRB_PDCP_ConfigBroadcast_r17__Format_Type := Eval cbn in seq_format_prod MRB_PDCP_ConfigBroadcast_r17__list.
Definition MRB_PDCP_ConfigBroadcast_r17__Format_list : MRB_PDCP_ConfigBroadcast_r17__Format_Type :=
  (MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17__Format, (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17__Format, (MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17__Format, unit_format))).
Definition MRB_PDCP_ConfigBroadcast_r17__list__Format := (*Eval compute in *) seq_format MRB_PDCP_ConfigBroadcast_r17__list MRB_PDCP_ConfigBroadcast_r17__Format_list.
Definition MRB_PDCP_ConfigBroadcast_r17__F1 z :=
  (MRB_PDCP_ConfigBroadcast_r17__pdcp_SN_SizeDL_r17 z, (MRB_PDCP_ConfigBroadcast_r17__headerCompression_r17 z, (MRB_PDCP_ConfigBroadcast_r17__t_Reordering_r17 z, tt))).
Definition MRB_PDCP_ConfigBroadcast_r17__F2 (y : seq_type MRB_PDCP_ConfigBroadcast_r17__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__MRB_PDCP_ConfigBroadcast_r17__Type i0 i1 i2
  end.
Lemma MRB_PDCP_ConfigBroadcast_r17__F1F2_cond (z : MRB_PDCP_ConfigBroadcast_r17__Type)
  : MRB_PDCP_ConfigBroadcast_r17__cond z ->
  (seq_cond MRB_PDCP_ConfigBroadcast_r17__list (MRB_PDCP_ConfigBroadcast_r17__F1 z)).
intro H. unfold MRB_PDCP_ConfigBroadcast_r17__cond in H. simpl. auto. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__F1F2_cond2 (z : MRB_PDCP_ConfigBroadcast_r17__Type)
 : MRB_PDCP_ConfigBroadcast_r17__F2 (MRB_PDCP_ConfigBroadcast_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MRB_PDCP_ConfigBroadcast_r17__F2F1_cond (y : seq_type MRB_PDCP_ConfigBroadcast_r17__list)
  : seq_cond MRB_PDCP_ConfigBroadcast_r17__list y ->
 (MRB_PDCP_ConfigBroadcast_r17__cond (MRB_PDCP_ConfigBroadcast_r17__F2 y)) /\  MRB_PDCP_ConfigBroadcast_r17__F1 (MRB_PDCP_ConfigBroadcast_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MRB_PDCP_ConfigBroadcast_r17__cond. simpl in *. auto.
 - simpl. unfold MRB_PDCP_ConfigBroadcast_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MRB_PDCP_ConfigBroadcast_r17__Format : T_Format MRB_PDCP_ConfigBroadcast_r17__Type MRB_PDCP_ConfigBroadcast_r17__cond :=
        proj2_format  MRB_PDCP_ConfigBroadcast_r17__cond MRB_PDCP_ConfigBroadcast_r17__list__Format
    MRB_PDCP_ConfigBroadcast_r17__F1 MRB_PDCP_ConfigBroadcast_r17__F2 MRB_PDCP_ConfigBroadcast_r17__F1F2_cond  MRB_PDCP_ConfigBroadcast_r17__F1F2_cond2 MRB_PDCP_ConfigBroadcast_r17__F2F1_cond.
Opaque MRB_PDCP_ConfigBroadcast_r17__cond MRB_PDCP_ConfigBroadcast_r17__Format.

