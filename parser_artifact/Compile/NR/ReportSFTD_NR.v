Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Type : Set :=
 | ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__true
.
Definition ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__cond := (fun (_ : ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Type) => True).
Lemma ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__nat__helper.

Definition ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F1 t :=
  match t with
  | ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__true => 0
  end.
Definition ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F2 n :=
  match n with
  | 0 => ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__true
  | _ => ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__true
  end.
Lemma ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F1F2 : forall x : ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Type, (ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F1 x <= 0) /\ ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F2 (ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F1 x) = x. imp_solve. Qed.
Lemma ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F2F1 : forall (y : nat) (H : y <= 0), ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F1 (ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F2 y) = y. enum_solve H y. Qed.

Inductive ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Type : Set :=
 | ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__true
.
Definition ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__cond := (fun (_ : ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Type) => True).
Lemma ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__nat__helper.

Definition ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F1 t :=
  match t with
  | ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__true => 0
  end.
Definition ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F2 n :=
  match n with
  | 0 => ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__true
  | _ => ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__true
  end.
Lemma ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F1F2 : forall x : ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Type, (ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F1 x <= 0) /\ ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F2 (ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F1 x) = x. imp_solve. Qed.
Lemma ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F2F1 : forall (y : nat) (H : y <= 0), ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F1 (ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Definition ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__Type := list PhysCellId__Type.

Lemma ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__helper1 : (0 <= 1 <= maxCellSFTD)%Z. unfold maxCellSFTD.
 lia. Qed.
Lemma ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__helper2 : to_bit_sz (Z.to_nat (maxCellSFTD - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxCellSFTD - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__cond (z : ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__Type) :=  (1 <= Z.of_nat (length z) <= maxCellSFTD)%Z /\ (list_and PhysCellId__cond z) .

Record ReportSFTD_NR__ext0O__Type : Set :=
  make__ReportSFTD_NR__ext0O__Type {
    ReportSFTD_NR__ext0O__reportSFTD_NeighMeas : option ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Type ;
    ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas : option ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Type ;
    ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD : option ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__Type ;
}.
Definition ReportSFTD_NR__ext0O__list := (
 Opt ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Type ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__cond ::
 Opt ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Type ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__cond ::
 Opt ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__Type ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__cond ::
 nil).
Definition ReportSFTD_NR__ext0O__cond z := 
  opt_cond ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__cond (ReportSFTD_NR__ext0O__reportSFTD_NeighMeas z) /\
  opt_cond ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__cond (ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas z) /\
  opt_cond ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__cond (ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD z) /\
  True.

Definition ReportSFTD_NR__ext0__Type := ReportSFTD_NR__ext0O__Type.
Definition ReportSFTD_NR__ext0__cond := ReportSFTD_NR__ext0O__cond.

Record ReportSFTD_NR__Type : Set :=
  make__ReportSFTD_NR__Type {
    ReportSFTD_NR__reportSFTD_Meas : bool ;
    ReportSFTD_NR__reportRSRP : bool ;
    ReportSFTD_NR__ext0 : option ReportSFTD_NR__ext0__Type ;
}.
Definition ReportSFTD_NR__root_list : list seq_elem := (
 Nor bool (fun _ => True) ::
 Nor bool (fun _ => True) ::
 nil).
Definition ReportSFTD_NR__ext_list : list typ := (
  typ_cons ReportSFTD_NR__ext0__Type ReportSFTD_NR__ext0__cond ::
  nil).
Definition ReportSFTD_NR__cond (z : ReportSFTD_NR__Type) := 
(  (fun _ => True) (ReportSFTD_NR__reportSFTD_Meas z) /\
  (fun _ => True) (ReportSFTD_NR__reportRSRP z) /\
  True) /\ 
(  opt_cond ReportSFTD_NR__ext0__cond (ReportSFTD_NR__ext0 z) /\
  True).


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
Definition ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Format : T_Format ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__nat__Format ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F1 ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F2 ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F1F2 ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__F2F1.

Opaque ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__cond ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Format.

Definition ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Format : T_Format ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__nat__Format ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F1 ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F2 ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F1F2 ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__F2F1.

Opaque ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__cond ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Format.

Definition ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__Format : T_Format ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__Type ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__cond := seq_of_format PhysCellId__Format 1 maxCellSFTD ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__helper1 ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__helper2.

Opaque ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__cond ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__Format.


Definition ReportSFTD_NR__ext0O__Format_Type := Eval cbn in seq_format_prod ReportSFTD_NR__ext0O__list.
Definition ReportSFTD_NR__ext0O__Format_list : ReportSFTD_NR__ext0O__Format_Type :=
  (ReportSFTD_NR__ext0O__reportSFTD_NeighMeas__Format, (ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas__Format, (ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD__Format, unit_format))).
Definition ReportSFTD_NR__ext0O__list__Format := (*Eval compute in *) seq_format ReportSFTD_NR__ext0O__list ReportSFTD_NR__ext0O__Format_list.
Definition ReportSFTD_NR__ext0O__F1 z :=
  (ReportSFTD_NR__ext0O__reportSFTD_NeighMeas z, (ReportSFTD_NR__ext0O__drx_SFTD_NeighMeas z, (ReportSFTD_NR__ext0O__cellsForWhichToReportSFTD z, tt))).
Definition ReportSFTD_NR__ext0O__F2 (y : seq_type ReportSFTD_NR__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__ReportSFTD_NR__ext0O__Type i0 i1 i2
  end.
Lemma ReportSFTD_NR__ext0O__F1F2_cond (z : ReportSFTD_NR__ext0O__Type)
  : ReportSFTD_NR__ext0O__cond z ->
  (seq_cond ReportSFTD_NR__ext0O__list (ReportSFTD_NR__ext0O__F1 z)).
intro H. unfold ReportSFTD_NR__ext0O__cond in H. simpl. auto. Qed.
Lemma ReportSFTD_NR__ext0O__F1F2_cond2 (z : ReportSFTD_NR__ext0O__Type)
 : ReportSFTD_NR__ext0O__F2 (ReportSFTD_NR__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReportSFTD_NR__ext0O__F2F1_cond (y : seq_type ReportSFTD_NR__ext0O__list)
  : seq_cond ReportSFTD_NR__ext0O__list y ->
 (ReportSFTD_NR__ext0O__cond (ReportSFTD_NR__ext0O__F2 y)) /\  ReportSFTD_NR__ext0O__F1 (ReportSFTD_NR__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReportSFTD_NR__ext0O__cond. simpl in *. auto.
 - simpl. unfold ReportSFTD_NR__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReportSFTD_NR__ext0O__Format : T_Format ReportSFTD_NR__ext0O__Type ReportSFTD_NR__ext0O__cond :=
        proj2_format  ReportSFTD_NR__ext0O__cond ReportSFTD_NR__ext0O__list__Format
    ReportSFTD_NR__ext0O__F1 ReportSFTD_NR__ext0O__F2 ReportSFTD_NR__ext0O__F1F2_cond  ReportSFTD_NR__ext0O__F1F2_cond2 ReportSFTD_NR__ext0O__F2F1_cond.
Opaque ReportSFTD_NR__ext0O__cond ReportSFTD_NR__ext0O__Format.

Definition ReportSFTD_NR__ext0__check_all_none (b : ReportSFTD_NR__ext0O__Type) : bool :=
match b with 
  | make__ReportSFTD_NR__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition ReportSFTD_NR__ext0__Format : T_Format ReportSFTD_NR__ext0__Type ReportSFTD_NR__ext0__cond :=
  restrict_add_format ReportSFTD_NR__ext0__check_all_none ReportSFTD_NR__ext0O__Format.

Opaque ReportSFTD_NR__ext0__cond ReportSFTD_NR__ext0__Format.


Definition ReportSFTD_NR__root_Format_Type := Eval cbn in seq_format_prod ReportSFTD_NR__root_list.
Definition ReportSFTD_NR__root_Format_list : ReportSFTD_NR__root_Format_Type :=
  (bool__Format, (bool__Format, unit_format)).

Definition ReportSFTD_NR__ext_Format_Type := Eval cbn in get_formats ReportSFTD_NR__ext_list.
Definition ReportSFTD_NR__ext_Format_list : ReportSFTD_NR__ext_Format_Type :=
  (ReportSFTD_NR__ext0__Format, unit__Format).

Definition ReportSFTD_NR__list_type : Set := (seq_type ReportSFTD_NR__root_list) * (seq_ext_type ReportSFTD_NR__ext_list).
Definition ReportSFTD_NR__list_cond (z : ReportSFTD_NR__list_type) : Prop :=
        (seq_cond ReportSFTD_NR__root_list (fst z)) /\ (seq_ext_cond ReportSFTD_NR__ext_list (snd z)).
Definition ReportSFTD_NR__list_format : T_Format ReportSFTD_NR__list_type ReportSFTD_NR__list_cond :=
 (* Eval compute in *) seq_ext_format ReportSFTD_NR__root_list ReportSFTD_NR__root_Format_list ReportSFTD_NR__ext_list ReportSFTD_NR__ext_Format_list.

Opaque ReportSFTD_NR__list_format.
Definition ReportSFTD_NR__F1 (z : ReportSFTD_NR__Type) : ReportSFTD_NR__list_type :=
  (((ReportSFTD_NR__reportSFTD_Meas z, (ReportSFTD_NR__reportRSRP z, tt))), (
(ReportSFTD_NR__ext0 z, tt))).
Definition ReportSFTD_NR__F2 (y : ReportSFTD_NR__list_type) : ReportSFTD_NR__Type :=
  match y with
  | ((j0, (j1, _)), (i0, _))=>
    make__ReportSFTD_NR__Type j0 j1 i0
  end.
Definition ReportSFTD_NR__helper1 : (forall a : ReportSFTD_NR__Type, ReportSFTD_NR__cond a -> ReportSFTD_NR__list_cond (ReportSFTD_NR__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ReportSFTD_NR__helper2 : (forall a : ReportSFTD_NR__Type, ReportSFTD_NR__F2 (ReportSFTD_NR__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ReportSFTD_NR__helper3 : (forall b : ReportSFTD_NR__list_type, ReportSFTD_NR__list_cond b -> ReportSFTD_NR__cond (ReportSFTD_NR__F2 b) /\ ReportSFTD_NR__F1 (ReportSFTD_NR__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ReportSFTD_NR__cond, ReportSFTD_NR__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ReportSFTD_NR__Format : T_Format ReportSFTD_NR__Type ReportSFTD_NR__cond :=
 proj2_format ReportSFTD_NR__cond ReportSFTD_NR__list_format  ReportSFTD_NR__F1 ReportSFTD_NR__F2 ReportSFTD_NR__helper1 ReportSFTD_NR__helper2 ReportSFTD_NR__helper3.

Opaque ReportSFTD_NR__cond ReportSFTD_NR__Format.

