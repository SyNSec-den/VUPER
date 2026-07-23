Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Inductive ReportCGI__ext0O__useAutonomousGaps_r16__Type : Set :=
 | ReportCGI__ext0O__useAutonomousGaps_r16__setup
.
Definition ReportCGI__ext0O__useAutonomousGaps_r16__cond := (fun (_ : ReportCGI__ext0O__useAutonomousGaps_r16__Type) => True).
Lemma ReportCGI__ext0O__useAutonomousGaps_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ReportCGI__ext0O__useAutonomousGaps_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 ReportCGI__ext0O__useAutonomousGaps_r16__nat__helper.

Definition ReportCGI__ext0O__useAutonomousGaps_r16__F1 t :=
  match t with
  | ReportCGI__ext0O__useAutonomousGaps_r16__setup => 0
  end.
Definition ReportCGI__ext0O__useAutonomousGaps_r16__F2 n :=
  match n with
  | 0 => ReportCGI__ext0O__useAutonomousGaps_r16__setup
  | _ => ReportCGI__ext0O__useAutonomousGaps_r16__setup
  end.
Lemma ReportCGI__ext0O__useAutonomousGaps_r16__F1F2 : forall x : ReportCGI__ext0O__useAutonomousGaps_r16__Type, (ReportCGI__ext0O__useAutonomousGaps_r16__F1 x <= 0) /\ ReportCGI__ext0O__useAutonomousGaps_r16__F2 (ReportCGI__ext0O__useAutonomousGaps_r16__F1 x) = x. imp_solve. Qed.
Lemma ReportCGI__ext0O__useAutonomousGaps_r16__F2F1 : forall (y : nat) (H : y <= 0), ReportCGI__ext0O__useAutonomousGaps_r16__F1 (ReportCGI__ext0O__useAutonomousGaps_r16__F2 y) = y. enum_solve H y. Qed.

Record ReportCGI__ext0O__Type : Set :=
  make__ReportCGI__ext0O__Type {
    ReportCGI__ext0O__useAutonomousGaps_r16 : option ReportCGI__ext0O__useAutonomousGaps_r16__Type ;
}.
Definition ReportCGI__ext0O__list := (
 Opt ReportCGI__ext0O__useAutonomousGaps_r16__Type ReportCGI__ext0O__useAutonomousGaps_r16__cond ::
 nil).
Definition ReportCGI__ext0O__cond z := 
  opt_cond ReportCGI__ext0O__useAutonomousGaps_r16__cond (ReportCGI__ext0O__useAutonomousGaps_r16 z) /\
  True.

Definition ReportCGI__ext0__Type := ReportCGI__ext0O__Type.
Definition ReportCGI__ext0__cond := ReportCGI__ext0O__cond.

Record ReportCGI__Type : Set :=
  make__ReportCGI__Type {
    ReportCGI__cellForWhichToReportCGI : PhysCellId__Type ;
    ReportCGI__ext0 : option ReportCGI__ext0__Type ;
}.
Definition ReportCGI__root_list : list seq_elem := (
 Nor PhysCellId__Type PhysCellId__cond ::
 nil).
Definition ReportCGI__ext_list : list typ := (
  typ_cons ReportCGI__ext0__Type ReportCGI__ext0__cond ::
  nil).
Definition ReportCGI__cond (z : ReportCGI__Type) := 
(  PhysCellId__cond (ReportCGI__cellForWhichToReportCGI z) /\
  True) /\ 
(  opt_cond ReportCGI__ext0__cond (ReportCGI__ext0 z) /\
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
Definition ReportCGI__ext0O__useAutonomousGaps_r16__Format : T_Format ReportCGI__ext0O__useAutonomousGaps_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ReportCGI__ext0O__useAutonomousGaps_r16__nat__Format ReportCGI__ext0O__useAutonomousGaps_r16__F1 ReportCGI__ext0O__useAutonomousGaps_r16__F2 ReportCGI__ext0O__useAutonomousGaps_r16__F1F2 ReportCGI__ext0O__useAutonomousGaps_r16__F2F1.

Opaque ReportCGI__ext0O__useAutonomousGaps_r16__cond ReportCGI__ext0O__useAutonomousGaps_r16__Format.


Definition ReportCGI__ext0O__Format_Type := Eval cbn in seq_format_prod ReportCGI__ext0O__list.
Definition ReportCGI__ext0O__Format_list : ReportCGI__ext0O__Format_Type :=
  (ReportCGI__ext0O__useAutonomousGaps_r16__Format, unit_format).
Definition ReportCGI__ext0O__list__Format := (*Eval compute in *) seq_format ReportCGI__ext0O__list ReportCGI__ext0O__Format_list.
Definition ReportCGI__ext0O__F1 z :=
  (ReportCGI__ext0O__useAutonomousGaps_r16 z, tt).
Definition ReportCGI__ext0O__F2 (y : seq_type ReportCGI__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__ReportCGI__ext0O__Type i0
  end.
Lemma ReportCGI__ext0O__F1F2_cond (z : ReportCGI__ext0O__Type)
  : ReportCGI__ext0O__cond z ->
  (seq_cond ReportCGI__ext0O__list (ReportCGI__ext0O__F1 z)).
intro H. unfold ReportCGI__ext0O__cond in H. simpl. auto. Qed.
Lemma ReportCGI__ext0O__F1F2_cond2 (z : ReportCGI__ext0O__Type)
 : ReportCGI__ext0O__F2 (ReportCGI__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ReportCGI__ext0O__F2F1_cond (y : seq_type ReportCGI__ext0O__list)
  : seq_cond ReportCGI__ext0O__list y ->
 (ReportCGI__ext0O__cond (ReportCGI__ext0O__F2 y)) /\  ReportCGI__ext0O__F1 (ReportCGI__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ReportCGI__ext0O__cond. simpl in *. auto.
 - simpl. unfold ReportCGI__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ReportCGI__ext0O__Format : T_Format ReportCGI__ext0O__Type ReportCGI__ext0O__cond :=
        proj2_format  ReportCGI__ext0O__cond ReportCGI__ext0O__list__Format
    ReportCGI__ext0O__F1 ReportCGI__ext0O__F2 ReportCGI__ext0O__F1F2_cond  ReportCGI__ext0O__F1F2_cond2 ReportCGI__ext0O__F2F1_cond.
Opaque ReportCGI__ext0O__cond ReportCGI__ext0O__Format.

Definition ReportCGI__ext0__check_all_none (b : ReportCGI__ext0O__Type) : bool :=
match b with 
  | make__ReportCGI__ext0O__Type None  => false 
  | _ => true 
 end.
Definition ReportCGI__ext0__Format : T_Format ReportCGI__ext0__Type ReportCGI__ext0__cond :=
  restrict_add_format ReportCGI__ext0__check_all_none ReportCGI__ext0O__Format.

Opaque ReportCGI__ext0__cond ReportCGI__ext0__Format.


Definition ReportCGI__root_Format_Type := Eval cbn in seq_format_prod ReportCGI__root_list.
Definition ReportCGI__root_Format_list : ReportCGI__root_Format_Type :=
  (PhysCellId__Format, unit_format).

Definition ReportCGI__ext_Format_Type := Eval cbn in get_formats ReportCGI__ext_list.
Definition ReportCGI__ext_Format_list : ReportCGI__ext_Format_Type :=
  (ReportCGI__ext0__Format, unit__Format).

Definition ReportCGI__list_type : Set := (seq_type ReportCGI__root_list) * (seq_ext_type ReportCGI__ext_list).
Definition ReportCGI__list_cond (z : ReportCGI__list_type) : Prop :=
        (seq_cond ReportCGI__root_list (fst z)) /\ (seq_ext_cond ReportCGI__ext_list (snd z)).
Definition ReportCGI__list_format : T_Format ReportCGI__list_type ReportCGI__list_cond :=
 (* Eval compute in *) seq_ext_format ReportCGI__root_list ReportCGI__root_Format_list ReportCGI__ext_list ReportCGI__ext_Format_list.

Opaque ReportCGI__list_format.
Definition ReportCGI__F1 (z : ReportCGI__Type) : ReportCGI__list_type :=
  (((ReportCGI__cellForWhichToReportCGI z, tt)), (
(ReportCGI__ext0 z, tt))).
Definition ReportCGI__F2 (y : ReportCGI__list_type) : ReportCGI__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__ReportCGI__Type j0 i0
  end.
Definition ReportCGI__helper1 : (forall a : ReportCGI__Type, ReportCGI__cond a -> ReportCGI__list_cond (ReportCGI__F1 a)).
                     intros. destruct a. auto. Qed.
Definition ReportCGI__helper2 : (forall a : ReportCGI__Type, ReportCGI__F2 (ReportCGI__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition ReportCGI__helper3 : (forall b : ReportCGI__list_type, ReportCGI__list_cond b -> ReportCGI__cond (ReportCGI__F2 b) /\ ReportCGI__F1 (ReportCGI__F2 b) = b).
                     intros. destruct b as [y y1]. unfold ReportCGI__cond, ReportCGI__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition ReportCGI__Format : T_Format ReportCGI__Type ReportCGI__cond :=
 proj2_format ReportCGI__cond ReportCGI__list_format  ReportCGI__F1 ReportCGI__F2 ReportCGI__helper1 ReportCGI__helper2 ReportCGI__helper3.

Opaque ReportCGI__cond ReportCGI__Format.

