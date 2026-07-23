Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.NZP_CSI_RS_ResourceId.

Opaque NZP_CSI_RS_ResourceId__cond NZP_CSI_RS_ResourceId__Format.

Require Import NR.CSI_RS_ResourceMapping.

Opaque CSI_RS_ResourceMapping__cond CSI_RS_ResourceMapping__Format.

Lemma NZP_CSI_RS_Resource__powerControlOffset__helper1 : (-8 <= 15)%Z.  lia. Qed.
Lemma NZP_CSI_RS_Resource__powerControlOffset__helper2 : to_bit_sz (Z.to_nat (15 - -8)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - -8))%Z). { apply Zorder.Zle_minus_le_0. apply NZP_CSI_RS_Resource__powerControlOffset__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NZP_CSI_RS_Resource__powerControlOffset__Type := Z.
Definition NZP_CSI_RS_Resource__powerControlOffset__cond := (fun z => (-8 <= z <= 15)%Z).
Inductive NZP_CSI_RS_Resource__powerControlOffsetSS__Type : Set :=
 | NZP_CSI_RS_Resource__powerControlOffsetSS__db_3
 | NZP_CSI_RS_Resource__powerControlOffsetSS__db0
 | NZP_CSI_RS_Resource__powerControlOffsetSS__db3
 | NZP_CSI_RS_Resource__powerControlOffsetSS__db6
.
Definition NZP_CSI_RS_Resource__powerControlOffsetSS__cond := (fun (_ : NZP_CSI_RS_Resource__powerControlOffsetSS__Type) => True).
Lemma NZP_CSI_RS_Resource__powerControlOffsetSS__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NZP_CSI_RS_Resource__powerControlOffsetSS__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 NZP_CSI_RS_Resource__powerControlOffsetSS__nat__helper.

Definition NZP_CSI_RS_Resource__powerControlOffsetSS__F1 t :=
  match t with
  | NZP_CSI_RS_Resource__powerControlOffsetSS__db_3 => 0
  | NZP_CSI_RS_Resource__powerControlOffsetSS__db0 => 1
  | NZP_CSI_RS_Resource__powerControlOffsetSS__db3 => 2
  | NZP_CSI_RS_Resource__powerControlOffsetSS__db6 => 3
  end.
Definition NZP_CSI_RS_Resource__powerControlOffsetSS__F2 n :=
  match n with
  | 0 => NZP_CSI_RS_Resource__powerControlOffsetSS__db_3
  | 1 => NZP_CSI_RS_Resource__powerControlOffsetSS__db0
  | 2 => NZP_CSI_RS_Resource__powerControlOffsetSS__db3
  | 3 => NZP_CSI_RS_Resource__powerControlOffsetSS__db6
  | _ => NZP_CSI_RS_Resource__powerControlOffsetSS__db_3
  end.
Lemma NZP_CSI_RS_Resource__powerControlOffsetSS__F1F2 : forall x : NZP_CSI_RS_Resource__powerControlOffsetSS__Type, (NZP_CSI_RS_Resource__powerControlOffsetSS__F1 x <= 3) /\ NZP_CSI_RS_Resource__powerControlOffsetSS__F2 (NZP_CSI_RS_Resource__powerControlOffsetSS__F1 x) = x. imp_solve. Qed.
Lemma NZP_CSI_RS_Resource__powerControlOffsetSS__F2F1 : forall (y : nat) (H : y <= 3), NZP_CSI_RS_Resource__powerControlOffsetSS__F1 (NZP_CSI_RS_Resource__powerControlOffsetSS__F2 y) = y. enum_solve H y. Qed.

Require Import NR.ScramblingId.

Opaque ScramblingId__cond ScramblingId__Format.

Require Import NR.CSI_ResourcePeriodicityAndOffset.

Opaque CSI_ResourcePeriodicityAndOffset__cond CSI_ResourcePeriodicityAndOffset__Format.

Require Import NR.TCI_StateId.

Opaque TCI_StateId__cond TCI_StateId__Format.

Record NZP_CSI_RS_Resource__Type : Set :=
  make__NZP_CSI_RS_Resource__Type {
    NZP_CSI_RS_Resource__nzp_CSI_RS_ResourceId : NZP_CSI_RS_ResourceId__Type ;
    NZP_CSI_RS_Resource__resourceMapping : CSI_RS_ResourceMapping__Type ;
    NZP_CSI_RS_Resource__powerControlOffset : Z ;
    NZP_CSI_RS_Resource__powerControlOffsetSS : option NZP_CSI_RS_Resource__powerControlOffsetSS__Type ;
    NZP_CSI_RS_Resource__scramblingID : ScramblingId__Type ;
    NZP_CSI_RS_Resource__periodicityAndOffset : option CSI_ResourcePeriodicityAndOffset__Type ;
    NZP_CSI_RS_Resource__qcl_InfoPeriodicCSI_RS : option TCI_StateId__Type ;
}.
Definition NZP_CSI_RS_Resource__root_list : list seq_elem := (
 Nor NZP_CSI_RS_ResourceId__Type NZP_CSI_RS_ResourceId__cond ::
 Nor CSI_RS_ResourceMapping__Type CSI_RS_ResourceMapping__cond ::
 Nor Z NZP_CSI_RS_Resource__powerControlOffset__cond ::
 Opt NZP_CSI_RS_Resource__powerControlOffsetSS__Type NZP_CSI_RS_Resource__powerControlOffsetSS__cond ::
 Nor ScramblingId__Type ScramblingId__cond ::
 Opt CSI_ResourcePeriodicityAndOffset__Type CSI_ResourcePeriodicityAndOffset__cond ::
 Opt TCI_StateId__Type TCI_StateId__cond ::
 nil).
Definition NZP_CSI_RS_Resource__ext_list : list typ := (
  nil).
Definition NZP_CSI_RS_Resource__cond (z : NZP_CSI_RS_Resource__Type) := 
(  NZP_CSI_RS_ResourceId__cond (NZP_CSI_RS_Resource__nzp_CSI_RS_ResourceId z) /\
  CSI_RS_ResourceMapping__cond (NZP_CSI_RS_Resource__resourceMapping z) /\
  NZP_CSI_RS_Resource__powerControlOffset__cond (NZP_CSI_RS_Resource__powerControlOffset z) /\
  opt_cond NZP_CSI_RS_Resource__powerControlOffsetSS__cond (NZP_CSI_RS_Resource__powerControlOffsetSS z) /\
  ScramblingId__cond (NZP_CSI_RS_Resource__scramblingID z) /\
  opt_cond CSI_ResourcePeriodicityAndOffset__cond (NZP_CSI_RS_Resource__periodicityAndOffset z) /\
  opt_cond TCI_StateId__cond (NZP_CSI_RS_Resource__qcl_InfoPeriodicCSI_RS z) /\
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
Definition NZP_CSI_RS_Resource__powerControlOffset__Format : T_Format Z NZP_CSI_RS_Resource__powerControlOffset__cond :=
 ranged_int_format (-8) (15) NZP_CSI_RS_Resource__powerControlOffset__helper1 NZP_CSI_RS_Resource__powerControlOffset__helper2.

Opaque NZP_CSI_RS_Resource__powerControlOffset__cond NZP_CSI_RS_Resource__powerControlOffset__Format.

Definition NZP_CSI_RS_Resource__powerControlOffsetSS__Format : T_Format NZP_CSI_RS_Resource__powerControlOffsetSS__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NZP_CSI_RS_Resource__powerControlOffsetSS__nat__Format NZP_CSI_RS_Resource__powerControlOffsetSS__F1 NZP_CSI_RS_Resource__powerControlOffsetSS__F2 NZP_CSI_RS_Resource__powerControlOffsetSS__F1F2 NZP_CSI_RS_Resource__powerControlOffsetSS__F2F1.

Opaque NZP_CSI_RS_Resource__powerControlOffsetSS__cond NZP_CSI_RS_Resource__powerControlOffsetSS__Format.


Definition NZP_CSI_RS_Resource__root_Format_Type := Eval cbn in seq_format_prod NZP_CSI_RS_Resource__root_list.
Definition NZP_CSI_RS_Resource__root_Format_list : NZP_CSI_RS_Resource__root_Format_Type :=
  (NZP_CSI_RS_ResourceId__Format, (CSI_RS_ResourceMapping__Format, (NZP_CSI_RS_Resource__powerControlOffset__Format, (NZP_CSI_RS_Resource__powerControlOffsetSS__Format, (ScramblingId__Format, (CSI_ResourcePeriodicityAndOffset__Format, (TCI_StateId__Format, unit_format))))))).

Definition NZP_CSI_RS_Resource__ext_Format_Type := Eval cbn in get_formats NZP_CSI_RS_Resource__ext_list.
Definition NZP_CSI_RS_Resource__ext_Format_list : NZP_CSI_RS_Resource__ext_Format_Type :=
  unit__Format.

Definition NZP_CSI_RS_Resource__list_type : Set := (seq_type NZP_CSI_RS_Resource__root_list) * (seq_ext_type NZP_CSI_RS_Resource__ext_list).
Definition NZP_CSI_RS_Resource__list_cond (z : NZP_CSI_RS_Resource__list_type) : Prop :=
        (seq_cond NZP_CSI_RS_Resource__root_list (fst z)) /\ (seq_ext_cond NZP_CSI_RS_Resource__ext_list (snd z)).
Definition NZP_CSI_RS_Resource__list_format : T_Format NZP_CSI_RS_Resource__list_type NZP_CSI_RS_Resource__list_cond :=
 (* Eval compute in *) seq_ext_format NZP_CSI_RS_Resource__root_list NZP_CSI_RS_Resource__root_Format_list NZP_CSI_RS_Resource__ext_list NZP_CSI_RS_Resource__ext_Format_list.

Opaque NZP_CSI_RS_Resource__list_format.
Definition NZP_CSI_RS_Resource__F1 (z : NZP_CSI_RS_Resource__Type) : NZP_CSI_RS_Resource__list_type :=
  (((NZP_CSI_RS_Resource__nzp_CSI_RS_ResourceId z, (NZP_CSI_RS_Resource__resourceMapping z, (NZP_CSI_RS_Resource__powerControlOffset z, (NZP_CSI_RS_Resource__powerControlOffsetSS z, (NZP_CSI_RS_Resource__scramblingID z, (NZP_CSI_RS_Resource__periodicityAndOffset z, (NZP_CSI_RS_Resource__qcl_InfoPeriodicCSI_RS z, tt)))))))), (
tt)).
Definition NZP_CSI_RS_Resource__F2 (y : NZP_CSI_RS_Resource__list_type) : NZP_CSI_RS_Resource__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, _))))))), _)=>
    make__NZP_CSI_RS_Resource__Type j0 j1 j2 j3 j4 j5 j6
  end.
Definition NZP_CSI_RS_Resource__helper1 : (forall a : NZP_CSI_RS_Resource__Type, NZP_CSI_RS_Resource__cond a -> NZP_CSI_RS_Resource__list_cond (NZP_CSI_RS_Resource__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NZP_CSI_RS_Resource__helper2 : (forall a : NZP_CSI_RS_Resource__Type, NZP_CSI_RS_Resource__F2 (NZP_CSI_RS_Resource__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NZP_CSI_RS_Resource__helper3 : (forall b : NZP_CSI_RS_Resource__list_type, NZP_CSI_RS_Resource__list_cond b -> NZP_CSI_RS_Resource__cond (NZP_CSI_RS_Resource__F2 b) /\ NZP_CSI_RS_Resource__F1 (NZP_CSI_RS_Resource__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NZP_CSI_RS_Resource__cond, NZP_CSI_RS_Resource__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NZP_CSI_RS_Resource__Format : T_Format NZP_CSI_RS_Resource__Type NZP_CSI_RS_Resource__cond :=
 proj2_format NZP_CSI_RS_Resource__cond NZP_CSI_RS_Resource__list_format  NZP_CSI_RS_Resource__F1 NZP_CSI_RS_Resource__F2 NZP_CSI_RS_Resource__helper1 NZP_CSI_RS_Resource__helper2 NZP_CSI_RS_Resource__helper3.

Opaque NZP_CSI_RS_Resource__cond NZP_CSI_RS_Resource__Format.

