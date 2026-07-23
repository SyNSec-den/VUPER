Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.DRB_Identity.

Opaque DRB_Identity__cond DRB_Identity__Format.

Definition ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__Type := list DRB_Identity__Type.

Lemma ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__helper1 : (0 <= 1 <= maxDRB)%Z. unfold maxDRB.
 lia. Qed.
Lemma ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__helper2 : to_bit_sz (Z.to_nat (maxDRB - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxDRB - 1))%Z). { apply Zorder.Zle_minus_le_0. apply ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__cond (z : ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__Type) :=  (1 <= Z.of_nat (length z) <= maxDRB)%Z /\ (list_and DRB_Identity__cond z) .

Inductive ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Type : Set :=
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms0dot25
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms0dot5
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms1
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms2
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms4
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms5
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms10
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms20
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms30
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms40
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms50
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms60
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms70
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms80
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms90
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms100
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms150
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms300
 | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms500
.
Definition ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__cond := (fun (_ : ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Type) => True).
Lemma ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__nat__helper : to_bit_sz 18 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__nat__Format : T_Format nat (fun z => (z <= 18)) :=
  nat_enum_format 18 ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__nat__helper.

Definition ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F1 t :=
  match t with
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms0dot25 => 0
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms0dot5 => 1
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms1 => 2
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms2 => 3
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms4 => 4
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms5 => 5
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms10 => 6
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms20 => 7
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms30 => 8
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms40 => 9
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms50 => 10
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms60 => 11
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms70 => 12
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms80 => 13
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms90 => 14
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms100 => 15
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms150 => 16
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms300 => 17
  | ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms500 => 18
  end.
Definition ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F2 n :=
  match n with
  | 0 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms0dot25
  | 1 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms0dot5
  | 2 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms1
  | 3 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms2
  | 4 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms4
  | 5 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms5
  | 6 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms10
  | 7 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms20
  | 8 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms30
  | 9 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms40
  | 10 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms50
  | 11 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms60
  | 12 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms70
  | 13 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms80
  | 14 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms90
  | 15 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms100
  | 16 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms150
  | 17 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms300
  | 18 => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms500
  | _ => ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__ms0dot25
  end.
Lemma ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F1F2 : forall x : ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Type, (ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F1 x <= 18) /\ ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F2 (ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F1 x) = x. imp_solve. Qed.
Lemma ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F2F1 : forall (y : nat) (H : y <= 18), ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F1 (ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F2 y) = y. enum_solve H y. Qed.

Record ExcessDelay_DRB_IdentityInfo_r17__Type : Set :=
  make__ExcessDelay_DRB_IdentityInfo_r17__Type {
    ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList : ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__Type ;
    ExcessDelay_DRB_IdentityInfo_r17__delayThreshold : ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Type ;
}.
Definition ExcessDelay_DRB_IdentityInfo_r17__list := (
 Nor ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__Type ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__cond ::
 Nor ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Type ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__cond ::
 nil).
Definition ExcessDelay_DRB_IdentityInfo_r17__cond z := 
  ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__cond (ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList z) /\
  ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__cond (ExcessDelay_DRB_IdentityInfo_r17__delayThreshold z) /\
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
Definition ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__Format : T_Format ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__Type ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__cond := seq_of_format DRB_Identity__Format 1 maxDRB ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__helper1 ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__helper2.

Opaque ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__cond ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__Format.

Definition ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Format : T_Format ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Type (fun _ => True) :=
(* Eval compute in *) proj3_format ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__nat__Format ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F1 ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F2 ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F1F2 ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__F2F1.

Opaque ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__cond ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Format.


Definition ExcessDelay_DRB_IdentityInfo_r17__Format_Type := Eval cbn in seq_format_prod ExcessDelay_DRB_IdentityInfo_r17__list.
Definition ExcessDelay_DRB_IdentityInfo_r17__Format_list : ExcessDelay_DRB_IdentityInfo_r17__Format_Type :=
  (ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList__Format, (ExcessDelay_DRB_IdentityInfo_r17__delayThreshold__Format, unit_format)).
Definition ExcessDelay_DRB_IdentityInfo_r17__list__Format := (*Eval compute in *) seq_format ExcessDelay_DRB_IdentityInfo_r17__list ExcessDelay_DRB_IdentityInfo_r17__Format_list.
Definition ExcessDelay_DRB_IdentityInfo_r17__F1 z :=
  (ExcessDelay_DRB_IdentityInfo_r17__drb_IdentityList z, (ExcessDelay_DRB_IdentityInfo_r17__delayThreshold z, tt)).
Definition ExcessDelay_DRB_IdentityInfo_r17__F2 (y : seq_type ExcessDelay_DRB_IdentityInfo_r17__list) :=
  match y with
  | (i0, (i1, _))=>
    make__ExcessDelay_DRB_IdentityInfo_r17__Type i0 i1
  end.
Lemma ExcessDelay_DRB_IdentityInfo_r17__F1F2_cond (z : ExcessDelay_DRB_IdentityInfo_r17__Type)
  : ExcessDelay_DRB_IdentityInfo_r17__cond z ->
  (seq_cond ExcessDelay_DRB_IdentityInfo_r17__list (ExcessDelay_DRB_IdentityInfo_r17__F1 z)).
intro H. unfold ExcessDelay_DRB_IdentityInfo_r17__cond in H. simpl. auto. Qed.
Lemma ExcessDelay_DRB_IdentityInfo_r17__F1F2_cond2 (z : ExcessDelay_DRB_IdentityInfo_r17__Type)
 : ExcessDelay_DRB_IdentityInfo_r17__F2 (ExcessDelay_DRB_IdentityInfo_r17__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma ExcessDelay_DRB_IdentityInfo_r17__F2F1_cond (y : seq_type ExcessDelay_DRB_IdentityInfo_r17__list)
  : seq_cond ExcessDelay_DRB_IdentityInfo_r17__list y ->
 (ExcessDelay_DRB_IdentityInfo_r17__cond (ExcessDelay_DRB_IdentityInfo_r17__F2 y)) /\  ExcessDelay_DRB_IdentityInfo_r17__F1 (ExcessDelay_DRB_IdentityInfo_r17__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold ExcessDelay_DRB_IdentityInfo_r17__cond. simpl in *. auto.
 - simpl. unfold ExcessDelay_DRB_IdentityInfo_r17__F1. simpl. destruct_all_unit. auto.   Qed.
Definition ExcessDelay_DRB_IdentityInfo_r17__Format : T_Format ExcessDelay_DRB_IdentityInfo_r17__Type ExcessDelay_DRB_IdentityInfo_r17__cond :=
        proj2_format  ExcessDelay_DRB_IdentityInfo_r17__cond ExcessDelay_DRB_IdentityInfo_r17__list__Format
    ExcessDelay_DRB_IdentityInfo_r17__F1 ExcessDelay_DRB_IdentityInfo_r17__F2 ExcessDelay_DRB_IdentityInfo_r17__F1F2_cond  ExcessDelay_DRB_IdentityInfo_r17__F1F2_cond2 ExcessDelay_DRB_IdentityInfo_r17__F2F1_cond.
Opaque ExcessDelay_DRB_IdentityInfo_r17__cond ExcessDelay_DRB_IdentityInfo_r17__Format.

