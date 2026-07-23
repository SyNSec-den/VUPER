Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Type : Set :=
 | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms120
 | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms240
 | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms480
 | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms640
 | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms1024
.
Definition RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__cond := (fun (_ : RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Type) => True).
Lemma RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__nat__helper.

Definition RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F1 t :=
  match t with
  | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms120 => 0
  | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms240 => 1
  | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms480 => 2
  | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms640 => 3
  | RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms1024 => 4
  end.
Definition RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F2 n :=
  match n with
  | 0 => RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms120
  | 1 => RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms240
  | 2 => RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms480
  | 3 => RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms640
  | 4 => RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms1024
  | _ => RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__ms120
  end.
Lemma RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F1F2 : forall x : RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Type, (RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F1 x <= 4) /\ RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F2 (RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F1 x) = x. imp_solve. Qed.
Lemma RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F2F1 : forall (y : nat) (H : y <= 4), RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F1 (RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F2 y) = y. enum_solve H y. Qed.

Lemma RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__helper1 : (1 <= 8)%Z.  lia. Qed.
Lemma RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__helper2 : to_bit_sz (Z.to_nat (8 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (8 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__Type := Z.
Definition RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__cond := (fun z => (1 <= z <= 8)%Z).
Record RAN_VisibleParameters_r17__Type : Set :=
  make__RAN_VisibleParameters_r17__Type {
    RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17 : option RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Type ;
    RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17 : option Z ;
    RAN_VisibleParameters_r17__reportPlayoutDelayForMediaStartup_r17 : option bool ;
}.
Definition RAN_VisibleParameters_r17__root_list : list seq_elem := (
 Opt RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Type RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__cond ::
 Opt Z RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__cond ::
 Opt bool (fun _ => True) ::
 nil).
Definition RAN_VisibleParameters_r17__ext_list : list typ := (
  nil).
Definition RAN_VisibleParameters_r17__cond (z : RAN_VisibleParameters_r17__Type) := 
(  opt_cond RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__cond (RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17 z) /\
  opt_cond RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__cond (RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17 z) /\
  opt_cond (fun _ => True) (RAN_VisibleParameters_r17__reportPlayoutDelayForMediaStartup_r17 z) /\
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
Definition RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Format : T_Format RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__nat__Format RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F1 RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F2 RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F1F2 RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__F2F1.

Opaque RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__cond RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Format.

Definition RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__Format : T_Format Z RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__cond :=
 ranged_int_format (1) (8) RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__helper1 RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__helper2.

Opaque RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__cond RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__Format.


Definition RAN_VisibleParameters_r17__root_Format_Type := Eval cbn in seq_format_prod RAN_VisibleParameters_r17__root_list.
Definition RAN_VisibleParameters_r17__root_Format_list : RAN_VisibleParameters_r17__root_Format_Type :=
  (RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17__Format, (RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17__Format, (bool__Format, unit_format))).

Definition RAN_VisibleParameters_r17__ext_Format_Type := Eval cbn in get_formats RAN_VisibleParameters_r17__ext_list.
Definition RAN_VisibleParameters_r17__ext_Format_list : RAN_VisibleParameters_r17__ext_Format_Type :=
  unit__Format.

Definition RAN_VisibleParameters_r17__list_type : Set := (seq_type RAN_VisibleParameters_r17__root_list) * (seq_ext_type RAN_VisibleParameters_r17__ext_list).
Definition RAN_VisibleParameters_r17__list_cond (z : RAN_VisibleParameters_r17__list_type) : Prop :=
        (seq_cond RAN_VisibleParameters_r17__root_list (fst z)) /\ (seq_ext_cond RAN_VisibleParameters_r17__ext_list (snd z)).
Definition RAN_VisibleParameters_r17__list_format : T_Format RAN_VisibleParameters_r17__list_type RAN_VisibleParameters_r17__list_cond :=
 (* Eval compute in *) seq_ext_format RAN_VisibleParameters_r17__root_list RAN_VisibleParameters_r17__root_Format_list RAN_VisibleParameters_r17__ext_list RAN_VisibleParameters_r17__ext_Format_list.

Opaque RAN_VisibleParameters_r17__list_format.
Definition RAN_VisibleParameters_r17__F1 (z : RAN_VisibleParameters_r17__Type) : RAN_VisibleParameters_r17__list_type :=
  (((RAN_VisibleParameters_r17__ran_VisiblePeriodicity_r17 z, (RAN_VisibleParameters_r17__numberOfBufferLevelEntries_r17 z, (RAN_VisibleParameters_r17__reportPlayoutDelayForMediaStartup_r17 z, tt)))), (
tt)).
Definition RAN_VisibleParameters_r17__F2 (y : RAN_VisibleParameters_r17__list_type) : RAN_VisibleParameters_r17__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__RAN_VisibleParameters_r17__Type j0 j1 j2
  end.
Definition RAN_VisibleParameters_r17__helper1 : (forall a : RAN_VisibleParameters_r17__Type, RAN_VisibleParameters_r17__cond a -> RAN_VisibleParameters_r17__list_cond (RAN_VisibleParameters_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition RAN_VisibleParameters_r17__helper2 : (forall a : RAN_VisibleParameters_r17__Type, RAN_VisibleParameters_r17__F2 (RAN_VisibleParameters_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition RAN_VisibleParameters_r17__helper3 : (forall b : RAN_VisibleParameters_r17__list_type, RAN_VisibleParameters_r17__list_cond b -> RAN_VisibleParameters_r17__cond (RAN_VisibleParameters_r17__F2 b) /\ RAN_VisibleParameters_r17__F1 (RAN_VisibleParameters_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold RAN_VisibleParameters_r17__cond, RAN_VisibleParameters_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition RAN_VisibleParameters_r17__Format : T_Format RAN_VisibleParameters_r17__Type RAN_VisibleParameters_r17__cond :=
 proj2_format RAN_VisibleParameters_r17__cond RAN_VisibleParameters_r17__list_format  RAN_VisibleParameters_r17__F1 RAN_VisibleParameters_r17__F2 RAN_VisibleParameters_r17__helper1 RAN_VisibleParameters_r17__helper2 RAN_VisibleParameters_r17__helper3.

Opaque RAN_VisibleParameters_r17__cond RAN_VisibleParameters_r17__Format.

