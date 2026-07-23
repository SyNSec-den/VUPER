Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma NAICS_Capability_Entry__numberOfNAICS_CapableCC__helper1 : (1 <= 5)%Z.  lia. Qed.
Lemma NAICS_Capability_Entry__numberOfNAICS_CapableCC__helper2 : to_bit_sz (Z.to_nat (5 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply NAICS_Capability_Entry__numberOfNAICS_CapableCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition NAICS_Capability_Entry__numberOfNAICS_CapableCC__Type := Z.
Definition NAICS_Capability_Entry__numberOfNAICS_CapableCC__cond := (fun z => (1 <= z <= 5)%Z).
Inductive NAICS_Capability_Entry__numberOfAggregatedPRB__Type : Set :=
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n50
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n75
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n100
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n125
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n150
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n175
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n200
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n225
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n250
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n275
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n300
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n350
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n400
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n450
 | NAICS_Capability_Entry__numberOfAggregatedPRB__n500
 | NAICS_Capability_Entry__numberOfAggregatedPRB__spare
.
Definition NAICS_Capability_Entry__numberOfAggregatedPRB__cond := (fun (_ : NAICS_Capability_Entry__numberOfAggregatedPRB__Type) => True).
Lemma NAICS_Capability_Entry__numberOfAggregatedPRB__nat__helper : to_bit_sz 15 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NAICS_Capability_Entry__numberOfAggregatedPRB__nat__Format : T_Format nat (fun z => (z <= 15)) :=
  nat_enum_format 15 NAICS_Capability_Entry__numberOfAggregatedPRB__nat__helper.

Definition NAICS_Capability_Entry__numberOfAggregatedPRB__F1 t :=
  match t with
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n50 => 0
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n75 => 1
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n100 => 2
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n125 => 3
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n150 => 4
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n175 => 5
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n200 => 6
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n225 => 7
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n250 => 8
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n275 => 9
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n300 => 10
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n350 => 11
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n400 => 12
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n450 => 13
  | NAICS_Capability_Entry__numberOfAggregatedPRB__n500 => 14
  | NAICS_Capability_Entry__numberOfAggregatedPRB__spare => 15
  end.
Definition NAICS_Capability_Entry__numberOfAggregatedPRB__F2 n :=
  match n with
  | 0 => NAICS_Capability_Entry__numberOfAggregatedPRB__n50
  | 1 => NAICS_Capability_Entry__numberOfAggregatedPRB__n75
  | 2 => NAICS_Capability_Entry__numberOfAggregatedPRB__n100
  | 3 => NAICS_Capability_Entry__numberOfAggregatedPRB__n125
  | 4 => NAICS_Capability_Entry__numberOfAggregatedPRB__n150
  | 5 => NAICS_Capability_Entry__numberOfAggregatedPRB__n175
  | 6 => NAICS_Capability_Entry__numberOfAggregatedPRB__n200
  | 7 => NAICS_Capability_Entry__numberOfAggregatedPRB__n225
  | 8 => NAICS_Capability_Entry__numberOfAggregatedPRB__n250
  | 9 => NAICS_Capability_Entry__numberOfAggregatedPRB__n275
  | 10 => NAICS_Capability_Entry__numberOfAggregatedPRB__n300
  | 11 => NAICS_Capability_Entry__numberOfAggregatedPRB__n350
  | 12 => NAICS_Capability_Entry__numberOfAggregatedPRB__n400
  | 13 => NAICS_Capability_Entry__numberOfAggregatedPRB__n450
  | 14 => NAICS_Capability_Entry__numberOfAggregatedPRB__n500
  | 15 => NAICS_Capability_Entry__numberOfAggregatedPRB__spare
  | _ => NAICS_Capability_Entry__numberOfAggregatedPRB__n50
  end.
Lemma NAICS_Capability_Entry__numberOfAggregatedPRB__F1F2 : forall x : NAICS_Capability_Entry__numberOfAggregatedPRB__Type, (NAICS_Capability_Entry__numberOfAggregatedPRB__F1 x <= 15) /\ NAICS_Capability_Entry__numberOfAggregatedPRB__F2 (NAICS_Capability_Entry__numberOfAggregatedPRB__F1 x) = x. imp_solve. Qed.
Lemma NAICS_Capability_Entry__numberOfAggregatedPRB__F2F1 : forall (y : nat) (H : y <= 15), NAICS_Capability_Entry__numberOfAggregatedPRB__F1 (NAICS_Capability_Entry__numberOfAggregatedPRB__F2 y) = y. enum_solve H y. Qed.

Record NAICS_Capability_Entry__Type : Set :=
  make__NAICS_Capability_Entry__Type {
    NAICS_Capability_Entry__numberOfNAICS_CapableCC : Z ;
    NAICS_Capability_Entry__numberOfAggregatedPRB : NAICS_Capability_Entry__numberOfAggregatedPRB__Type ;
}.
Definition NAICS_Capability_Entry__root_list : list seq_elem := (
 Nor Z NAICS_Capability_Entry__numberOfNAICS_CapableCC__cond ::
 Nor NAICS_Capability_Entry__numberOfAggregatedPRB__Type NAICS_Capability_Entry__numberOfAggregatedPRB__cond ::
 nil).
Definition NAICS_Capability_Entry__ext_list : list typ := (
  nil).
Definition NAICS_Capability_Entry__cond (z : NAICS_Capability_Entry__Type) := 
(  NAICS_Capability_Entry__numberOfNAICS_CapableCC__cond (NAICS_Capability_Entry__numberOfNAICS_CapableCC z) /\
  NAICS_Capability_Entry__numberOfAggregatedPRB__cond (NAICS_Capability_Entry__numberOfAggregatedPRB z) /\
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
Definition NAICS_Capability_Entry__numberOfNAICS_CapableCC__Format : T_Format Z NAICS_Capability_Entry__numberOfNAICS_CapableCC__cond :=
 ranged_int_format (1) (5) NAICS_Capability_Entry__numberOfNAICS_CapableCC__helper1 NAICS_Capability_Entry__numberOfNAICS_CapableCC__helper2.

Opaque NAICS_Capability_Entry__numberOfNAICS_CapableCC__cond NAICS_Capability_Entry__numberOfNAICS_CapableCC__Format.

Definition NAICS_Capability_Entry__numberOfAggregatedPRB__Format : T_Format NAICS_Capability_Entry__numberOfAggregatedPRB__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NAICS_Capability_Entry__numberOfAggregatedPRB__nat__Format NAICS_Capability_Entry__numberOfAggregatedPRB__F1 NAICS_Capability_Entry__numberOfAggregatedPRB__F2 NAICS_Capability_Entry__numberOfAggregatedPRB__F1F2 NAICS_Capability_Entry__numberOfAggregatedPRB__F2F1.

Opaque NAICS_Capability_Entry__numberOfAggregatedPRB__cond NAICS_Capability_Entry__numberOfAggregatedPRB__Format.


Definition NAICS_Capability_Entry__root_Format_Type := Eval cbn in seq_format_prod NAICS_Capability_Entry__root_list.
Definition NAICS_Capability_Entry__root_Format_list : NAICS_Capability_Entry__root_Format_Type :=
  (NAICS_Capability_Entry__numberOfNAICS_CapableCC__Format, (NAICS_Capability_Entry__numberOfAggregatedPRB__Format, unit_format)).

Definition NAICS_Capability_Entry__ext_Format_Type := Eval cbn in get_formats NAICS_Capability_Entry__ext_list.
Definition NAICS_Capability_Entry__ext_Format_list : NAICS_Capability_Entry__ext_Format_Type :=
  unit__Format.

Definition NAICS_Capability_Entry__list_type : Set := (seq_type NAICS_Capability_Entry__root_list) * (seq_ext_type NAICS_Capability_Entry__ext_list).
Definition NAICS_Capability_Entry__list_cond (z : NAICS_Capability_Entry__list_type) : Prop :=
        (seq_cond NAICS_Capability_Entry__root_list (fst z)) /\ (seq_ext_cond NAICS_Capability_Entry__ext_list (snd z)).
Definition NAICS_Capability_Entry__list_format : T_Format NAICS_Capability_Entry__list_type NAICS_Capability_Entry__list_cond :=
 (* Eval compute in *) seq_ext_format NAICS_Capability_Entry__root_list NAICS_Capability_Entry__root_Format_list NAICS_Capability_Entry__ext_list NAICS_Capability_Entry__ext_Format_list.

Opaque NAICS_Capability_Entry__list_format.
Definition NAICS_Capability_Entry__F1 (z : NAICS_Capability_Entry__Type) : NAICS_Capability_Entry__list_type :=
  (((NAICS_Capability_Entry__numberOfNAICS_CapableCC z, (NAICS_Capability_Entry__numberOfAggregatedPRB z, tt))), (
tt)).
Definition NAICS_Capability_Entry__F2 (y : NAICS_Capability_Entry__list_type) : NAICS_Capability_Entry__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__NAICS_Capability_Entry__Type j0 j1
  end.
Definition NAICS_Capability_Entry__helper1 : (forall a : NAICS_Capability_Entry__Type, NAICS_Capability_Entry__cond a -> NAICS_Capability_Entry__list_cond (NAICS_Capability_Entry__F1 a)).
                     intros. destruct a. auto. Qed.
Definition NAICS_Capability_Entry__helper2 : (forall a : NAICS_Capability_Entry__Type, NAICS_Capability_Entry__F2 (NAICS_Capability_Entry__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition NAICS_Capability_Entry__helper3 : (forall b : NAICS_Capability_Entry__list_type, NAICS_Capability_Entry__list_cond b -> NAICS_Capability_Entry__cond (NAICS_Capability_Entry__F2 b) /\ NAICS_Capability_Entry__F1 (NAICS_Capability_Entry__F2 b) = b).
                     intros. destruct b as [y y1]. unfold NAICS_Capability_Entry__cond, NAICS_Capability_Entry__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition NAICS_Capability_Entry__Format : T_Format NAICS_Capability_Entry__Type NAICS_Capability_Entry__cond :=
 proj2_format NAICS_Capability_Entry__cond NAICS_Capability_Entry__list_format  NAICS_Capability_Entry__F1 NAICS_Capability_Entry__F2 NAICS_Capability_Entry__helper1 NAICS_Capability_Entry__helper2 NAICS_Capability_Entry__helper3.

Opaque NAICS_Capability_Entry__cond NAICS_Capability_Entry__Format.

