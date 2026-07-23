Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma PTRS_DownlinkConfig__frequencyDensity__seq_of__helper1 : (1 <= 276)%Z.  lia. Qed.
Lemma PTRS_DownlinkConfig__frequencyDensity__seq_of__helper2 : to_bit_sz (Z.to_nat (276 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (276 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DownlinkConfig__frequencyDensity__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DownlinkConfig__frequencyDensity__seq_of__Type := Z.
Definition PTRS_DownlinkConfig__frequencyDensity__seq_of__cond := (fun z => (1 <= z <= 276)%Z).
Definition PTRS_DownlinkConfig__frequencyDensity__Type := list Z.

Definition PTRS_DownlinkConfig__frequencyDensity__cond (z : PTRS_DownlinkConfig__frequencyDensity__Type) := (list_and PTRS_DownlinkConfig__frequencyDensity__seq_of__cond z) /\ (length z = Z.to_nat 2).

Lemma PTRS_DownlinkConfig__timeDensity__seq_of__helper1 : (0 <= 29)%Z.  lia. Qed.
Lemma PTRS_DownlinkConfig__timeDensity__seq_of__helper2 : to_bit_sz (Z.to_nat (29 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (29 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DownlinkConfig__timeDensity__seq_of__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DownlinkConfig__timeDensity__seq_of__Type := Z.
Definition PTRS_DownlinkConfig__timeDensity__seq_of__cond := (fun z => (0 <= z <= 29)%Z).
Definition PTRS_DownlinkConfig__timeDensity__Type := list Z.

Definition PTRS_DownlinkConfig__timeDensity__cond (z : PTRS_DownlinkConfig__timeDensity__Type) := (list_and PTRS_DownlinkConfig__timeDensity__seq_of__cond z) /\ (length z = Z.to_nat 3).

Lemma PTRS_DownlinkConfig__epre_Ratio__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma PTRS_DownlinkConfig__epre_Ratio__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply PTRS_DownlinkConfig__epre_Ratio__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition PTRS_DownlinkConfig__epre_Ratio__Type := Z.
Definition PTRS_DownlinkConfig__epre_Ratio__cond := (fun z => (0 <= z <= 3)%Z).
Inductive PTRS_DownlinkConfig__resourceElementOffset__Type : Set :=
 | PTRS_DownlinkConfig__resourceElementOffset__offset01
 | PTRS_DownlinkConfig__resourceElementOffset__offset10
 | PTRS_DownlinkConfig__resourceElementOffset__offset11
.
Definition PTRS_DownlinkConfig__resourceElementOffset__cond := (fun (_ : PTRS_DownlinkConfig__resourceElementOffset__Type) => True).
Lemma PTRS_DownlinkConfig__resourceElementOffset__nat__helper : to_bit_sz 2 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PTRS_DownlinkConfig__resourceElementOffset__nat__Format : T_Format nat (fun z => (z <= 2)) :=
  nat_enum_format 2 PTRS_DownlinkConfig__resourceElementOffset__nat__helper.

Definition PTRS_DownlinkConfig__resourceElementOffset__F1 t :=
  match t with
  | PTRS_DownlinkConfig__resourceElementOffset__offset01 => 0
  | PTRS_DownlinkConfig__resourceElementOffset__offset10 => 1
  | PTRS_DownlinkConfig__resourceElementOffset__offset11 => 2
  end.
Definition PTRS_DownlinkConfig__resourceElementOffset__F2 n :=
  match n with
  | 0 => PTRS_DownlinkConfig__resourceElementOffset__offset01
  | 1 => PTRS_DownlinkConfig__resourceElementOffset__offset10
  | 2 => PTRS_DownlinkConfig__resourceElementOffset__offset11
  | _ => PTRS_DownlinkConfig__resourceElementOffset__offset01
  end.
Lemma PTRS_DownlinkConfig__resourceElementOffset__F1F2 : forall x : PTRS_DownlinkConfig__resourceElementOffset__Type, (PTRS_DownlinkConfig__resourceElementOffset__F1 x <= 2) /\ PTRS_DownlinkConfig__resourceElementOffset__F2 (PTRS_DownlinkConfig__resourceElementOffset__F1 x) = x. imp_solve. Qed.
Lemma PTRS_DownlinkConfig__resourceElementOffset__F2F1 : forall (y : nat) (H : y <= 2), PTRS_DownlinkConfig__resourceElementOffset__F1 (PTRS_DownlinkConfig__resourceElementOffset__F2 y) = y. enum_solve H y. Qed.

Inductive PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Type : Set :=
 | PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__n1
 | PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__n2
.
Definition PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__cond := (fun (_ : PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Type) => True).
Lemma PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__nat__helper.

Definition PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F1 t :=
  match t with
  | PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__n1 => 0
  | PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__n2 => 1
  end.
Definition PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F2 n :=
  match n with
  | 0 => PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__n1
  | 1 => PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__n2
  | _ => PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__n1
  end.
Lemma PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F1F2 : forall x : PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Type, (PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F1 x <= 1) /\ PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F2 (PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F1 x) = x. imp_solve. Qed.
Lemma PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F2F1 : forall (y : nat) (H : y <= 1), PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F1 (PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F2 y) = y. enum_solve H y. Qed.

Record PTRS_DownlinkConfig__ext0O__Type : Set :=
  make__PTRS_DownlinkConfig__ext0O__Type {
    PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16 : option PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Type ;
}.
Definition PTRS_DownlinkConfig__ext0O__list := (
 Opt PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Type PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__cond ::
 nil).
Definition PTRS_DownlinkConfig__ext0O__cond z := 
  opt_cond PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__cond (PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16 z) /\
  True.

Definition PTRS_DownlinkConfig__ext0__Type := PTRS_DownlinkConfig__ext0O__Type.
Definition PTRS_DownlinkConfig__ext0__cond := PTRS_DownlinkConfig__ext0O__cond.

Record PTRS_DownlinkConfig__Type : Set :=
  make__PTRS_DownlinkConfig__Type {
    PTRS_DownlinkConfig__frequencyDensity : option PTRS_DownlinkConfig__frequencyDensity__Type ;
    PTRS_DownlinkConfig__timeDensity : option PTRS_DownlinkConfig__timeDensity__Type ;
    PTRS_DownlinkConfig__epre_Ratio : option Z ;
    PTRS_DownlinkConfig__resourceElementOffset : option PTRS_DownlinkConfig__resourceElementOffset__Type ;
    PTRS_DownlinkConfig__ext0 : option PTRS_DownlinkConfig__ext0__Type ;
}.
Definition PTRS_DownlinkConfig__root_list : list seq_elem := (
 Opt PTRS_DownlinkConfig__frequencyDensity__Type PTRS_DownlinkConfig__frequencyDensity__cond ::
 Opt PTRS_DownlinkConfig__timeDensity__Type PTRS_DownlinkConfig__timeDensity__cond ::
 Opt Z PTRS_DownlinkConfig__epre_Ratio__cond ::
 Opt PTRS_DownlinkConfig__resourceElementOffset__Type PTRS_DownlinkConfig__resourceElementOffset__cond ::
 nil).
Definition PTRS_DownlinkConfig__ext_list : list typ := (
  typ_cons PTRS_DownlinkConfig__ext0__Type PTRS_DownlinkConfig__ext0__cond ::
  nil).
Definition PTRS_DownlinkConfig__cond (z : PTRS_DownlinkConfig__Type) := 
(  opt_cond PTRS_DownlinkConfig__frequencyDensity__cond (PTRS_DownlinkConfig__frequencyDensity z) /\
  opt_cond PTRS_DownlinkConfig__timeDensity__cond (PTRS_DownlinkConfig__timeDensity z) /\
  opt_cond PTRS_DownlinkConfig__epre_Ratio__cond (PTRS_DownlinkConfig__epre_Ratio z) /\
  opt_cond PTRS_DownlinkConfig__resourceElementOffset__cond (PTRS_DownlinkConfig__resourceElementOffset z) /\
  True) /\ 
(  opt_cond PTRS_DownlinkConfig__ext0__cond (PTRS_DownlinkConfig__ext0 z) /\
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
Definition PTRS_DownlinkConfig__frequencyDensity__seq_of__Format : T_Format Z PTRS_DownlinkConfig__frequencyDensity__seq_of__cond :=
 ranged_int_format (1) (276) PTRS_DownlinkConfig__frequencyDensity__seq_of__helper1 PTRS_DownlinkConfig__frequencyDensity__seq_of__helper2.

Opaque PTRS_DownlinkConfig__frequencyDensity__seq_of__cond PTRS_DownlinkConfig__frequencyDensity__seq_of__Format.

Definition PTRS_DownlinkConfig__frequencyDensity__Format : T_Format PTRS_DownlinkConfig__frequencyDensity__Type PTRS_DownlinkConfig__frequencyDensity__cond := seq_of_fixed_format PTRS_DownlinkConfig__frequencyDensity__seq_of__Format 2.

Opaque PTRS_DownlinkConfig__frequencyDensity__cond PTRS_DownlinkConfig__frequencyDensity__Format.

Definition PTRS_DownlinkConfig__timeDensity__seq_of__Format : T_Format Z PTRS_DownlinkConfig__timeDensity__seq_of__cond :=
 ranged_int_format (0) (29) PTRS_DownlinkConfig__timeDensity__seq_of__helper1 PTRS_DownlinkConfig__timeDensity__seq_of__helper2.

Opaque PTRS_DownlinkConfig__timeDensity__seq_of__cond PTRS_DownlinkConfig__timeDensity__seq_of__Format.

Definition PTRS_DownlinkConfig__timeDensity__Format : T_Format PTRS_DownlinkConfig__timeDensity__Type PTRS_DownlinkConfig__timeDensity__cond := seq_of_fixed_format PTRS_DownlinkConfig__timeDensity__seq_of__Format 3.

Opaque PTRS_DownlinkConfig__timeDensity__cond PTRS_DownlinkConfig__timeDensity__Format.

Definition PTRS_DownlinkConfig__epre_Ratio__Format : T_Format Z PTRS_DownlinkConfig__epre_Ratio__cond :=
 ranged_int_format (0) (3) PTRS_DownlinkConfig__epre_Ratio__helper1 PTRS_DownlinkConfig__epre_Ratio__helper2.

Opaque PTRS_DownlinkConfig__epre_Ratio__cond PTRS_DownlinkConfig__epre_Ratio__Format.

Definition PTRS_DownlinkConfig__resourceElementOffset__Format : T_Format PTRS_DownlinkConfig__resourceElementOffset__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PTRS_DownlinkConfig__resourceElementOffset__nat__Format PTRS_DownlinkConfig__resourceElementOffset__F1 PTRS_DownlinkConfig__resourceElementOffset__F2 PTRS_DownlinkConfig__resourceElementOffset__F1F2 PTRS_DownlinkConfig__resourceElementOffset__F2F1.

Opaque PTRS_DownlinkConfig__resourceElementOffset__cond PTRS_DownlinkConfig__resourceElementOffset__Format.

Definition PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Format : T_Format PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__nat__Format PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F1 PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F2 PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F1F2 PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__F2F1.

Opaque PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__cond PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Format.


Definition PTRS_DownlinkConfig__ext0O__Format_Type := Eval cbn in seq_format_prod PTRS_DownlinkConfig__ext0O__list.
Definition PTRS_DownlinkConfig__ext0O__Format_list : PTRS_DownlinkConfig__ext0O__Format_Type :=
  (PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16__Format, unit_format).
Definition PTRS_DownlinkConfig__ext0O__list__Format := (*Eval compute in *) seq_format PTRS_DownlinkConfig__ext0O__list PTRS_DownlinkConfig__ext0O__Format_list.
Definition PTRS_DownlinkConfig__ext0O__F1 z :=
  (PTRS_DownlinkConfig__ext0O__maxNrofPorts_r16 z, tt).
Definition PTRS_DownlinkConfig__ext0O__F2 (y : seq_type PTRS_DownlinkConfig__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__PTRS_DownlinkConfig__ext0O__Type i0
  end.
Lemma PTRS_DownlinkConfig__ext0O__F1F2_cond (z : PTRS_DownlinkConfig__ext0O__Type)
  : PTRS_DownlinkConfig__ext0O__cond z ->
  (seq_cond PTRS_DownlinkConfig__ext0O__list (PTRS_DownlinkConfig__ext0O__F1 z)).
intro H. unfold PTRS_DownlinkConfig__ext0O__cond in H. simpl. auto. Qed.
Lemma PTRS_DownlinkConfig__ext0O__F1F2_cond2 (z : PTRS_DownlinkConfig__ext0O__Type)
 : PTRS_DownlinkConfig__ext0O__F2 (PTRS_DownlinkConfig__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma PTRS_DownlinkConfig__ext0O__F2F1_cond (y : seq_type PTRS_DownlinkConfig__ext0O__list)
  : seq_cond PTRS_DownlinkConfig__ext0O__list y ->
 (PTRS_DownlinkConfig__ext0O__cond (PTRS_DownlinkConfig__ext0O__F2 y)) /\  PTRS_DownlinkConfig__ext0O__F1 (PTRS_DownlinkConfig__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold PTRS_DownlinkConfig__ext0O__cond. simpl in *. auto.
 - simpl. unfold PTRS_DownlinkConfig__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition PTRS_DownlinkConfig__ext0O__Format : T_Format PTRS_DownlinkConfig__ext0O__Type PTRS_DownlinkConfig__ext0O__cond :=
        proj2_format  PTRS_DownlinkConfig__ext0O__cond PTRS_DownlinkConfig__ext0O__list__Format
    PTRS_DownlinkConfig__ext0O__F1 PTRS_DownlinkConfig__ext0O__F2 PTRS_DownlinkConfig__ext0O__F1F2_cond  PTRS_DownlinkConfig__ext0O__F1F2_cond2 PTRS_DownlinkConfig__ext0O__F2F1_cond.
Opaque PTRS_DownlinkConfig__ext0O__cond PTRS_DownlinkConfig__ext0O__Format.

Definition PTRS_DownlinkConfig__ext0__check_all_none (b : PTRS_DownlinkConfig__ext0O__Type) : bool :=
match b with 
  | make__PTRS_DownlinkConfig__ext0O__Type None  => false 
  | _ => true 
 end.
Definition PTRS_DownlinkConfig__ext0__Format : T_Format PTRS_DownlinkConfig__ext0__Type PTRS_DownlinkConfig__ext0__cond :=
  restrict_add_format PTRS_DownlinkConfig__ext0__check_all_none PTRS_DownlinkConfig__ext0O__Format.

Opaque PTRS_DownlinkConfig__ext0__cond PTRS_DownlinkConfig__ext0__Format.


Definition PTRS_DownlinkConfig__root_Format_Type := Eval cbn in seq_format_prod PTRS_DownlinkConfig__root_list.
Definition PTRS_DownlinkConfig__root_Format_list : PTRS_DownlinkConfig__root_Format_Type :=
  (PTRS_DownlinkConfig__frequencyDensity__Format, (PTRS_DownlinkConfig__timeDensity__Format, (PTRS_DownlinkConfig__epre_Ratio__Format, (PTRS_DownlinkConfig__resourceElementOffset__Format, unit_format)))).

Definition PTRS_DownlinkConfig__ext_Format_Type := Eval cbn in get_formats PTRS_DownlinkConfig__ext_list.
Definition PTRS_DownlinkConfig__ext_Format_list : PTRS_DownlinkConfig__ext_Format_Type :=
  (PTRS_DownlinkConfig__ext0__Format, unit__Format).

Definition PTRS_DownlinkConfig__list_type : Set := (seq_type PTRS_DownlinkConfig__root_list) * (seq_ext_type PTRS_DownlinkConfig__ext_list).
Definition PTRS_DownlinkConfig__list_cond (z : PTRS_DownlinkConfig__list_type) : Prop :=
        (seq_cond PTRS_DownlinkConfig__root_list (fst z)) /\ (seq_ext_cond PTRS_DownlinkConfig__ext_list (snd z)).
Definition PTRS_DownlinkConfig__list_format : T_Format PTRS_DownlinkConfig__list_type PTRS_DownlinkConfig__list_cond :=
 (* Eval compute in *) seq_ext_format PTRS_DownlinkConfig__root_list PTRS_DownlinkConfig__root_Format_list PTRS_DownlinkConfig__ext_list PTRS_DownlinkConfig__ext_Format_list.

Opaque PTRS_DownlinkConfig__list_format.
Definition PTRS_DownlinkConfig__F1 (z : PTRS_DownlinkConfig__Type) : PTRS_DownlinkConfig__list_type :=
  (((PTRS_DownlinkConfig__frequencyDensity z, (PTRS_DownlinkConfig__timeDensity z, (PTRS_DownlinkConfig__epre_Ratio z, (PTRS_DownlinkConfig__resourceElementOffset z, tt))))), (
(PTRS_DownlinkConfig__ext0 z, tt))).
Definition PTRS_DownlinkConfig__F2 (y : PTRS_DownlinkConfig__list_type) : PTRS_DownlinkConfig__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, _)))), (i0, _))=>
    make__PTRS_DownlinkConfig__Type j0 j1 j2 j3 i0
  end.
Definition PTRS_DownlinkConfig__helper1 : (forall a : PTRS_DownlinkConfig__Type, PTRS_DownlinkConfig__cond a -> PTRS_DownlinkConfig__list_cond (PTRS_DownlinkConfig__F1 a)).
                     intros. destruct a. auto. Qed.
Definition PTRS_DownlinkConfig__helper2 : (forall a : PTRS_DownlinkConfig__Type, PTRS_DownlinkConfig__F2 (PTRS_DownlinkConfig__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition PTRS_DownlinkConfig__helper3 : (forall b : PTRS_DownlinkConfig__list_type, PTRS_DownlinkConfig__list_cond b -> PTRS_DownlinkConfig__cond (PTRS_DownlinkConfig__F2 b) /\ PTRS_DownlinkConfig__F1 (PTRS_DownlinkConfig__F2 b) = b).
                     intros. destruct b as [y y1]. unfold PTRS_DownlinkConfig__cond, PTRS_DownlinkConfig__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition PTRS_DownlinkConfig__Format : T_Format PTRS_DownlinkConfig__Type PTRS_DownlinkConfig__cond :=
 proj2_format PTRS_DownlinkConfig__cond PTRS_DownlinkConfig__list_format  PTRS_DownlinkConfig__F1 PTRS_DownlinkConfig__F2 PTRS_DownlinkConfig__helper1 PTRS_DownlinkConfig__helper2 PTRS_DownlinkConfig__helper3.

Opaque PTRS_DownlinkConfig__cond PTRS_DownlinkConfig__Format.

