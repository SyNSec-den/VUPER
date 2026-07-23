Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive MobilityStateParameters__t_Evaluation__Type : Set :=
 | MobilityStateParameters__t_Evaluation__s30
 | MobilityStateParameters__t_Evaluation__s60
 | MobilityStateParameters__t_Evaluation__s120
 | MobilityStateParameters__t_Evaluation__s180
 | MobilityStateParameters__t_Evaluation__s240
 | MobilityStateParameters__t_Evaluation__spare3
 | MobilityStateParameters__t_Evaluation__spare2
 | MobilityStateParameters__t_Evaluation__spare1
.
Definition MobilityStateParameters__t_Evaluation__cond := (fun (_ : MobilityStateParameters__t_Evaluation__Type) => True).
Lemma MobilityStateParameters__t_Evaluation__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MobilityStateParameters__t_Evaluation__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MobilityStateParameters__t_Evaluation__nat__helper.

Definition MobilityStateParameters__t_Evaluation__F1 t :=
  match t with
  | MobilityStateParameters__t_Evaluation__s30 => 0
  | MobilityStateParameters__t_Evaluation__s60 => 1
  | MobilityStateParameters__t_Evaluation__s120 => 2
  | MobilityStateParameters__t_Evaluation__s180 => 3
  | MobilityStateParameters__t_Evaluation__s240 => 4
  | MobilityStateParameters__t_Evaluation__spare3 => 5
  | MobilityStateParameters__t_Evaluation__spare2 => 6
  | MobilityStateParameters__t_Evaluation__spare1 => 7
  end.
Definition MobilityStateParameters__t_Evaluation__F2 n :=
  match n with
  | 0 => MobilityStateParameters__t_Evaluation__s30
  | 1 => MobilityStateParameters__t_Evaluation__s60
  | 2 => MobilityStateParameters__t_Evaluation__s120
  | 3 => MobilityStateParameters__t_Evaluation__s180
  | 4 => MobilityStateParameters__t_Evaluation__s240
  | 5 => MobilityStateParameters__t_Evaluation__spare3
  | 6 => MobilityStateParameters__t_Evaluation__spare2
  | 7 => MobilityStateParameters__t_Evaluation__spare1
  | _ => MobilityStateParameters__t_Evaluation__s30
  end.
Lemma MobilityStateParameters__t_Evaluation__F1F2 : forall x : MobilityStateParameters__t_Evaluation__Type, (MobilityStateParameters__t_Evaluation__F1 x <= 7) /\ MobilityStateParameters__t_Evaluation__F2 (MobilityStateParameters__t_Evaluation__F1 x) = x. imp_solve. Qed.
Lemma MobilityStateParameters__t_Evaluation__F2F1 : forall (y : nat) (H : y <= 7), MobilityStateParameters__t_Evaluation__F1 (MobilityStateParameters__t_Evaluation__F2 y) = y. enum_solve H y. Qed.

Inductive MobilityStateParameters__t_HystNormal__Type : Set :=
 | MobilityStateParameters__t_HystNormal__s30
 | MobilityStateParameters__t_HystNormal__s60
 | MobilityStateParameters__t_HystNormal__s120
 | MobilityStateParameters__t_HystNormal__s180
 | MobilityStateParameters__t_HystNormal__s240
 | MobilityStateParameters__t_HystNormal__spare3
 | MobilityStateParameters__t_HystNormal__spare2
 | MobilityStateParameters__t_HystNormal__spare1
.
Definition MobilityStateParameters__t_HystNormal__cond := (fun (_ : MobilityStateParameters__t_HystNormal__Type) => True).
Lemma MobilityStateParameters__t_HystNormal__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MobilityStateParameters__t_HystNormal__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 MobilityStateParameters__t_HystNormal__nat__helper.

Definition MobilityStateParameters__t_HystNormal__F1 t :=
  match t with
  | MobilityStateParameters__t_HystNormal__s30 => 0
  | MobilityStateParameters__t_HystNormal__s60 => 1
  | MobilityStateParameters__t_HystNormal__s120 => 2
  | MobilityStateParameters__t_HystNormal__s180 => 3
  | MobilityStateParameters__t_HystNormal__s240 => 4
  | MobilityStateParameters__t_HystNormal__spare3 => 5
  | MobilityStateParameters__t_HystNormal__spare2 => 6
  | MobilityStateParameters__t_HystNormal__spare1 => 7
  end.
Definition MobilityStateParameters__t_HystNormal__F2 n :=
  match n with
  | 0 => MobilityStateParameters__t_HystNormal__s30
  | 1 => MobilityStateParameters__t_HystNormal__s60
  | 2 => MobilityStateParameters__t_HystNormal__s120
  | 3 => MobilityStateParameters__t_HystNormal__s180
  | 4 => MobilityStateParameters__t_HystNormal__s240
  | 5 => MobilityStateParameters__t_HystNormal__spare3
  | 6 => MobilityStateParameters__t_HystNormal__spare2
  | 7 => MobilityStateParameters__t_HystNormal__spare1
  | _ => MobilityStateParameters__t_HystNormal__s30
  end.
Lemma MobilityStateParameters__t_HystNormal__F1F2 : forall x : MobilityStateParameters__t_HystNormal__Type, (MobilityStateParameters__t_HystNormal__F1 x <= 7) /\ MobilityStateParameters__t_HystNormal__F2 (MobilityStateParameters__t_HystNormal__F1 x) = x. imp_solve. Qed.
Lemma MobilityStateParameters__t_HystNormal__F2F1 : forall (y : nat) (H : y <= 7), MobilityStateParameters__t_HystNormal__F1 (MobilityStateParameters__t_HystNormal__F2 y) = y. enum_solve H y. Qed.

Lemma MobilityStateParameters__n_CellChangeMedium__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma MobilityStateParameters__n_CellChangeMedium__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MobilityStateParameters__n_CellChangeMedium__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MobilityStateParameters__n_CellChangeMedium__Type := Z.
Definition MobilityStateParameters__n_CellChangeMedium__cond := (fun z => (1 <= z <= 16)%Z).
Lemma MobilityStateParameters__n_CellChangeHigh__helper1 : (1 <= 16)%Z.  lia. Qed.
Lemma MobilityStateParameters__n_CellChangeHigh__helper2 : to_bit_sz (Z.to_nat (16 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (16 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply MobilityStateParameters__n_CellChangeHigh__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition MobilityStateParameters__n_CellChangeHigh__Type := Z.
Definition MobilityStateParameters__n_CellChangeHigh__cond := (fun z => (1 <= z <= 16)%Z).
Record MobilityStateParameters__Type : Set :=
  make__MobilityStateParameters__Type {
    MobilityStateParameters__t_Evaluation : MobilityStateParameters__t_Evaluation__Type ;
    MobilityStateParameters__t_HystNormal : MobilityStateParameters__t_HystNormal__Type ;
    MobilityStateParameters__n_CellChangeMedium : Z ;
    MobilityStateParameters__n_CellChangeHigh : Z ;
}.
Definition MobilityStateParameters__list := (
 Nor MobilityStateParameters__t_Evaluation__Type MobilityStateParameters__t_Evaluation__cond ::
 Nor MobilityStateParameters__t_HystNormal__Type MobilityStateParameters__t_HystNormal__cond ::
 Nor Z MobilityStateParameters__n_CellChangeMedium__cond ::
 Nor Z MobilityStateParameters__n_CellChangeHigh__cond ::
 nil).
Definition MobilityStateParameters__cond z := 
  MobilityStateParameters__t_Evaluation__cond (MobilityStateParameters__t_Evaluation z) /\
  MobilityStateParameters__t_HystNormal__cond (MobilityStateParameters__t_HystNormal z) /\
  MobilityStateParameters__n_CellChangeMedium__cond (MobilityStateParameters__n_CellChangeMedium z) /\
  MobilityStateParameters__n_CellChangeHigh__cond (MobilityStateParameters__n_CellChangeHigh z) /\
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
Definition MobilityStateParameters__t_Evaluation__Format : T_Format MobilityStateParameters__t_Evaluation__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MobilityStateParameters__t_Evaluation__nat__Format MobilityStateParameters__t_Evaluation__F1 MobilityStateParameters__t_Evaluation__F2 MobilityStateParameters__t_Evaluation__F1F2 MobilityStateParameters__t_Evaluation__F2F1.

Opaque MobilityStateParameters__t_Evaluation__cond MobilityStateParameters__t_Evaluation__Format.

Definition MobilityStateParameters__t_HystNormal__Format : T_Format MobilityStateParameters__t_HystNormal__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MobilityStateParameters__t_HystNormal__nat__Format MobilityStateParameters__t_HystNormal__F1 MobilityStateParameters__t_HystNormal__F2 MobilityStateParameters__t_HystNormal__F1F2 MobilityStateParameters__t_HystNormal__F2F1.

Opaque MobilityStateParameters__t_HystNormal__cond MobilityStateParameters__t_HystNormal__Format.

Definition MobilityStateParameters__n_CellChangeMedium__Format : T_Format Z MobilityStateParameters__n_CellChangeMedium__cond :=
 ranged_int_format (1) (16) MobilityStateParameters__n_CellChangeMedium__helper1 MobilityStateParameters__n_CellChangeMedium__helper2.

Opaque MobilityStateParameters__n_CellChangeMedium__cond MobilityStateParameters__n_CellChangeMedium__Format.

Definition MobilityStateParameters__n_CellChangeHigh__Format : T_Format Z MobilityStateParameters__n_CellChangeHigh__cond :=
 ranged_int_format (1) (16) MobilityStateParameters__n_CellChangeHigh__helper1 MobilityStateParameters__n_CellChangeHigh__helper2.

Opaque MobilityStateParameters__n_CellChangeHigh__cond MobilityStateParameters__n_CellChangeHigh__Format.


Definition MobilityStateParameters__Format_Type := Eval cbn in seq_format_prod MobilityStateParameters__list.
Definition MobilityStateParameters__Format_list : MobilityStateParameters__Format_Type :=
  (MobilityStateParameters__t_Evaluation__Format, (MobilityStateParameters__t_HystNormal__Format, (MobilityStateParameters__n_CellChangeMedium__Format, (MobilityStateParameters__n_CellChangeHigh__Format, unit_format)))).
Definition MobilityStateParameters__list__Format := (*Eval compute in *) seq_format MobilityStateParameters__list MobilityStateParameters__Format_list.
Definition MobilityStateParameters__F1 z :=
  (MobilityStateParameters__t_Evaluation z, (MobilityStateParameters__t_HystNormal z, (MobilityStateParameters__n_CellChangeMedium z, (MobilityStateParameters__n_CellChangeHigh z, tt)))).
Definition MobilityStateParameters__F2 (y : seq_type MobilityStateParameters__list) :=
  match y with
  | (i0, (i1, (i2, (i3, _))))=>
    make__MobilityStateParameters__Type i0 i1 i2 i3
  end.
Lemma MobilityStateParameters__F1F2_cond (z : MobilityStateParameters__Type)
  : MobilityStateParameters__cond z ->
  (seq_cond MobilityStateParameters__list (MobilityStateParameters__F1 z)).
intro H. unfold MobilityStateParameters__cond in H. simpl. auto. Qed.
Lemma MobilityStateParameters__F1F2_cond2 (z : MobilityStateParameters__Type)
 : MobilityStateParameters__F2 (MobilityStateParameters__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma MobilityStateParameters__F2F1_cond (y : seq_type MobilityStateParameters__list)
  : seq_cond MobilityStateParameters__list y ->
 (MobilityStateParameters__cond (MobilityStateParameters__F2 y)) /\  MobilityStateParameters__F1 (MobilityStateParameters__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold MobilityStateParameters__cond. simpl in *. auto.
 - simpl. unfold MobilityStateParameters__F1. simpl. destruct_all_unit. auto.   Qed.
Definition MobilityStateParameters__Format : T_Format MobilityStateParameters__Type MobilityStateParameters__cond :=
        proj2_format  MobilityStateParameters__cond MobilityStateParameters__list__Format
    MobilityStateParameters__F1 MobilityStateParameters__F2 MobilityStateParameters__F1F2_cond  MobilityStateParameters__F1F2_cond2 MobilityStateParameters__F2F1_cond.
Opaque MobilityStateParameters__cond MobilityStateParameters__Format.

