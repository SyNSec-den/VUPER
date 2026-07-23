Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.PC5_RRC_Definitions.
Inductive NotificationMessageSidelink_r17_IEs__indicationType_r17__Type : Set :=
 | NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_Uu_RLF
 | NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_HO
 | NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_CellReselection
 | NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_Uu_RRC_Failure
.
Definition NotificationMessageSidelink_r17_IEs__indicationType_r17__cond := (fun (_ : NotificationMessageSidelink_r17_IEs__indicationType_r17__Type) => True).
Lemma NotificationMessageSidelink_r17_IEs__indicationType_r17__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition NotificationMessageSidelink_r17_IEs__indicationType_r17__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 NotificationMessageSidelink_r17_IEs__indicationType_r17__nat__helper.

Definition NotificationMessageSidelink_r17_IEs__indicationType_r17__F1 t :=
  match t with
  | NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_Uu_RLF => 0
  | NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_HO => 1
  | NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_CellReselection => 2
  | NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_Uu_RRC_Failure => 3
  end.
Definition NotificationMessageSidelink_r17_IEs__indicationType_r17__F2 n :=
  match n with
  | 0 => NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_Uu_RLF
  | 1 => NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_HO
  | 2 => NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_CellReselection
  | 3 => NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_Uu_RRC_Failure
  | _ => NotificationMessageSidelink_r17_IEs__indicationType_r17__relayUE_Uu_RLF
  end.
Lemma NotificationMessageSidelink_r17_IEs__indicationType_r17__F1F2 : forall x : NotificationMessageSidelink_r17_IEs__indicationType_r17__Type, (NotificationMessageSidelink_r17_IEs__indicationType_r17__F1 x <= 3) /\ NotificationMessageSidelink_r17_IEs__indicationType_r17__F2 (NotificationMessageSidelink_r17_IEs__indicationType_r17__F1 x) = x. imp_solve. Qed.
Lemma NotificationMessageSidelink_r17_IEs__indicationType_r17__F2F1 : forall (y : nat) (H : y <= 3), NotificationMessageSidelink_r17_IEs__indicationType_r17__F1 (NotificationMessageSidelink_r17_IEs__indicationType_r17__F2 y) = y. enum_solve H y. Qed.

Record NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type : Set := make__NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type {}.
Definition NotificationMessageSidelink_r17_IEs__nonCriticalExtension__cond (z : NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type) := True.
Record NotificationMessageSidelink_r17_IEs__Type : Set :=
  make__NotificationMessageSidelink_r17_IEs__Type {
    NotificationMessageSidelink_r17_IEs__indicationType_r17 : option NotificationMessageSidelink_r17_IEs__indicationType_r17__Type ;
    NotificationMessageSidelink_r17_IEs__lateNonCriticalExtension : option octet_string ;
    NotificationMessageSidelink_r17_IEs__nonCriticalExtension : option NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type ;
}.
Definition NotificationMessageSidelink_r17_IEs__list := (
 Opt NotificationMessageSidelink_r17_IEs__indicationType_r17__Type NotificationMessageSidelink_r17_IEs__indicationType_r17__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type NotificationMessageSidelink_r17_IEs__nonCriticalExtension__cond ::
 nil).
Definition NotificationMessageSidelink_r17_IEs__cond z := 
  opt_cond NotificationMessageSidelink_r17_IEs__indicationType_r17__cond (NotificationMessageSidelink_r17_IEs__indicationType_r17 z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (NotificationMessageSidelink_r17_IEs__lateNonCriticalExtension z) /\
  opt_cond NotificationMessageSidelink_r17_IEs__nonCriticalExtension__cond (NotificationMessageSidelink_r17_IEs__nonCriticalExtension z) /\
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
Definition NotificationMessageSidelink_r17_IEs__indicationType_r17__Format : T_Format NotificationMessageSidelink_r17_IEs__indicationType_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format NotificationMessageSidelink_r17_IEs__indicationType_r17__nat__Format NotificationMessageSidelink_r17_IEs__indicationType_r17__F1 NotificationMessageSidelink_r17_IEs__indicationType_r17__F2 NotificationMessageSidelink_r17_IEs__indicationType_r17__F1F2 NotificationMessageSidelink_r17_IEs__indicationType_r17__F2F1.

Opaque NotificationMessageSidelink_r17_IEs__indicationType_r17__cond NotificationMessageSidelink_r17_IEs__indicationType_r17__Format.

Definition NotificationMessageSidelink_r17_IEs__nonCriticalExtension__helper : forall a : NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type, True -> True /\ make__NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Format : T_Format NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type NotificationMessageSidelink_r17_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Type)
    NotificationMessageSidelink_r17_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque NotificationMessageSidelink_r17_IEs__nonCriticalExtension__cond NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Format.


Definition NotificationMessageSidelink_r17_IEs__Format_Type := Eval cbn in seq_format_prod NotificationMessageSidelink_r17_IEs__list.
Definition NotificationMessageSidelink_r17_IEs__Format_list : NotificationMessageSidelink_r17_IEs__Format_Type :=
  (NotificationMessageSidelink_r17_IEs__indicationType_r17__Format, (octet_string_nc__Format, (NotificationMessageSidelink_r17_IEs__nonCriticalExtension__Format, unit_format))).
Definition NotificationMessageSidelink_r17_IEs__list__Format := (*Eval compute in *) seq_format NotificationMessageSidelink_r17_IEs__list NotificationMessageSidelink_r17_IEs__Format_list.
Definition NotificationMessageSidelink_r17_IEs__F1 z :=
  (NotificationMessageSidelink_r17_IEs__indicationType_r17 z, (NotificationMessageSidelink_r17_IEs__lateNonCriticalExtension z, (NotificationMessageSidelink_r17_IEs__nonCriticalExtension z, tt))).
Definition NotificationMessageSidelink_r17_IEs__F2 (y : seq_type NotificationMessageSidelink_r17_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__NotificationMessageSidelink_r17_IEs__Type i0 i1 i2
  end.
Lemma NotificationMessageSidelink_r17_IEs__F1F2_cond (z : NotificationMessageSidelink_r17_IEs__Type)
  : NotificationMessageSidelink_r17_IEs__cond z ->
  (seq_cond NotificationMessageSidelink_r17_IEs__list (NotificationMessageSidelink_r17_IEs__F1 z)).
intro H. unfold NotificationMessageSidelink_r17_IEs__cond in H. simpl. auto. Qed.
Lemma NotificationMessageSidelink_r17_IEs__F1F2_cond2 (z : NotificationMessageSidelink_r17_IEs__Type)
 : NotificationMessageSidelink_r17_IEs__F2 (NotificationMessageSidelink_r17_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma NotificationMessageSidelink_r17_IEs__F2F1_cond (y : seq_type NotificationMessageSidelink_r17_IEs__list)
  : seq_cond NotificationMessageSidelink_r17_IEs__list y ->
 (NotificationMessageSidelink_r17_IEs__cond (NotificationMessageSidelink_r17_IEs__F2 y)) /\  NotificationMessageSidelink_r17_IEs__F1 (NotificationMessageSidelink_r17_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold NotificationMessageSidelink_r17_IEs__cond. simpl in *. auto.
 - simpl. unfold NotificationMessageSidelink_r17_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition NotificationMessageSidelink_r17_IEs__Format : T_Format NotificationMessageSidelink_r17_IEs__Type NotificationMessageSidelink_r17_IEs__cond :=
        proj2_format  NotificationMessageSidelink_r17_IEs__cond NotificationMessageSidelink_r17_IEs__list__Format
    NotificationMessageSidelink_r17_IEs__F1 NotificationMessageSidelink_r17_IEs__F2 NotificationMessageSidelink_r17_IEs__F1F2_cond  NotificationMessageSidelink_r17_IEs__F1F2_cond2 NotificationMessageSidelink_r17_IEs__F2F1_cond.
Opaque NotificationMessageSidelink_r17_IEs__cond NotificationMessageSidelink_r17_IEs__Format.

