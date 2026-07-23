Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.TMGI_r17.

Opaque TMGI_r17__cond TMGI_r17__Format.

Require Import NR.MRB_Identity_r17.

Opaque MRB_Identity_r17__cond MRB_Identity_r17__Format.

Require Import NR.MRB_Identity_r17.

Opaque MRB_Identity_r17__cond MRB_Identity_r17__Format.

Inductive MRB_ToAddMod_r17__reestablishPDCP_r17__Type : Set :=
 | MRB_ToAddMod_r17__reestablishPDCP_r17__true
.
Definition MRB_ToAddMod_r17__reestablishPDCP_r17__cond := (fun (_ : MRB_ToAddMod_r17__reestablishPDCP_r17__Type) => True).
Lemma MRB_ToAddMod_r17__reestablishPDCP_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRB_ToAddMod_r17__reestablishPDCP_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRB_ToAddMod_r17__reestablishPDCP_r17__nat__helper.

Definition MRB_ToAddMod_r17__reestablishPDCP_r17__F1 t :=
  match t with
  | MRB_ToAddMod_r17__reestablishPDCP_r17__true => 0
  end.
Definition MRB_ToAddMod_r17__reestablishPDCP_r17__F2 n :=
  match n with
  | 0 => MRB_ToAddMod_r17__reestablishPDCP_r17__true
  | _ => MRB_ToAddMod_r17__reestablishPDCP_r17__true
  end.
Lemma MRB_ToAddMod_r17__reestablishPDCP_r17__F1F2 : forall x : MRB_ToAddMod_r17__reestablishPDCP_r17__Type, (MRB_ToAddMod_r17__reestablishPDCP_r17__F1 x <= 0) /\ MRB_ToAddMod_r17__reestablishPDCP_r17__F2 (MRB_ToAddMod_r17__reestablishPDCP_r17__F1 x) = x. imp_solve. Qed.
Lemma MRB_ToAddMod_r17__reestablishPDCP_r17__F2F1 : forall (y : nat) (H : y <= 0), MRB_ToAddMod_r17__reestablishPDCP_r17__F1 (MRB_ToAddMod_r17__reestablishPDCP_r17__F2 y) = y. enum_solve H y. Qed.

Inductive MRB_ToAddMod_r17__recoverPDCP_r17__Type : Set :=
 | MRB_ToAddMod_r17__recoverPDCP_r17__true
.
Definition MRB_ToAddMod_r17__recoverPDCP_r17__cond := (fun (_ : MRB_ToAddMod_r17__recoverPDCP_r17__Type) => True).
Lemma MRB_ToAddMod_r17__recoverPDCP_r17__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition MRB_ToAddMod_r17__recoverPDCP_r17__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 MRB_ToAddMod_r17__recoverPDCP_r17__nat__helper.

Definition MRB_ToAddMod_r17__recoverPDCP_r17__F1 t :=
  match t with
  | MRB_ToAddMod_r17__recoverPDCP_r17__true => 0
  end.
Definition MRB_ToAddMod_r17__recoverPDCP_r17__F2 n :=
  match n with
  | 0 => MRB_ToAddMod_r17__recoverPDCP_r17__true
  | _ => MRB_ToAddMod_r17__recoverPDCP_r17__true
  end.
Lemma MRB_ToAddMod_r17__recoverPDCP_r17__F1F2 : forall x : MRB_ToAddMod_r17__recoverPDCP_r17__Type, (MRB_ToAddMod_r17__recoverPDCP_r17__F1 x <= 0) /\ MRB_ToAddMod_r17__recoverPDCP_r17__F2 (MRB_ToAddMod_r17__recoverPDCP_r17__F1 x) = x. imp_solve. Qed.
Lemma MRB_ToAddMod_r17__recoverPDCP_r17__F2F1 : forall (y : nat) (H : y <= 0), MRB_ToAddMod_r17__recoverPDCP_r17__F1 (MRB_ToAddMod_r17__recoverPDCP_r17__F2 y) = y. enum_solve H y. Qed.

Require Import NR.PDCP_Config.

Opaque PDCP_Config__cond PDCP_Config__Format.

Record MRB_ToAddMod_r17__Type : Set :=
  make__MRB_ToAddMod_r17__Type {
    MRB_ToAddMod_r17__mbs_SessionId_r17 : option TMGI_r17__Type ;
    MRB_ToAddMod_r17__mrb_Identity_r17 : MRB_Identity_r17__Type ;
    MRB_ToAddMod_r17__mrb_IdentityNew_r17 : option MRB_Identity_r17__Type ;
    MRB_ToAddMod_r17__reestablishPDCP_r17 : option MRB_ToAddMod_r17__reestablishPDCP_r17__Type ;
    MRB_ToAddMod_r17__recoverPDCP_r17 : option MRB_ToAddMod_r17__recoverPDCP_r17__Type ;
    MRB_ToAddMod_r17__pdcp_Config_r17 : option PDCP_Config__Type ;
}.
Definition MRB_ToAddMod_r17__root_list : list seq_elem := (
 Opt TMGI_r17__Type TMGI_r17__cond ::
 Nor MRB_Identity_r17__Type MRB_Identity_r17__cond ::
 Opt MRB_Identity_r17__Type MRB_Identity_r17__cond ::
 Opt MRB_ToAddMod_r17__reestablishPDCP_r17__Type MRB_ToAddMod_r17__reestablishPDCP_r17__cond ::
 Opt MRB_ToAddMod_r17__recoverPDCP_r17__Type MRB_ToAddMod_r17__recoverPDCP_r17__cond ::
 Opt PDCP_Config__Type PDCP_Config__cond ::
 nil).
Definition MRB_ToAddMod_r17__ext_list : list typ := (
  nil).
Definition MRB_ToAddMod_r17__cond (z : MRB_ToAddMod_r17__Type) := 
(  opt_cond TMGI_r17__cond (MRB_ToAddMod_r17__mbs_SessionId_r17 z) /\
  MRB_Identity_r17__cond (MRB_ToAddMod_r17__mrb_Identity_r17 z) /\
  opt_cond MRB_Identity_r17__cond (MRB_ToAddMod_r17__mrb_IdentityNew_r17 z) /\
  opt_cond MRB_ToAddMod_r17__reestablishPDCP_r17__cond (MRB_ToAddMod_r17__reestablishPDCP_r17 z) /\
  opt_cond MRB_ToAddMod_r17__recoverPDCP_r17__cond (MRB_ToAddMod_r17__recoverPDCP_r17 z) /\
  opt_cond PDCP_Config__cond (MRB_ToAddMod_r17__pdcp_Config_r17 z) /\
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
Definition MRB_ToAddMod_r17__reestablishPDCP_r17__Format : T_Format MRB_ToAddMod_r17__reestablishPDCP_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRB_ToAddMod_r17__reestablishPDCP_r17__nat__Format MRB_ToAddMod_r17__reestablishPDCP_r17__F1 MRB_ToAddMod_r17__reestablishPDCP_r17__F2 MRB_ToAddMod_r17__reestablishPDCP_r17__F1F2 MRB_ToAddMod_r17__reestablishPDCP_r17__F2F1.

Opaque MRB_ToAddMod_r17__reestablishPDCP_r17__cond MRB_ToAddMod_r17__reestablishPDCP_r17__Format.

Definition MRB_ToAddMod_r17__recoverPDCP_r17__Format : T_Format MRB_ToAddMod_r17__recoverPDCP_r17__Type (fun _ => True) :=
(* Eval compute in *) proj3_format MRB_ToAddMod_r17__recoverPDCP_r17__nat__Format MRB_ToAddMod_r17__recoverPDCP_r17__F1 MRB_ToAddMod_r17__recoverPDCP_r17__F2 MRB_ToAddMod_r17__recoverPDCP_r17__F1F2 MRB_ToAddMod_r17__recoverPDCP_r17__F2F1.

Opaque MRB_ToAddMod_r17__recoverPDCP_r17__cond MRB_ToAddMod_r17__recoverPDCP_r17__Format.


Definition MRB_ToAddMod_r17__root_Format_Type := Eval cbn in seq_format_prod MRB_ToAddMod_r17__root_list.
Definition MRB_ToAddMod_r17__root_Format_list : MRB_ToAddMod_r17__root_Format_Type :=
  (TMGI_r17__Format, (MRB_Identity_r17__Format, (MRB_Identity_r17__Format, (MRB_ToAddMod_r17__reestablishPDCP_r17__Format, (MRB_ToAddMod_r17__recoverPDCP_r17__Format, (PDCP_Config__Format, unit_format)))))).

Definition MRB_ToAddMod_r17__ext_Format_Type := Eval cbn in get_formats MRB_ToAddMod_r17__ext_list.
Definition MRB_ToAddMod_r17__ext_Format_list : MRB_ToAddMod_r17__ext_Format_Type :=
  unit__Format.

Definition MRB_ToAddMod_r17__list_type : Set := (seq_type MRB_ToAddMod_r17__root_list) * (seq_ext_type MRB_ToAddMod_r17__ext_list).
Definition MRB_ToAddMod_r17__list_cond (z : MRB_ToAddMod_r17__list_type) : Prop :=
        (seq_cond MRB_ToAddMod_r17__root_list (fst z)) /\ (seq_ext_cond MRB_ToAddMod_r17__ext_list (snd z)).
Definition MRB_ToAddMod_r17__list_format : T_Format MRB_ToAddMod_r17__list_type MRB_ToAddMod_r17__list_cond :=
 (* Eval compute in *) seq_ext_format MRB_ToAddMod_r17__root_list MRB_ToAddMod_r17__root_Format_list MRB_ToAddMod_r17__ext_list MRB_ToAddMod_r17__ext_Format_list.

Opaque MRB_ToAddMod_r17__list_format.
Definition MRB_ToAddMod_r17__F1 (z : MRB_ToAddMod_r17__Type) : MRB_ToAddMod_r17__list_type :=
  (((MRB_ToAddMod_r17__mbs_SessionId_r17 z, (MRB_ToAddMod_r17__mrb_Identity_r17 z, (MRB_ToAddMod_r17__mrb_IdentityNew_r17 z, (MRB_ToAddMod_r17__reestablishPDCP_r17 z, (MRB_ToAddMod_r17__recoverPDCP_r17 z, (MRB_ToAddMod_r17__pdcp_Config_r17 z, tt))))))), (
tt)).
Definition MRB_ToAddMod_r17__F2 (y : MRB_ToAddMod_r17__list_type) : MRB_ToAddMod_r17__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, _)))))), _)=>
    make__MRB_ToAddMod_r17__Type j0 j1 j2 j3 j4 j5
  end.
Definition MRB_ToAddMod_r17__helper1 : (forall a : MRB_ToAddMod_r17__Type, MRB_ToAddMod_r17__cond a -> MRB_ToAddMod_r17__list_cond (MRB_ToAddMod_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MRB_ToAddMod_r17__helper2 : (forall a : MRB_ToAddMod_r17__Type, MRB_ToAddMod_r17__F2 (MRB_ToAddMod_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MRB_ToAddMod_r17__helper3 : (forall b : MRB_ToAddMod_r17__list_type, MRB_ToAddMod_r17__list_cond b -> MRB_ToAddMod_r17__cond (MRB_ToAddMod_r17__F2 b) /\ MRB_ToAddMod_r17__F1 (MRB_ToAddMod_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MRB_ToAddMod_r17__cond, MRB_ToAddMod_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MRB_ToAddMod_r17__Format : T_Format MRB_ToAddMod_r17__Type MRB_ToAddMod_r17__cond :=
 proj2_format MRB_ToAddMod_r17__cond MRB_ToAddMod_r17__list_format  MRB_ToAddMod_r17__F1 MRB_ToAddMod_r17__F2 MRB_ToAddMod_r17__helper1 MRB_ToAddMod_r17__helper2 MRB_ToAddMod_r17__helper3.

Opaque MRB_ToAddMod_r17__cond MRB_ToAddMod_r17__Format.

