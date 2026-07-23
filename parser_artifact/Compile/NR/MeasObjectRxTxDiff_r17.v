Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.

Inductive MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type : Set :=
  | MeasObjectRxTxDiff_r17__dl_Ref_r17__root__prs_Ref_r17 : unit -> MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type
  | MeasObjectRxTxDiff_r17__dl_Ref_r17__root__csi_RS_Ref_r17 : unit -> MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type
.
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__cond (c : MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type) := 
  match c with
  | MeasObjectRxTxDiff_r17__dl_Ref_r17__root__prs_Ref_r17 t => (fun _ => True) t 
  | MeasObjectRxTxDiff_r17__dl_Ref_r17__root__csi_RS_Ref_r17 t => (fun _ => True) t 
  end.

Lemma MeasObjectRxTxDiff_r17__dl_Ref_r17__root__len_helper1 : to_bit_sz (length MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma MeasObjectRxTxDiff_r17__dl_Ref_r17__root__len_helper2 : 2 <= length2 MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list.
 simpl. lia. Qed.

Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__Type : Set := Empty_set.
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__cond (c : MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__Type) := True.
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__Type : Set := MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type + MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__Type.
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__cond :=
  sum_cond MeasObjectRxTxDiff_r17__dl_Ref_r17__root__cond MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__cond.
Record MeasObjectRxTxDiff_r17__Type : Set :=
  make__MeasObjectRxTxDiff_r17__Type {
    MeasObjectRxTxDiff_r17__dl_Ref_r17 : option MeasObjectRxTxDiff_r17__dl_Ref_r17__Type ;
}.
Definition MeasObjectRxTxDiff_r17__root_list : list seq_elem := (
 Opt MeasObjectRxTxDiff_r17__dl_Ref_r17__Type MeasObjectRxTxDiff_r17__dl_Ref_r17__cond ::
 nil).
Definition MeasObjectRxTxDiff_r17__ext_list : list typ := (
  nil).
Definition MeasObjectRxTxDiff_r17__cond (z : MeasObjectRxTxDiff_r17__Type) := 
(  opt_cond MeasObjectRxTxDiff_r17__dl_Ref_r17__cond (MeasObjectRxTxDiff_r17__dl_Ref_r17 z) /\
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

Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Format_Type := Eval cbn in get_formats MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list.
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Format_list : MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Format_Type :=
  (unit__Format, (unit__Format, unit__Format)).
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list__Format := Eval compute in choice_format MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list MeasObjectRxTxDiff_r17__dl_Ref_r17__root__len_helper1 MeasObjectRxTxDiff_r17__dl_Ref_r17__root__len_helper2  MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Format_list.
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F1 (z : MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type) : (choice MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list) :=
  match z with
   | MeasObjectRxTxDiff_r17__dl_Ref_r17__root__prs_Ref_r17 t => existT _ 0 t
  | MeasObjectRxTxDiff_r17__dl_Ref_r17__root__csi_RS_Ref_r17 t => existT _ 1 t
  end.
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__g := (fun n => typ_set (get_nth_typ MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list n)).
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F2 (y : choice MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list) : MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (MeasObjectRxTxDiff_r17__dl_Ref_r17__root__g n -> MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type) with
    | 0 => fun (t : unit) => MeasObjectRxTxDiff_r17__dl_Ref_r17__root__prs_Ref_r17 t 
    | 1 => fun (t : unit) => MeasObjectRxTxDiff_r17__dl_Ref_r17__root__csi_RS_Ref_r17 t 
 | (S (S n0)) => (fun (x' : nat) (t'' : MeasObjectRxTxDiff_r17__dl_Ref_r17__root__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type with end) n0
           end t0).

Lemma MeasObjectRxTxDiff_r17__dl_Ref_r17__root__helper2 :  forall (y : MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type), MeasObjectRxTxDiff_r17__dl_Ref_r17__root__cond y -> choice_cond MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list (MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma MeasObjectRxTxDiff_r17__dl_Ref_r17__root__helper3 :  forall (y : MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type), MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F2 (MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma MeasObjectRxTxDiff_r17__dl_Ref_r17__root__helper4 : (forall b : choice MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list, choice_cond MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list b -> MeasObjectRxTxDiff_r17__dl_Ref_r17__root__cond (MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F2 b) /\ MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F1 (MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F1 MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F2.
Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Format : T_Format MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Type MeasObjectRxTxDiff_r17__dl_Ref_r17__root__cond :=
  (* Eval compute in *) proj2_format MeasObjectRxTxDiff_r17__dl_Ref_r17__root__cond MeasObjectRxTxDiff_r17__dl_Ref_r17__root__list__Format MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F1 MeasObjectRxTxDiff_r17__dl_Ref_r17__root__F2 MeasObjectRxTxDiff_r17__dl_Ref_r17__root__helper2 MeasObjectRxTxDiff_r17__dl_Ref_r17__root__helper3 MeasObjectRxTxDiff_r17__dl_Ref_r17__root__helper4.
Opaque MeasObjectRxTxDiff_r17__dl_Ref_r17__root__cond MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Format.

Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__Format : T_Format MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__Type MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__cond := empty_format.
Opaque MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__cond MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__Format.

Definition MeasObjectRxTxDiff_r17__dl_Ref_r17__Format : T_Format MeasObjectRxTxDiff_r17__dl_Ref_r17__Type MeasObjectRxTxDiff_r17__dl_Ref_r17__cond := sum_format MeasObjectRxTxDiff_r17__dl_Ref_r17__root__Format MeasObjectRxTxDiff_r17__dl_Ref_r17__ext__Format.
Opaque MeasObjectRxTxDiff_r17__dl_Ref_r17__cond MeasObjectRxTxDiff_r17__dl_Ref_r17__Format.


Definition MeasObjectRxTxDiff_r17__root_Format_Type := Eval cbn in seq_format_prod MeasObjectRxTxDiff_r17__root_list.
Definition MeasObjectRxTxDiff_r17__root_Format_list : MeasObjectRxTxDiff_r17__root_Format_Type :=
  (MeasObjectRxTxDiff_r17__dl_Ref_r17__Format, unit_format).

Definition MeasObjectRxTxDiff_r17__ext_Format_Type := Eval cbn in get_formats MeasObjectRxTxDiff_r17__ext_list.
Definition MeasObjectRxTxDiff_r17__ext_Format_list : MeasObjectRxTxDiff_r17__ext_Format_Type :=
  unit__Format.

Definition MeasObjectRxTxDiff_r17__list_type : Set := (seq_type MeasObjectRxTxDiff_r17__root_list) * (seq_ext_type MeasObjectRxTxDiff_r17__ext_list).
Definition MeasObjectRxTxDiff_r17__list_cond (z : MeasObjectRxTxDiff_r17__list_type) : Prop :=
        (seq_cond MeasObjectRxTxDiff_r17__root_list (fst z)) /\ (seq_ext_cond MeasObjectRxTxDiff_r17__ext_list (snd z)).
Definition MeasObjectRxTxDiff_r17__list_format : T_Format MeasObjectRxTxDiff_r17__list_type MeasObjectRxTxDiff_r17__list_cond :=
 (* Eval compute in *) seq_ext_format MeasObjectRxTxDiff_r17__root_list MeasObjectRxTxDiff_r17__root_Format_list MeasObjectRxTxDiff_r17__ext_list MeasObjectRxTxDiff_r17__ext_Format_list.

Opaque MeasObjectRxTxDiff_r17__list_format.
Definition MeasObjectRxTxDiff_r17__F1 (z : MeasObjectRxTxDiff_r17__Type) : MeasObjectRxTxDiff_r17__list_type :=
  (((MeasObjectRxTxDiff_r17__dl_Ref_r17 z, tt)), (
tt)).
Definition MeasObjectRxTxDiff_r17__F2 (y : MeasObjectRxTxDiff_r17__list_type) : MeasObjectRxTxDiff_r17__Type :=
  match y with
  | ((j0, _), _)=>
    make__MeasObjectRxTxDiff_r17__Type j0
  end.
Definition MeasObjectRxTxDiff_r17__helper1 : (forall a : MeasObjectRxTxDiff_r17__Type, MeasObjectRxTxDiff_r17__cond a -> MeasObjectRxTxDiff_r17__list_cond (MeasObjectRxTxDiff_r17__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasObjectRxTxDiff_r17__helper2 : (forall a : MeasObjectRxTxDiff_r17__Type, MeasObjectRxTxDiff_r17__F2 (MeasObjectRxTxDiff_r17__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasObjectRxTxDiff_r17__helper3 : (forall b : MeasObjectRxTxDiff_r17__list_type, MeasObjectRxTxDiff_r17__list_cond b -> MeasObjectRxTxDiff_r17__cond (MeasObjectRxTxDiff_r17__F2 b) /\ MeasObjectRxTxDiff_r17__F1 (MeasObjectRxTxDiff_r17__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasObjectRxTxDiff_r17__cond, MeasObjectRxTxDiff_r17__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasObjectRxTxDiff_r17__Format : T_Format MeasObjectRxTxDiff_r17__Type MeasObjectRxTxDiff_r17__cond :=
 proj2_format MeasObjectRxTxDiff_r17__cond MeasObjectRxTxDiff_r17__list_format  MeasObjectRxTxDiff_r17__F1 MeasObjectRxTxDiff_r17__F2 MeasObjectRxTxDiff_r17__helper1 MeasObjectRxTxDiff_r17__helper2 MeasObjectRxTxDiff_r17__helper3.

Opaque MeasObjectRxTxDiff_r17__cond MeasObjectRxTxDiff_r17__Format.

