Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Inductive BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Type : Set :=
 | BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__supported
.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__cond := (fun (_ : BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Type) => True).
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__nat__helper.

Definition BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F1 t :=
  match t with
  | BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__supported => 0
  end.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F2 n :=
  match n with
  | 0 => BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__supported
  | _ => BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__supported
  end.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F1F2 : forall x : BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Type, (BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F1 x <= 0) /\ BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F2 (BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F1 (BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Type : Set :=
 | BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__supported
.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__cond := (fun (_ : BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Type) => True).
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__nat__helper.

Definition BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F1 t :=
  match t with
  | BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__supported => 0
  end.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F2 n :=
  match n with
  | 0 => BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__supported
  | _ => BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__supported
  end.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F1F2 : forall x : BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Type, (BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F1 x <= 0) /\ BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F2 (BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F1 x) = x. imp_solve. Qed.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F2F1 : forall (y : nat) (H : y <= 0), BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F1 (BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F2 y) = y. enum_solve H y. Qed.

Inductive BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Type : Set :=
 | BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__supported
.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__cond := (fun (_ : BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Type) => True).
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__nat__helper.

Definition BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F1 t :=
  match t with
  | BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__supported => 0
  end.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F2 n :=
  match n with
  | 0 => BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__supported
  | _ => BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__supported
  end.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F1F2 : forall x : BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Type, (BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F1 x <= 0) /\ BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F2 (BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F1 x) = x. imp_solve. Qed.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F2F1 : forall (y : nat) (H : y <= 0), BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F1 (BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F2 y) = y. enum_solve H y. Qed.

Record BandParametersSidelinkEUTRA_NR_v1630__nr__Type : Set :=
  make__BandParametersSidelinkEUTRA_NR_v1630__nr__Type {
    BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16 : option BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Type ;
    BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16 : option BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Type ;
    BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16 : option BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Type ;
}.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__list := (
 Opt BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Type BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__cond ::
 Opt BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Type BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__cond ::
 Opt BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Type BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__cond ::
 nil).
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__cond z := 
  opt_cond BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__cond (BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16 z) /\
  opt_cond BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__cond (BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16 z) /\
  opt_cond BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__cond (BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16 z) /\
  True.


Inductive BandParametersSidelinkEUTRA_NR_v1630__Type : Set :=
  | BandParametersSidelinkEUTRA_NR_v1630__eutra : unit -> BandParametersSidelinkEUTRA_NR_v1630__Type
  | BandParametersSidelinkEUTRA_NR_v1630__nr : BandParametersSidelinkEUTRA_NR_v1630__nr__Type -> BandParametersSidelinkEUTRA_NR_v1630__Type
.
Definition BandParametersSidelinkEUTRA_NR_v1630__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons BandParametersSidelinkEUTRA_NR_v1630__nr__Type BandParametersSidelinkEUTRA_NR_v1630__nr__cond ::
 nil).
Definition BandParametersSidelinkEUTRA_NR_v1630__cond (c : BandParametersSidelinkEUTRA_NR_v1630__Type) := 
  match c with
  | BandParametersSidelinkEUTRA_NR_v1630__eutra t => (fun _ => True) t 
  | BandParametersSidelinkEUTRA_NR_v1630__nr t => BandParametersSidelinkEUTRA_NR_v1630__nr__cond t 
  end.

Lemma BandParametersSidelinkEUTRA_NR_v1630__len_helper1 : to_bit_sz (length BandParametersSidelinkEUTRA_NR_v1630__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma BandParametersSidelinkEUTRA_NR_v1630__len_helper2 : 2 <= length2 BandParametersSidelinkEUTRA_NR_v1630__list.
 simpl. lia. Qed.

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
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Format : T_Format BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__nat__Format BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F1 BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F2 BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F1F2 BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__F2F1.

Opaque BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__cond BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Format.

Definition BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Format : T_Format BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__nat__Format BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F1 BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F2 BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F1F2 BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__F2F1.

Opaque BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__cond BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Format.

Definition BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Format : T_Format BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__nat__Format BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F1 BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F2 BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F1F2 BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__F2F1.

Opaque BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__cond BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Format.


Definition BandParametersSidelinkEUTRA_NR_v1630__nr__Format_Type := Eval cbn in seq_format_prod BandParametersSidelinkEUTRA_NR_v1630__nr__list.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__Format_list : BandParametersSidelinkEUTRA_NR_v1630__nr__Format_Type :=
  (BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16__Format, (BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16__Format, (BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16__Format, unit_format))).
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__list__Format := (*Eval compute in *) seq_format BandParametersSidelinkEUTRA_NR_v1630__nr__list BandParametersSidelinkEUTRA_NR_v1630__nr__Format_list.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__F1 z :=
  (BandParametersSidelinkEUTRA_NR_v1630__nr__tx_Sidelink_r16 z, (BandParametersSidelinkEUTRA_NR_v1630__nr__rx_Sidelink_r16 z, (BandParametersSidelinkEUTRA_NR_v1630__nr__sl_CrossCarrierScheduling_r16 z, tt))).
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__F2 (y : seq_type BandParametersSidelinkEUTRA_NR_v1630__nr__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__BandParametersSidelinkEUTRA_NR_v1630__nr__Type i0 i1 i2
  end.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__F1F2_cond (z : BandParametersSidelinkEUTRA_NR_v1630__nr__Type)
  : BandParametersSidelinkEUTRA_NR_v1630__nr__cond z ->
  (seq_cond BandParametersSidelinkEUTRA_NR_v1630__nr__list (BandParametersSidelinkEUTRA_NR_v1630__nr__F1 z)).
intro H. unfold BandParametersSidelinkEUTRA_NR_v1630__nr__cond in H. simpl. auto. Qed.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__F1F2_cond2 (z : BandParametersSidelinkEUTRA_NR_v1630__nr__Type)
 : BandParametersSidelinkEUTRA_NR_v1630__nr__F2 (BandParametersSidelinkEUTRA_NR_v1630__nr__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma BandParametersSidelinkEUTRA_NR_v1630__nr__F2F1_cond (y : seq_type BandParametersSidelinkEUTRA_NR_v1630__nr__list)
  : seq_cond BandParametersSidelinkEUTRA_NR_v1630__nr__list y ->
 (BandParametersSidelinkEUTRA_NR_v1630__nr__cond (BandParametersSidelinkEUTRA_NR_v1630__nr__F2 y)) /\  BandParametersSidelinkEUTRA_NR_v1630__nr__F1 (BandParametersSidelinkEUTRA_NR_v1630__nr__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold BandParametersSidelinkEUTRA_NR_v1630__nr__cond. simpl in *. auto.
 - simpl. unfold BandParametersSidelinkEUTRA_NR_v1630__nr__F1. simpl. destruct_all_unit. auto.   Qed.
Definition BandParametersSidelinkEUTRA_NR_v1630__nr__Format : T_Format BandParametersSidelinkEUTRA_NR_v1630__nr__Type BandParametersSidelinkEUTRA_NR_v1630__nr__cond :=
        proj2_format  BandParametersSidelinkEUTRA_NR_v1630__nr__cond BandParametersSidelinkEUTRA_NR_v1630__nr__list__Format
    BandParametersSidelinkEUTRA_NR_v1630__nr__F1 BandParametersSidelinkEUTRA_NR_v1630__nr__F2 BandParametersSidelinkEUTRA_NR_v1630__nr__F1F2_cond  BandParametersSidelinkEUTRA_NR_v1630__nr__F1F2_cond2 BandParametersSidelinkEUTRA_NR_v1630__nr__F2F1_cond.
Opaque BandParametersSidelinkEUTRA_NR_v1630__nr__cond BandParametersSidelinkEUTRA_NR_v1630__nr__Format.


Definition BandParametersSidelinkEUTRA_NR_v1630__Format_Type := Eval cbn in get_formats BandParametersSidelinkEUTRA_NR_v1630__list.
Definition BandParametersSidelinkEUTRA_NR_v1630__Format_list : BandParametersSidelinkEUTRA_NR_v1630__Format_Type :=
  (unit__Format, (BandParametersSidelinkEUTRA_NR_v1630__nr__Format, unit__Format)).
Definition BandParametersSidelinkEUTRA_NR_v1630__list__Format := Eval compute in choice_format BandParametersSidelinkEUTRA_NR_v1630__list BandParametersSidelinkEUTRA_NR_v1630__len_helper1 BandParametersSidelinkEUTRA_NR_v1630__len_helper2  BandParametersSidelinkEUTRA_NR_v1630__Format_list.
Definition BandParametersSidelinkEUTRA_NR_v1630__F1 (z : BandParametersSidelinkEUTRA_NR_v1630__Type) : (choice BandParametersSidelinkEUTRA_NR_v1630__list) :=
  match z with
   | BandParametersSidelinkEUTRA_NR_v1630__eutra t => existT _ 0 t
  | BandParametersSidelinkEUTRA_NR_v1630__nr t => existT _ 1 t
  end.
Definition BandParametersSidelinkEUTRA_NR_v1630__g := (fun n => typ_set (get_nth_typ BandParametersSidelinkEUTRA_NR_v1630__list n)).
Definition BandParametersSidelinkEUTRA_NR_v1630__F2 (y : choice BandParametersSidelinkEUTRA_NR_v1630__list) : BandParametersSidelinkEUTRA_NR_v1630__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (BandParametersSidelinkEUTRA_NR_v1630__g n -> BandParametersSidelinkEUTRA_NR_v1630__Type) with
    | 0 => fun (t : unit) => BandParametersSidelinkEUTRA_NR_v1630__eutra t 
    | 1 => fun (t : BandParametersSidelinkEUTRA_NR_v1630__nr__Type) => BandParametersSidelinkEUTRA_NR_v1630__nr t 
 | (S (S n0)) => (fun (x' : nat) (t'' : BandParametersSidelinkEUTRA_NR_v1630__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ BandParametersSidelinkEUTRA_NR_v1630__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len BandParametersSidelinkEUTRA_NR_v1630__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return BandParametersSidelinkEUTRA_NR_v1630__Type with end) n0
           end t0).

Lemma BandParametersSidelinkEUTRA_NR_v1630__helper2 :  forall (y : BandParametersSidelinkEUTRA_NR_v1630__Type), BandParametersSidelinkEUTRA_NR_v1630__cond y -> choice_cond BandParametersSidelinkEUTRA_NR_v1630__list (BandParametersSidelinkEUTRA_NR_v1630__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma BandParametersSidelinkEUTRA_NR_v1630__helper3 :  forall (y : BandParametersSidelinkEUTRA_NR_v1630__Type), BandParametersSidelinkEUTRA_NR_v1630__F2 (BandParametersSidelinkEUTRA_NR_v1630__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma BandParametersSidelinkEUTRA_NR_v1630__helper4 : (forall b : choice BandParametersSidelinkEUTRA_NR_v1630__list, choice_cond BandParametersSidelinkEUTRA_NR_v1630__list b -> BandParametersSidelinkEUTRA_NR_v1630__cond (BandParametersSidelinkEUTRA_NR_v1630__F2 b) /\ BandParametersSidelinkEUTRA_NR_v1630__F1 (BandParametersSidelinkEUTRA_NR_v1630__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length BandParametersSidelinkEUTRA_NR_v1630__F1 BandParametersSidelinkEUTRA_NR_v1630__F2.
Definition BandParametersSidelinkEUTRA_NR_v1630__Format : T_Format BandParametersSidelinkEUTRA_NR_v1630__Type BandParametersSidelinkEUTRA_NR_v1630__cond :=
  (* Eval compute in *) proj2_format BandParametersSidelinkEUTRA_NR_v1630__cond BandParametersSidelinkEUTRA_NR_v1630__list__Format BandParametersSidelinkEUTRA_NR_v1630__F1 BandParametersSidelinkEUTRA_NR_v1630__F2 BandParametersSidelinkEUTRA_NR_v1630__helper2 BandParametersSidelinkEUTRA_NR_v1630__helper3 BandParametersSidelinkEUTRA_NR_v1630__helper4.
Opaque BandParametersSidelinkEUTRA_NR_v1630__cond BandParametersSidelinkEUTRA_NR_v1630__Format.

