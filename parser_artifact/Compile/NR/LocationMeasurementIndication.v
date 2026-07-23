Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.LocationMeasurementIndication_IEs.

Opaque LocationMeasurementIndication_IEs__cond LocationMeasurementIndication_IEs__Format.

Record LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type : Set := make__LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type {}.
Definition LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__cond (z : LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type) := True.

Inductive LocationMeasurementIndication__criticalExtensions__Type : Set :=
  | LocationMeasurementIndication__criticalExtensions__locationMeasurementIndication : LocationMeasurementIndication_IEs__Type -> LocationMeasurementIndication__criticalExtensions__Type
  | LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture : LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type -> LocationMeasurementIndication__criticalExtensions__Type
.
Definition LocationMeasurementIndication__criticalExtensions__list : list typ := (
typ_cons LocationMeasurementIndication_IEs__Type LocationMeasurementIndication_IEs__cond ::
typ_cons LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__cond ::
 nil).
Definition LocationMeasurementIndication__criticalExtensions__cond (c : LocationMeasurementIndication__criticalExtensions__Type) := 
  match c with
  | LocationMeasurementIndication__criticalExtensions__locationMeasurementIndication t => LocationMeasurementIndication_IEs__cond t 
  | LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture t => LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__cond t 
  end.

Lemma LocationMeasurementIndication__criticalExtensions__len_helper1 : to_bit_sz (length LocationMeasurementIndication__criticalExtensions__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma LocationMeasurementIndication__criticalExtensions__len_helper2 : 2 <= length2 LocationMeasurementIndication__criticalExtensions__list.
 simpl. lia. Qed.
Record LocationMeasurementIndication__Type : Set :=
  make__LocationMeasurementIndication__Type {
    LocationMeasurementIndication__criticalExtensions : LocationMeasurementIndication__criticalExtensions__Type ;
}.
Definition LocationMeasurementIndication__list := (
 Nor LocationMeasurementIndication__criticalExtensions__Type LocationMeasurementIndication__criticalExtensions__cond ::
 nil).
Definition LocationMeasurementIndication__cond z := 
  LocationMeasurementIndication__criticalExtensions__cond (LocationMeasurementIndication__criticalExtensions z) /\
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
Definition LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__helper : forall a : LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type, True -> True /\ make__LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type = a.
  eq_unit_helper_tact. Qed.
Definition LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Format : T_Format LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type)
    LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__helper unit_unique (fun _ => left I).

Opaque LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__cond LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Format.


Definition LocationMeasurementIndication__criticalExtensions__Format_Type := Eval cbn in get_formats LocationMeasurementIndication__criticalExtensions__list.
Definition LocationMeasurementIndication__criticalExtensions__Format_list : LocationMeasurementIndication__criticalExtensions__Format_Type :=
  (LocationMeasurementIndication_IEs__Format, (LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Format, unit__Format)).
Definition LocationMeasurementIndication__criticalExtensions__list__Format := Eval compute in choice_format LocationMeasurementIndication__criticalExtensions__list LocationMeasurementIndication__criticalExtensions__len_helper1 LocationMeasurementIndication__criticalExtensions__len_helper2  LocationMeasurementIndication__criticalExtensions__Format_list.
Definition LocationMeasurementIndication__criticalExtensions__F1 (z : LocationMeasurementIndication__criticalExtensions__Type) : (choice LocationMeasurementIndication__criticalExtensions__list) :=
  match z with
   | LocationMeasurementIndication__criticalExtensions__locationMeasurementIndication t => existT _ 0 t
  | LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture t => existT _ 1 t
  end.
Definition LocationMeasurementIndication__criticalExtensions__g := (fun n => typ_set (get_nth_typ LocationMeasurementIndication__criticalExtensions__list n)).
Definition LocationMeasurementIndication__criticalExtensions__F2 (y : choice LocationMeasurementIndication__criticalExtensions__list) : LocationMeasurementIndication__criticalExtensions__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (LocationMeasurementIndication__criticalExtensions__g n -> LocationMeasurementIndication__criticalExtensions__Type) with
    | 0 => fun (t : LocationMeasurementIndication_IEs__Type) => LocationMeasurementIndication__criticalExtensions__locationMeasurementIndication t 
    | 1 => fun (t : LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture__Type) => LocationMeasurementIndication__criticalExtensions__criticalExtensionsFuture t 
 | (S (S n0)) => (fun (x' : nat) (t'' : LocationMeasurementIndication__criticalExtensions__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ LocationMeasurementIndication__criticalExtensions__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len LocationMeasurementIndication__criticalExtensions__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return LocationMeasurementIndication__criticalExtensions__Type with end) n0
           end t0).

Lemma LocationMeasurementIndication__criticalExtensions__helper2 :  forall (y : LocationMeasurementIndication__criticalExtensions__Type), LocationMeasurementIndication__criticalExtensions__cond y -> choice_cond LocationMeasurementIndication__criticalExtensions__list (LocationMeasurementIndication__criticalExtensions__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma LocationMeasurementIndication__criticalExtensions__helper3 :  forall (y : LocationMeasurementIndication__criticalExtensions__Type), LocationMeasurementIndication__criticalExtensions__F2 (LocationMeasurementIndication__criticalExtensions__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma LocationMeasurementIndication__criticalExtensions__helper4 : (forall b : choice LocationMeasurementIndication__criticalExtensions__list, choice_cond LocationMeasurementIndication__criticalExtensions__list b -> LocationMeasurementIndication__criticalExtensions__cond (LocationMeasurementIndication__criticalExtensions__F2 b) /\ LocationMeasurementIndication__criticalExtensions__F1 (LocationMeasurementIndication__criticalExtensions__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length LocationMeasurementIndication__criticalExtensions__F1 LocationMeasurementIndication__criticalExtensions__F2.
Definition LocationMeasurementIndication__criticalExtensions__Format : T_Format LocationMeasurementIndication__criticalExtensions__Type LocationMeasurementIndication__criticalExtensions__cond :=
  (* Eval compute in *) proj2_format LocationMeasurementIndication__criticalExtensions__cond LocationMeasurementIndication__criticalExtensions__list__Format LocationMeasurementIndication__criticalExtensions__F1 LocationMeasurementIndication__criticalExtensions__F2 LocationMeasurementIndication__criticalExtensions__helper2 LocationMeasurementIndication__criticalExtensions__helper3 LocationMeasurementIndication__criticalExtensions__helper4.
Opaque LocationMeasurementIndication__criticalExtensions__cond LocationMeasurementIndication__criticalExtensions__Format.


Definition LocationMeasurementIndication__Format_Type := Eval cbn in seq_format_prod LocationMeasurementIndication__list.
Definition LocationMeasurementIndication__Format_list : LocationMeasurementIndication__Format_Type :=
  (LocationMeasurementIndication__criticalExtensions__Format, unit_format).
Definition LocationMeasurementIndication__list__Format := (*Eval compute in *) seq_format LocationMeasurementIndication__list LocationMeasurementIndication__Format_list.
Definition LocationMeasurementIndication__F1 z :=
  (LocationMeasurementIndication__criticalExtensions z, tt).
Definition LocationMeasurementIndication__F2 (y : seq_type LocationMeasurementIndication__list) :=
  match y with
  | (i0, _)=>
    make__LocationMeasurementIndication__Type i0
  end.
Lemma LocationMeasurementIndication__F1F2_cond (z : LocationMeasurementIndication__Type)
  : LocationMeasurementIndication__cond z ->
  (seq_cond LocationMeasurementIndication__list (LocationMeasurementIndication__F1 z)).
intro H. unfold LocationMeasurementIndication__cond in H. simpl. auto. Qed.
Lemma LocationMeasurementIndication__F1F2_cond2 (z : LocationMeasurementIndication__Type)
 : LocationMeasurementIndication__F2 (LocationMeasurementIndication__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma LocationMeasurementIndication__F2F1_cond (y : seq_type LocationMeasurementIndication__list)
  : seq_cond LocationMeasurementIndication__list y ->
 (LocationMeasurementIndication__cond (LocationMeasurementIndication__F2 y)) /\  LocationMeasurementIndication__F1 (LocationMeasurementIndication__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold LocationMeasurementIndication__cond. simpl in *. auto.
 - simpl. unfold LocationMeasurementIndication__F1. simpl. destruct_all_unit. auto.   Qed.
Definition LocationMeasurementIndication__Format : T_Format LocationMeasurementIndication__Type LocationMeasurementIndication__cond :=
        proj2_format  LocationMeasurementIndication__cond LocationMeasurementIndication__list__Format
    LocationMeasurementIndication__F1 LocationMeasurementIndication__F2 LocationMeasurementIndication__F1F2_cond  LocationMeasurementIndication__F1F2_cond2 LocationMeasurementIndication__F2F1_cond.
Opaque LocationMeasurementIndication__cond LocationMeasurementIndication__Format.

