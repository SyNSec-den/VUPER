Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__Type := bit_string_fixed.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 4 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__Type := bit_string_fixed.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 12 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__Type := bit_string_fixed.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 3 /\ bit_string_len_prop (fst z) (snd z)).
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__other__Type := bit_string_fixed.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__other__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 6 /\ bit_string_len_prop (fst z) (snd z)).

Inductive CSI_RS_ResourceMapping__frequencyDomainAllocation__Type : Set :=
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__row1 : CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__Type -> CSI_RS_ResourceMapping__frequencyDomainAllocation__Type
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__row2 : CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__Type -> CSI_RS_ResourceMapping__frequencyDomainAllocation__Type
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__row4 : CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__Type -> CSI_RS_ResourceMapping__frequencyDomainAllocation__Type
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__other : CSI_RS_ResourceMapping__frequencyDomainAllocation__other__Type -> CSI_RS_ResourceMapping__frequencyDomainAllocation__Type
.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__list : list typ := (
typ_cons CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__cond ::
typ_cons CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__cond ::
typ_cons CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__cond ::
typ_cons CSI_RS_ResourceMapping__frequencyDomainAllocation__other__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__other__cond ::
 nil).
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__cond (c : CSI_RS_ResourceMapping__frequencyDomainAllocation__Type) := 
  match c with
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__row1 t => CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__cond t 
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__row2 t => CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__cond t 
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__row4 t => CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__cond t 
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__other t => CSI_RS_ResourceMapping__frequencyDomainAllocation__other__cond t 
  end.

Lemma CSI_RS_ResourceMapping__frequencyDomainAllocation__len_helper1 : to_bit_sz (length CSI_RS_ResourceMapping__frequencyDomainAllocation__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_RS_ResourceMapping__frequencyDomainAllocation__len_helper2 : 2 <= length2 CSI_RS_ResourceMapping__frequencyDomainAllocation__list.
 simpl. lia. Qed.
Inductive CSI_RS_ResourceMapping__nrofPorts__Type : Set :=
 | CSI_RS_ResourceMapping__nrofPorts__p1
 | CSI_RS_ResourceMapping__nrofPorts__p2
 | CSI_RS_ResourceMapping__nrofPorts__p4
 | CSI_RS_ResourceMapping__nrofPorts__p8
 | CSI_RS_ResourceMapping__nrofPorts__p12
 | CSI_RS_ResourceMapping__nrofPorts__p16
 | CSI_RS_ResourceMapping__nrofPorts__p24
 | CSI_RS_ResourceMapping__nrofPorts__p32
.
Definition CSI_RS_ResourceMapping__nrofPorts__cond := (fun (_ : CSI_RS_ResourceMapping__nrofPorts__Type) => True).
Lemma CSI_RS_ResourceMapping__nrofPorts__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_RS_ResourceMapping__nrofPorts__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CSI_RS_ResourceMapping__nrofPorts__nat__helper.

Definition CSI_RS_ResourceMapping__nrofPorts__F1 t :=
  match t with
  | CSI_RS_ResourceMapping__nrofPorts__p1 => 0
  | CSI_RS_ResourceMapping__nrofPorts__p2 => 1
  | CSI_RS_ResourceMapping__nrofPorts__p4 => 2
  | CSI_RS_ResourceMapping__nrofPorts__p8 => 3
  | CSI_RS_ResourceMapping__nrofPorts__p12 => 4
  | CSI_RS_ResourceMapping__nrofPorts__p16 => 5
  | CSI_RS_ResourceMapping__nrofPorts__p24 => 6
  | CSI_RS_ResourceMapping__nrofPorts__p32 => 7
  end.
Definition CSI_RS_ResourceMapping__nrofPorts__F2 n :=
  match n with
  | 0 => CSI_RS_ResourceMapping__nrofPorts__p1
  | 1 => CSI_RS_ResourceMapping__nrofPorts__p2
  | 2 => CSI_RS_ResourceMapping__nrofPorts__p4
  | 3 => CSI_RS_ResourceMapping__nrofPorts__p8
  | 4 => CSI_RS_ResourceMapping__nrofPorts__p12
  | 5 => CSI_RS_ResourceMapping__nrofPorts__p16
  | 6 => CSI_RS_ResourceMapping__nrofPorts__p24
  | 7 => CSI_RS_ResourceMapping__nrofPorts__p32
  | _ => CSI_RS_ResourceMapping__nrofPorts__p1
  end.
Lemma CSI_RS_ResourceMapping__nrofPorts__F1F2 : forall x : CSI_RS_ResourceMapping__nrofPorts__Type, (CSI_RS_ResourceMapping__nrofPorts__F1 x <= 7) /\ CSI_RS_ResourceMapping__nrofPorts__F2 (CSI_RS_ResourceMapping__nrofPorts__F1 x) = x. imp_solve. Qed.
Lemma CSI_RS_ResourceMapping__nrofPorts__F2F1 : forall (y : nat) (H : y <= 7), CSI_RS_ResourceMapping__nrofPorts__F1 (CSI_RS_ResourceMapping__nrofPorts__F2 y) = y. enum_solve H y. Qed.

Lemma CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__helper1 : (0 <= 13)%Z.  lia. Qed.
Lemma CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__helper2 : to_bit_sz (Z.to_nat (13 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (13 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__Type := Z.
Definition CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__cond := (fun z => (0 <= z <= 13)%Z).
Lemma CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__helper1 : (2 <= 12)%Z.  lia. Qed.
Lemma CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__helper2 : to_bit_sz (Z.to_nat (12 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (12 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__Type := Z.
Definition CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__cond := (fun z => (2 <= z <= 12)%Z).
Inductive CSI_RS_ResourceMapping__cdm_Type__Type : Set :=
 | CSI_RS_ResourceMapping__cdm_Type__noCDM
 | CSI_RS_ResourceMapping__cdm_Type__fd_CDM2
 | CSI_RS_ResourceMapping__cdm_Type__cdm4_FD2_TD2
 | CSI_RS_ResourceMapping__cdm_Type__cdm8_FD2_TD4
.
Definition CSI_RS_ResourceMapping__cdm_Type__cond := (fun (_ : CSI_RS_ResourceMapping__cdm_Type__Type) => True).
Lemma CSI_RS_ResourceMapping__cdm_Type__nat__helper : to_bit_sz 3 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_RS_ResourceMapping__cdm_Type__nat__Format : T_Format nat (fun z => (z <= 3)) :=
  nat_enum_format 3 CSI_RS_ResourceMapping__cdm_Type__nat__helper.

Definition CSI_RS_ResourceMapping__cdm_Type__F1 t :=
  match t with
  | CSI_RS_ResourceMapping__cdm_Type__noCDM => 0
  | CSI_RS_ResourceMapping__cdm_Type__fd_CDM2 => 1
  | CSI_RS_ResourceMapping__cdm_Type__cdm4_FD2_TD2 => 2
  | CSI_RS_ResourceMapping__cdm_Type__cdm8_FD2_TD4 => 3
  end.
Definition CSI_RS_ResourceMapping__cdm_Type__F2 n :=
  match n with
  | 0 => CSI_RS_ResourceMapping__cdm_Type__noCDM
  | 1 => CSI_RS_ResourceMapping__cdm_Type__fd_CDM2
  | 2 => CSI_RS_ResourceMapping__cdm_Type__cdm4_FD2_TD2
  | 3 => CSI_RS_ResourceMapping__cdm_Type__cdm8_FD2_TD4
  | _ => CSI_RS_ResourceMapping__cdm_Type__noCDM
  end.
Lemma CSI_RS_ResourceMapping__cdm_Type__F1F2 : forall x : CSI_RS_ResourceMapping__cdm_Type__Type, (CSI_RS_ResourceMapping__cdm_Type__F1 x <= 3) /\ CSI_RS_ResourceMapping__cdm_Type__F2 (CSI_RS_ResourceMapping__cdm_Type__F1 x) = x. imp_solve. Qed.
Lemma CSI_RS_ResourceMapping__cdm_Type__F2F1 : forall (y : nat) (H : y <= 3), CSI_RS_ResourceMapping__cdm_Type__F1 (CSI_RS_ResourceMapping__cdm_Type__F2 y) = y. enum_solve H y. Qed.

Inductive CSI_RS_ResourceMapping__density__dot5__Type : Set :=
 | CSI_RS_ResourceMapping__density__dot5__evenPRBs
 | CSI_RS_ResourceMapping__density__dot5__oddPRBs
.
Definition CSI_RS_ResourceMapping__density__dot5__cond := (fun (_ : CSI_RS_ResourceMapping__density__dot5__Type) => True).
Lemma CSI_RS_ResourceMapping__density__dot5__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CSI_RS_ResourceMapping__density__dot5__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 CSI_RS_ResourceMapping__density__dot5__nat__helper.

Definition CSI_RS_ResourceMapping__density__dot5__F1 t :=
  match t with
  | CSI_RS_ResourceMapping__density__dot5__evenPRBs => 0
  | CSI_RS_ResourceMapping__density__dot5__oddPRBs => 1
  end.
Definition CSI_RS_ResourceMapping__density__dot5__F2 n :=
  match n with
  | 0 => CSI_RS_ResourceMapping__density__dot5__evenPRBs
  | 1 => CSI_RS_ResourceMapping__density__dot5__oddPRBs
  | _ => CSI_RS_ResourceMapping__density__dot5__evenPRBs
  end.
Lemma CSI_RS_ResourceMapping__density__dot5__F1F2 : forall x : CSI_RS_ResourceMapping__density__dot5__Type, (CSI_RS_ResourceMapping__density__dot5__F1 x <= 1) /\ CSI_RS_ResourceMapping__density__dot5__F2 (CSI_RS_ResourceMapping__density__dot5__F1 x) = x. imp_solve. Qed.
Lemma CSI_RS_ResourceMapping__density__dot5__F2F1 : forall (y : nat) (H : y <= 1), CSI_RS_ResourceMapping__density__dot5__F1 (CSI_RS_ResourceMapping__density__dot5__F2 y) = y. enum_solve H y. Qed.


Inductive CSI_RS_ResourceMapping__density__Type : Set :=
  | CSI_RS_ResourceMapping__density__dot5 : CSI_RS_ResourceMapping__density__dot5__Type -> CSI_RS_ResourceMapping__density__Type
  | CSI_RS_ResourceMapping__density__one : unit -> CSI_RS_ResourceMapping__density__Type
  | CSI_RS_ResourceMapping__density__three : unit -> CSI_RS_ResourceMapping__density__Type
  | CSI_RS_ResourceMapping__density__spare : unit -> CSI_RS_ResourceMapping__density__Type
.
Definition CSI_RS_ResourceMapping__density__list : list typ := (
typ_cons CSI_RS_ResourceMapping__density__dot5__Type CSI_RS_ResourceMapping__density__dot5__cond ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
typ_cons unit (fun _ => True) ::
 nil).
Definition CSI_RS_ResourceMapping__density__cond (c : CSI_RS_ResourceMapping__density__Type) := 
  match c with
  | CSI_RS_ResourceMapping__density__dot5 t => CSI_RS_ResourceMapping__density__dot5__cond t 
  | CSI_RS_ResourceMapping__density__one t => (fun _ => True) t 
  | CSI_RS_ResourceMapping__density__three t => (fun _ => True) t 
  | CSI_RS_ResourceMapping__density__spare t => (fun _ => True) t 
  end.

Lemma CSI_RS_ResourceMapping__density__len_helper1 : to_bit_sz (length CSI_RS_ResourceMapping__density__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma CSI_RS_ResourceMapping__density__len_helper2 : 2 <= length2 CSI_RS_ResourceMapping__density__list.
 simpl. lia. Qed.
Require Import NR.CSI_FrequencyOccupation.

Opaque CSI_FrequencyOccupation__cond CSI_FrequencyOccupation__Format.

Record CSI_RS_ResourceMapping__Type : Set :=
  make__CSI_RS_ResourceMapping__Type {
    CSI_RS_ResourceMapping__frequencyDomainAllocation : CSI_RS_ResourceMapping__frequencyDomainAllocation__Type ;
    CSI_RS_ResourceMapping__nrofPorts : CSI_RS_ResourceMapping__nrofPorts__Type ;
    CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain : Z ;
    CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2 : option Z ;
    CSI_RS_ResourceMapping__cdm_Type : CSI_RS_ResourceMapping__cdm_Type__Type ;
    CSI_RS_ResourceMapping__density : CSI_RS_ResourceMapping__density__Type ;
    CSI_RS_ResourceMapping__freqBand : CSI_FrequencyOccupation__Type ;
}.
Definition CSI_RS_ResourceMapping__root_list : list seq_elem := (
 Nor CSI_RS_ResourceMapping__frequencyDomainAllocation__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__cond ::
 Nor CSI_RS_ResourceMapping__nrofPorts__Type CSI_RS_ResourceMapping__nrofPorts__cond ::
 Nor Z CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__cond ::
 Opt Z CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__cond ::
 Nor CSI_RS_ResourceMapping__cdm_Type__Type CSI_RS_ResourceMapping__cdm_Type__cond ::
 Nor CSI_RS_ResourceMapping__density__Type CSI_RS_ResourceMapping__density__cond ::
 Nor CSI_FrequencyOccupation__Type CSI_FrequencyOccupation__cond ::
 nil).
Definition CSI_RS_ResourceMapping__ext_list : list typ := (
  nil).
Definition CSI_RS_ResourceMapping__cond (z : CSI_RS_ResourceMapping__Type) := 
(  CSI_RS_ResourceMapping__frequencyDomainAllocation__cond (CSI_RS_ResourceMapping__frequencyDomainAllocation z) /\
  CSI_RS_ResourceMapping__nrofPorts__cond (CSI_RS_ResourceMapping__nrofPorts z) /\
  CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__cond (CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain z) /\
  opt_cond CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__cond (CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2 z) /\
  CSI_RS_ResourceMapping__cdm_Type__cond (CSI_RS_ResourceMapping__cdm_Type z) /\
  CSI_RS_ResourceMapping__density__cond (CSI_RS_ResourceMapping__density z) /\
  CSI_FrequencyOccupation__cond (CSI_RS_ResourceMapping__freqBand z) /\
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
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__Format : T_Format CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__cond := (* Eval compute in *) bit_string_fixed_format 4.
Opaque CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__cond CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__Format.

Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__Format : T_Format CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__cond := (* Eval compute in *) bit_string_fixed_format 12.
Opaque CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__cond CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__Format.

Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__Format : T_Format CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__cond := (* Eval compute in *) bit_string_fixed_format 3.
Opaque CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__cond CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__Format.

Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__other__Format : T_Format CSI_RS_ResourceMapping__frequencyDomainAllocation__other__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__other__cond := (* Eval compute in *) bit_string_fixed_format 6.
Opaque CSI_RS_ResourceMapping__frequencyDomainAllocation__other__cond CSI_RS_ResourceMapping__frequencyDomainAllocation__other__Format.


Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__Format_Type := Eval cbn in get_formats CSI_RS_ResourceMapping__frequencyDomainAllocation__list.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__Format_list : CSI_RS_ResourceMapping__frequencyDomainAllocation__Format_Type :=
  (CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__Format, (CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__Format, (CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__Format, (CSI_RS_ResourceMapping__frequencyDomainAllocation__other__Format, unit__Format)))).
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__list__Format := Eval compute in choice_format CSI_RS_ResourceMapping__frequencyDomainAllocation__list CSI_RS_ResourceMapping__frequencyDomainAllocation__len_helper1 CSI_RS_ResourceMapping__frequencyDomainAllocation__len_helper2  CSI_RS_ResourceMapping__frequencyDomainAllocation__Format_list.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__F1 (z : CSI_RS_ResourceMapping__frequencyDomainAllocation__Type) : (choice CSI_RS_ResourceMapping__frequencyDomainAllocation__list) :=
  match z with
   | CSI_RS_ResourceMapping__frequencyDomainAllocation__row1 t => existT _ 0 t
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__row2 t => existT _ 1 t
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__row4 t => existT _ 2 t
  | CSI_RS_ResourceMapping__frequencyDomainAllocation__other t => existT _ 3 t
  end.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__g := (fun n => typ_set (get_nth_typ CSI_RS_ResourceMapping__frequencyDomainAllocation__list n)).
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__F2 (y : choice CSI_RS_ResourceMapping__frequencyDomainAllocation__list) : CSI_RS_ResourceMapping__frequencyDomainAllocation__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_RS_ResourceMapping__frequencyDomainAllocation__g n -> CSI_RS_ResourceMapping__frequencyDomainAllocation__Type) with
    | 0 => fun (t : CSI_RS_ResourceMapping__frequencyDomainAllocation__row1__Type) => CSI_RS_ResourceMapping__frequencyDomainAllocation__row1 t 
    | 1 => fun (t : CSI_RS_ResourceMapping__frequencyDomainAllocation__row2__Type) => CSI_RS_ResourceMapping__frequencyDomainAllocation__row2 t 
    | 2 => fun (t : CSI_RS_ResourceMapping__frequencyDomainAllocation__row4__Type) => CSI_RS_ResourceMapping__frequencyDomainAllocation__row4 t 
    | 3 => fun (t : CSI_RS_ResourceMapping__frequencyDomainAllocation__other__Type) => CSI_RS_ResourceMapping__frequencyDomainAllocation__other t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : CSI_RS_ResourceMapping__frequencyDomainAllocation__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ CSI_RS_ResourceMapping__frequencyDomainAllocation__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_RS_ResourceMapping__frequencyDomainAllocation__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return CSI_RS_ResourceMapping__frequencyDomainAllocation__Type with end) n0
           end t0).

Lemma CSI_RS_ResourceMapping__frequencyDomainAllocation__helper2 :  forall (y : CSI_RS_ResourceMapping__frequencyDomainAllocation__Type), CSI_RS_ResourceMapping__frequencyDomainAllocation__cond y -> choice_cond CSI_RS_ResourceMapping__frequencyDomainAllocation__list (CSI_RS_ResourceMapping__frequencyDomainAllocation__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_RS_ResourceMapping__frequencyDomainAllocation__helper3 :  forall (y : CSI_RS_ResourceMapping__frequencyDomainAllocation__Type), CSI_RS_ResourceMapping__frequencyDomainAllocation__F2 (CSI_RS_ResourceMapping__frequencyDomainAllocation__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_RS_ResourceMapping__frequencyDomainAllocation__helper4 : (forall b : choice CSI_RS_ResourceMapping__frequencyDomainAllocation__list, choice_cond CSI_RS_ResourceMapping__frequencyDomainAllocation__list b -> CSI_RS_ResourceMapping__frequencyDomainAllocation__cond (CSI_RS_ResourceMapping__frequencyDomainAllocation__F2 b) /\ CSI_RS_ResourceMapping__frequencyDomainAllocation__F1 (CSI_RS_ResourceMapping__frequencyDomainAllocation__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_RS_ResourceMapping__frequencyDomainAllocation__F1 CSI_RS_ResourceMapping__frequencyDomainAllocation__F2.
Definition CSI_RS_ResourceMapping__frequencyDomainAllocation__Format : T_Format CSI_RS_ResourceMapping__frequencyDomainAllocation__Type CSI_RS_ResourceMapping__frequencyDomainAllocation__cond :=
  (* Eval compute in *) proj2_format CSI_RS_ResourceMapping__frequencyDomainAllocation__cond CSI_RS_ResourceMapping__frequencyDomainAllocation__list__Format CSI_RS_ResourceMapping__frequencyDomainAllocation__F1 CSI_RS_ResourceMapping__frequencyDomainAllocation__F2 CSI_RS_ResourceMapping__frequencyDomainAllocation__helper2 CSI_RS_ResourceMapping__frequencyDomainAllocation__helper3 CSI_RS_ResourceMapping__frequencyDomainAllocation__helper4.
Opaque CSI_RS_ResourceMapping__frequencyDomainAllocation__cond CSI_RS_ResourceMapping__frequencyDomainAllocation__Format.

Definition CSI_RS_ResourceMapping__nrofPorts__Format : T_Format CSI_RS_ResourceMapping__nrofPorts__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_RS_ResourceMapping__nrofPorts__nat__Format CSI_RS_ResourceMapping__nrofPorts__F1 CSI_RS_ResourceMapping__nrofPorts__F2 CSI_RS_ResourceMapping__nrofPorts__F1F2 CSI_RS_ResourceMapping__nrofPorts__F2F1.

Opaque CSI_RS_ResourceMapping__nrofPorts__cond CSI_RS_ResourceMapping__nrofPorts__Format.

Definition CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__Format : T_Format Z CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__cond :=
 ranged_int_format (0) (13) CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__helper1 CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__helper2.

Opaque CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__cond CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__Format.

Definition CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__Format : T_Format Z CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__cond :=
 ranged_int_format (2) (12) CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__helper1 CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__helper2.

Opaque CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__cond CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__Format.

Definition CSI_RS_ResourceMapping__cdm_Type__Format : T_Format CSI_RS_ResourceMapping__cdm_Type__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_RS_ResourceMapping__cdm_Type__nat__Format CSI_RS_ResourceMapping__cdm_Type__F1 CSI_RS_ResourceMapping__cdm_Type__F2 CSI_RS_ResourceMapping__cdm_Type__F1F2 CSI_RS_ResourceMapping__cdm_Type__F2F1.

Opaque CSI_RS_ResourceMapping__cdm_Type__cond CSI_RS_ResourceMapping__cdm_Type__Format.

Definition CSI_RS_ResourceMapping__density__dot5__Format : T_Format CSI_RS_ResourceMapping__density__dot5__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CSI_RS_ResourceMapping__density__dot5__nat__Format CSI_RS_ResourceMapping__density__dot5__F1 CSI_RS_ResourceMapping__density__dot5__F2 CSI_RS_ResourceMapping__density__dot5__F1F2 CSI_RS_ResourceMapping__density__dot5__F2F1.

Opaque CSI_RS_ResourceMapping__density__dot5__cond CSI_RS_ResourceMapping__density__dot5__Format.


Definition CSI_RS_ResourceMapping__density__Format_Type := Eval cbn in get_formats CSI_RS_ResourceMapping__density__list.
Definition CSI_RS_ResourceMapping__density__Format_list : CSI_RS_ResourceMapping__density__Format_Type :=
  (CSI_RS_ResourceMapping__density__dot5__Format, (unit__Format, (unit__Format, (unit__Format, unit__Format)))).
Definition CSI_RS_ResourceMapping__density__list__Format := Eval compute in choice_format CSI_RS_ResourceMapping__density__list CSI_RS_ResourceMapping__density__len_helper1 CSI_RS_ResourceMapping__density__len_helper2  CSI_RS_ResourceMapping__density__Format_list.
Definition CSI_RS_ResourceMapping__density__F1 (z : CSI_RS_ResourceMapping__density__Type) : (choice CSI_RS_ResourceMapping__density__list) :=
  match z with
   | CSI_RS_ResourceMapping__density__dot5 t => existT _ 0 t
  | CSI_RS_ResourceMapping__density__one t => existT _ 1 t
  | CSI_RS_ResourceMapping__density__three t => existT _ 2 t
  | CSI_RS_ResourceMapping__density__spare t => existT _ 3 t
  end.
Definition CSI_RS_ResourceMapping__density__g := (fun n => typ_set (get_nth_typ CSI_RS_ResourceMapping__density__list n)).
Definition CSI_RS_ResourceMapping__density__F2 (y : choice CSI_RS_ResourceMapping__density__list) : CSI_RS_ResourceMapping__density__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (CSI_RS_ResourceMapping__density__g n -> CSI_RS_ResourceMapping__density__Type) with
    | 0 => fun (t : CSI_RS_ResourceMapping__density__dot5__Type) => CSI_RS_ResourceMapping__density__dot5 t 
    | 1 => fun (t : unit) => CSI_RS_ResourceMapping__density__one t 
    | 2 => fun (t : unit) => CSI_RS_ResourceMapping__density__three t 
    | 3 => fun (t : unit) => CSI_RS_ResourceMapping__density__spare t 
 | (S (S (S (S n0)))) => (fun (x' : nat) (t'' : CSI_RS_ResourceMapping__density__g (S (S (S (S x'))))) =>let t' :=
           eq_rect (get_nth_typ CSI_RS_ResourceMapping__density__list (S (S (S (S x')))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len CSI_RS_ResourceMapping__density__list (S (S (S (S x'))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))) in match t' return CSI_RS_ResourceMapping__density__Type with end) n0
           end t0).

Lemma CSI_RS_ResourceMapping__density__helper2 :  forall (y : CSI_RS_ResourceMapping__density__Type), CSI_RS_ResourceMapping__density__cond y -> choice_cond CSI_RS_ResourceMapping__density__list (CSI_RS_ResourceMapping__density__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma CSI_RS_ResourceMapping__density__helper3 :  forall (y : CSI_RS_ResourceMapping__density__Type), CSI_RS_ResourceMapping__density__F2 (CSI_RS_ResourceMapping__density__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma CSI_RS_ResourceMapping__density__helper4 : (forall b : choice CSI_RS_ResourceMapping__density__list, choice_cond CSI_RS_ResourceMapping__density__list b -> CSI_RS_ResourceMapping__density__cond (CSI_RS_ResourceMapping__density__F2 b) /\ CSI_RS_ResourceMapping__density__F1 (CSI_RS_ResourceMapping__density__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length CSI_RS_ResourceMapping__density__F1 CSI_RS_ResourceMapping__density__F2.
Definition CSI_RS_ResourceMapping__density__Format : T_Format CSI_RS_ResourceMapping__density__Type CSI_RS_ResourceMapping__density__cond :=
  (* Eval compute in *) proj2_format CSI_RS_ResourceMapping__density__cond CSI_RS_ResourceMapping__density__list__Format CSI_RS_ResourceMapping__density__F1 CSI_RS_ResourceMapping__density__F2 CSI_RS_ResourceMapping__density__helper2 CSI_RS_ResourceMapping__density__helper3 CSI_RS_ResourceMapping__density__helper4.
Opaque CSI_RS_ResourceMapping__density__cond CSI_RS_ResourceMapping__density__Format.


Definition CSI_RS_ResourceMapping__root_Format_Type := Eval cbn in seq_format_prod CSI_RS_ResourceMapping__root_list.
Definition CSI_RS_ResourceMapping__root_Format_list : CSI_RS_ResourceMapping__root_Format_Type :=
  (CSI_RS_ResourceMapping__frequencyDomainAllocation__Format, (CSI_RS_ResourceMapping__nrofPorts__Format, (CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain__Format, (CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2__Format, (CSI_RS_ResourceMapping__cdm_Type__Format, (CSI_RS_ResourceMapping__density__Format, (CSI_FrequencyOccupation__Format, unit_format))))))).

Definition CSI_RS_ResourceMapping__ext_Format_Type := Eval cbn in get_formats CSI_RS_ResourceMapping__ext_list.
Definition CSI_RS_ResourceMapping__ext_Format_list : CSI_RS_ResourceMapping__ext_Format_Type :=
  unit__Format.

Definition CSI_RS_ResourceMapping__list_type : Set := (seq_type CSI_RS_ResourceMapping__root_list) * (seq_ext_type CSI_RS_ResourceMapping__ext_list).
Definition CSI_RS_ResourceMapping__list_cond (z : CSI_RS_ResourceMapping__list_type) : Prop :=
        (seq_cond CSI_RS_ResourceMapping__root_list (fst z)) /\ (seq_ext_cond CSI_RS_ResourceMapping__ext_list (snd z)).
Definition CSI_RS_ResourceMapping__list_format : T_Format CSI_RS_ResourceMapping__list_type CSI_RS_ResourceMapping__list_cond :=
 (* Eval compute in *) seq_ext_format CSI_RS_ResourceMapping__root_list CSI_RS_ResourceMapping__root_Format_list CSI_RS_ResourceMapping__ext_list CSI_RS_ResourceMapping__ext_Format_list.

Opaque CSI_RS_ResourceMapping__list_format.
Definition CSI_RS_ResourceMapping__F1 (z : CSI_RS_ResourceMapping__Type) : CSI_RS_ResourceMapping__list_type :=
  (((CSI_RS_ResourceMapping__frequencyDomainAllocation z, (CSI_RS_ResourceMapping__nrofPorts z, (CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain z, (CSI_RS_ResourceMapping__firstOFDMSymbolInTimeDomain2 z, (CSI_RS_ResourceMapping__cdm_Type z, (CSI_RS_ResourceMapping__density z, (CSI_RS_ResourceMapping__freqBand z, tt)))))))), (
tt)).
Definition CSI_RS_ResourceMapping__F2 (y : CSI_RS_ResourceMapping__list_type) : CSI_RS_ResourceMapping__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, (j5, (j6, _))))))), _)=>
    make__CSI_RS_ResourceMapping__Type j0 j1 j2 j3 j4 j5 j6
  end.
Definition CSI_RS_ResourceMapping__helper1 : (forall a : CSI_RS_ResourceMapping__Type, CSI_RS_ResourceMapping__cond a -> CSI_RS_ResourceMapping__list_cond (CSI_RS_ResourceMapping__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CSI_RS_ResourceMapping__helper2 : (forall a : CSI_RS_ResourceMapping__Type, CSI_RS_ResourceMapping__F2 (CSI_RS_ResourceMapping__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CSI_RS_ResourceMapping__helper3 : (forall b : CSI_RS_ResourceMapping__list_type, CSI_RS_ResourceMapping__list_cond b -> CSI_RS_ResourceMapping__cond (CSI_RS_ResourceMapping__F2 b) /\ CSI_RS_ResourceMapping__F1 (CSI_RS_ResourceMapping__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CSI_RS_ResourceMapping__cond, CSI_RS_ResourceMapping__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CSI_RS_ResourceMapping__Format : T_Format CSI_RS_ResourceMapping__Type CSI_RS_ResourceMapping__cond :=
 proj2_format CSI_RS_ResourceMapping__cond CSI_RS_ResourceMapping__list_format  CSI_RS_ResourceMapping__F1 CSI_RS_ResourceMapping__F2 CSI_RS_ResourceMapping__helper1 CSI_RS_ResourceMapping__helper2 CSI_RS_ResourceMapping__helper3.

Opaque CSI_RS_ResourceMapping__cond CSI_RS_ResourceMapping__Format.

