Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.FreqPriorityListEUTRA.

Opaque FreqPriorityListEUTRA__cond FreqPriorityListEUTRA__Format.

Require Import NR.FreqPriorityListNR.

Opaque FreqPriorityListNR__cond FreqPriorityListNR__Format.

Inductive CellReselectionPriorities__t320__Type : Set :=
 | CellReselectionPriorities__t320__min5
 | CellReselectionPriorities__t320__min10
 | CellReselectionPriorities__t320__min20
 | CellReselectionPriorities__t320__min30
 | CellReselectionPriorities__t320__min60
 | CellReselectionPriorities__t320__min120
 | CellReselectionPriorities__t320__min180
 | CellReselectionPriorities__t320__spare1
.
Definition CellReselectionPriorities__t320__cond := (fun (_ : CellReselectionPriorities__t320__Type) => True).
Lemma CellReselectionPriorities__t320__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition CellReselectionPriorities__t320__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 CellReselectionPriorities__t320__nat__helper.

Definition CellReselectionPriorities__t320__F1 t :=
  match t with
  | CellReselectionPriorities__t320__min5 => 0
  | CellReselectionPriorities__t320__min10 => 1
  | CellReselectionPriorities__t320__min20 => 2
  | CellReselectionPriorities__t320__min30 => 3
  | CellReselectionPriorities__t320__min60 => 4
  | CellReselectionPriorities__t320__min120 => 5
  | CellReselectionPriorities__t320__min180 => 6
  | CellReselectionPriorities__t320__spare1 => 7
  end.
Definition CellReselectionPriorities__t320__F2 n :=
  match n with
  | 0 => CellReselectionPriorities__t320__min5
  | 1 => CellReselectionPriorities__t320__min10
  | 2 => CellReselectionPriorities__t320__min20
  | 3 => CellReselectionPriorities__t320__min30
  | 4 => CellReselectionPriorities__t320__min60
  | 5 => CellReselectionPriorities__t320__min120
  | 6 => CellReselectionPriorities__t320__min180
  | 7 => CellReselectionPriorities__t320__spare1
  | _ => CellReselectionPriorities__t320__min5
  end.
Lemma CellReselectionPriorities__t320__F1F2 : forall x : CellReselectionPriorities__t320__Type, (CellReselectionPriorities__t320__F1 x <= 7) /\ CellReselectionPriorities__t320__F2 (CellReselectionPriorities__t320__F1 x) = x. imp_solve. Qed.
Lemma CellReselectionPriorities__t320__F2F1 : forall (y : nat) (H : y <= 7), CellReselectionPriorities__t320__F1 (CellReselectionPriorities__t320__F2 y) = y. enum_solve H y. Qed.

Require Import NR.FreqPriorityListDedicatedSlicing_r17.

Opaque FreqPriorityListDedicatedSlicing_r17__cond FreqPriorityListDedicatedSlicing_r17__Format.

Record CellReselectionPriorities__ext0O__Type : Set :=
  make__CellReselectionPriorities__ext0O__Type {
    CellReselectionPriorities__ext0O__freqPriorityListDedicatedSlicing_r17 : option FreqPriorityListDedicatedSlicing_r17__Type ;
}.
Definition CellReselectionPriorities__ext0O__list := (
 Opt FreqPriorityListDedicatedSlicing_r17__Type FreqPriorityListDedicatedSlicing_r17__cond ::
 nil).
Definition CellReselectionPriorities__ext0O__cond z := 
  opt_cond FreqPriorityListDedicatedSlicing_r17__cond (CellReselectionPriorities__ext0O__freqPriorityListDedicatedSlicing_r17 z) /\
  True.

Definition CellReselectionPriorities__ext0__Type := CellReselectionPriorities__ext0O__Type.
Definition CellReselectionPriorities__ext0__cond := CellReselectionPriorities__ext0O__cond.

Record CellReselectionPriorities__Type : Set :=
  make__CellReselectionPriorities__Type {
    CellReselectionPriorities__freqPriorityListEUTRA : option FreqPriorityListEUTRA__Type ;
    CellReselectionPriorities__freqPriorityListNR : option FreqPriorityListNR__Type ;
    CellReselectionPriorities__t320 : option CellReselectionPriorities__t320__Type ;
    CellReselectionPriorities__ext0 : option CellReselectionPriorities__ext0__Type ;
}.
Definition CellReselectionPriorities__root_list : list seq_elem := (
 Opt FreqPriorityListEUTRA__Type FreqPriorityListEUTRA__cond ::
 Opt FreqPriorityListNR__Type FreqPriorityListNR__cond ::
 Opt CellReselectionPriorities__t320__Type CellReselectionPriorities__t320__cond ::
 nil).
Definition CellReselectionPriorities__ext_list : list typ := (
  typ_cons CellReselectionPriorities__ext0__Type CellReselectionPriorities__ext0__cond ::
  nil).
Definition CellReselectionPriorities__cond (z : CellReselectionPriorities__Type) := 
(  opt_cond FreqPriorityListEUTRA__cond (CellReselectionPriorities__freqPriorityListEUTRA z) /\
  opt_cond FreqPriorityListNR__cond (CellReselectionPriorities__freqPriorityListNR z) /\
  opt_cond CellReselectionPriorities__t320__cond (CellReselectionPriorities__t320 z) /\
  True) /\ 
(  opt_cond CellReselectionPriorities__ext0__cond (CellReselectionPriorities__ext0 z) /\
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
Definition CellReselectionPriorities__t320__Format : T_Format CellReselectionPriorities__t320__Type (fun _ => True) :=
(* Eval compute in *) proj3_format CellReselectionPriorities__t320__nat__Format CellReselectionPriorities__t320__F1 CellReselectionPriorities__t320__F2 CellReselectionPriorities__t320__F1F2 CellReselectionPriorities__t320__F2F1.

Opaque CellReselectionPriorities__t320__cond CellReselectionPriorities__t320__Format.


Definition CellReselectionPriorities__ext0O__Format_Type := Eval cbn in seq_format_prod CellReselectionPriorities__ext0O__list.
Definition CellReselectionPriorities__ext0O__Format_list : CellReselectionPriorities__ext0O__Format_Type :=
  (FreqPriorityListDedicatedSlicing_r17__Format, unit_format).
Definition CellReselectionPriorities__ext0O__list__Format := (*Eval compute in *) seq_format CellReselectionPriorities__ext0O__list CellReselectionPriorities__ext0O__Format_list.
Definition CellReselectionPriorities__ext0O__F1 z :=
  (CellReselectionPriorities__ext0O__freqPriorityListDedicatedSlicing_r17 z, tt).
Definition CellReselectionPriorities__ext0O__F2 (y : seq_type CellReselectionPriorities__ext0O__list) :=
  match y with
  | (i0, _)=>
    make__CellReselectionPriorities__ext0O__Type i0
  end.
Lemma CellReselectionPriorities__ext0O__F1F2_cond (z : CellReselectionPriorities__ext0O__Type)
  : CellReselectionPriorities__ext0O__cond z ->
  (seq_cond CellReselectionPriorities__ext0O__list (CellReselectionPriorities__ext0O__F1 z)).
intro H. unfold CellReselectionPriorities__ext0O__cond in H. simpl. auto. Qed.
Lemma CellReselectionPriorities__ext0O__F1F2_cond2 (z : CellReselectionPriorities__ext0O__Type)
 : CellReselectionPriorities__ext0O__F2 (CellReselectionPriorities__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma CellReselectionPriorities__ext0O__F2F1_cond (y : seq_type CellReselectionPriorities__ext0O__list)
  : seq_cond CellReselectionPriorities__ext0O__list y ->
 (CellReselectionPriorities__ext0O__cond (CellReselectionPriorities__ext0O__F2 y)) /\  CellReselectionPriorities__ext0O__F1 (CellReselectionPriorities__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold CellReselectionPriorities__ext0O__cond. simpl in *. auto.
 - simpl. unfold CellReselectionPriorities__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition CellReselectionPriorities__ext0O__Format : T_Format CellReselectionPriorities__ext0O__Type CellReselectionPriorities__ext0O__cond :=
        proj2_format  CellReselectionPriorities__ext0O__cond CellReselectionPriorities__ext0O__list__Format
    CellReselectionPriorities__ext0O__F1 CellReselectionPriorities__ext0O__F2 CellReselectionPriorities__ext0O__F1F2_cond  CellReselectionPriorities__ext0O__F1F2_cond2 CellReselectionPriorities__ext0O__F2F1_cond.
Opaque CellReselectionPriorities__ext0O__cond CellReselectionPriorities__ext0O__Format.

Definition CellReselectionPriorities__ext0__check_all_none (b : CellReselectionPriorities__ext0O__Type) : bool :=
match b with 
  | make__CellReselectionPriorities__ext0O__Type None  => false 
  | _ => true 
 end.
Definition CellReselectionPriorities__ext0__Format : T_Format CellReselectionPriorities__ext0__Type CellReselectionPriorities__ext0__cond :=
  restrict_add_format CellReselectionPriorities__ext0__check_all_none CellReselectionPriorities__ext0O__Format.

Opaque CellReselectionPriorities__ext0__cond CellReselectionPriorities__ext0__Format.


Definition CellReselectionPriorities__root_Format_Type := Eval cbn in seq_format_prod CellReselectionPriorities__root_list.
Definition CellReselectionPriorities__root_Format_list : CellReselectionPriorities__root_Format_Type :=
  (FreqPriorityListEUTRA__Format, (FreqPriorityListNR__Format, (CellReselectionPriorities__t320__Format, unit_format))).

Definition CellReselectionPriorities__ext_Format_Type := Eval cbn in get_formats CellReselectionPriorities__ext_list.
Definition CellReselectionPriorities__ext_Format_list : CellReselectionPriorities__ext_Format_Type :=
  (CellReselectionPriorities__ext0__Format, unit__Format).

Definition CellReselectionPriorities__list_type : Set := (seq_type CellReselectionPriorities__root_list) * (seq_ext_type CellReselectionPriorities__ext_list).
Definition CellReselectionPriorities__list_cond (z : CellReselectionPriorities__list_type) : Prop :=
        (seq_cond CellReselectionPriorities__root_list (fst z)) /\ (seq_ext_cond CellReselectionPriorities__ext_list (snd z)).
Definition CellReselectionPriorities__list_format : T_Format CellReselectionPriorities__list_type CellReselectionPriorities__list_cond :=
 (* Eval compute in *) seq_ext_format CellReselectionPriorities__root_list CellReselectionPriorities__root_Format_list CellReselectionPriorities__ext_list CellReselectionPriorities__ext_Format_list.

Opaque CellReselectionPriorities__list_format.
Definition CellReselectionPriorities__F1 (z : CellReselectionPriorities__Type) : CellReselectionPriorities__list_type :=
  (((CellReselectionPriorities__freqPriorityListEUTRA z, (CellReselectionPriorities__freqPriorityListNR z, (CellReselectionPriorities__t320 z, tt)))), (
(CellReselectionPriorities__ext0 z, tt))).
Definition CellReselectionPriorities__F2 (y : CellReselectionPriorities__list_type) : CellReselectionPriorities__Type :=
  match y with
  | ((j0, (j1, (j2, _))), (i0, _))=>
    make__CellReselectionPriorities__Type j0 j1 j2 i0
  end.
Definition CellReselectionPriorities__helper1 : (forall a : CellReselectionPriorities__Type, CellReselectionPriorities__cond a -> CellReselectionPriorities__list_cond (CellReselectionPriorities__F1 a)).
                     intros. destruct a. auto. Qed.
Definition CellReselectionPriorities__helper2 : (forall a : CellReselectionPriorities__Type, CellReselectionPriorities__F2 (CellReselectionPriorities__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition CellReselectionPriorities__helper3 : (forall b : CellReselectionPriorities__list_type, CellReselectionPriorities__list_cond b -> CellReselectionPriorities__cond (CellReselectionPriorities__F2 b) /\ CellReselectionPriorities__F1 (CellReselectionPriorities__F2 b) = b).
                     intros. destruct b as [y y1]. unfold CellReselectionPriorities__cond, CellReselectionPriorities__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition CellReselectionPriorities__Format : T_Format CellReselectionPriorities__Type CellReselectionPriorities__cond :=
 proj2_format CellReselectionPriorities__cond CellReselectionPriorities__list_format  CellReselectionPriorities__F1 CellReselectionPriorities__F2 CellReselectionPriorities__helper1 CellReselectionPriorities__helper2 CellReselectionPriorities__helper3.

Opaque CellReselectionPriorities__cond CellReselectionPriorities__Format.

