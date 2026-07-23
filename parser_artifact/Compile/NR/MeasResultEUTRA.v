Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.PhysCellId.

Opaque PhysCellId__cond PhysCellId__Format.

Require Import NR.MeasQuantityResultsEUTRA.

Opaque MeasQuantityResultsEUTRA__cond MeasQuantityResultsEUTRA__Format.

Require Import NR.CGI_InfoEUTRA.

Opaque CGI_InfoEUTRA__cond CGI_InfoEUTRA__Format.

Record MeasResultEUTRA__Type : Set :=
  make__MeasResultEUTRA__Type {
    MeasResultEUTRA__eutra_PhysCellId : PhysCellId__Type ;
    MeasResultEUTRA__measResult : MeasQuantityResultsEUTRA__Type ;
    MeasResultEUTRA__cgi_Info : option CGI_InfoEUTRA__Type ;
}.
Definition MeasResultEUTRA__root_list : list seq_elem := (
 Nor PhysCellId__Type PhysCellId__cond ::
 Nor MeasQuantityResultsEUTRA__Type MeasQuantityResultsEUTRA__cond ::
 Opt CGI_InfoEUTRA__Type CGI_InfoEUTRA__cond ::
 nil).
Definition MeasResultEUTRA__ext_list : list typ := (
  nil).
Definition MeasResultEUTRA__cond (z : MeasResultEUTRA__Type) := 
(  PhysCellId__cond (MeasResultEUTRA__eutra_PhysCellId z) /\
  MeasQuantityResultsEUTRA__cond (MeasResultEUTRA__measResult z) /\
  opt_cond CGI_InfoEUTRA__cond (MeasResultEUTRA__cgi_Info z) /\
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

Definition MeasResultEUTRA__root_Format_Type := Eval cbn in seq_format_prod MeasResultEUTRA__root_list.
Definition MeasResultEUTRA__root_Format_list : MeasResultEUTRA__root_Format_Type :=
  (PhysCellId__Format, (MeasQuantityResultsEUTRA__Format, (CGI_InfoEUTRA__Format, unit_format))).

Definition MeasResultEUTRA__ext_Format_Type := Eval cbn in get_formats MeasResultEUTRA__ext_list.
Definition MeasResultEUTRA__ext_Format_list : MeasResultEUTRA__ext_Format_Type :=
  unit__Format.

Definition MeasResultEUTRA__list_type : Set := (seq_type MeasResultEUTRA__root_list) * (seq_ext_type MeasResultEUTRA__ext_list).
Definition MeasResultEUTRA__list_cond (z : MeasResultEUTRA__list_type) : Prop :=
        (seq_cond MeasResultEUTRA__root_list (fst z)) /\ (seq_ext_cond MeasResultEUTRA__ext_list (snd z)).
Definition MeasResultEUTRA__list_format : T_Format MeasResultEUTRA__list_type MeasResultEUTRA__list_cond :=
 (* Eval compute in *) seq_ext_format MeasResultEUTRA__root_list MeasResultEUTRA__root_Format_list MeasResultEUTRA__ext_list MeasResultEUTRA__ext_Format_list.

Opaque MeasResultEUTRA__list_format.
Definition MeasResultEUTRA__F1 (z : MeasResultEUTRA__Type) : MeasResultEUTRA__list_type :=
  (((MeasResultEUTRA__eutra_PhysCellId z, (MeasResultEUTRA__measResult z, (MeasResultEUTRA__cgi_Info z, tt)))), (
tt)).
Definition MeasResultEUTRA__F2 (y : MeasResultEUTRA__list_type) : MeasResultEUTRA__Type :=
  match y with
  | ((j0, (j1, (j2, _))), _)=>
    make__MeasResultEUTRA__Type j0 j1 j2
  end.
Definition MeasResultEUTRA__helper1 : (forall a : MeasResultEUTRA__Type, MeasResultEUTRA__cond a -> MeasResultEUTRA__list_cond (MeasResultEUTRA__F1 a)).
                     intros. destruct a. auto. Qed.
Definition MeasResultEUTRA__helper2 : (forall a : MeasResultEUTRA__Type, MeasResultEUTRA__F2 (MeasResultEUTRA__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition MeasResultEUTRA__helper3 : (forall b : MeasResultEUTRA__list_type, MeasResultEUTRA__list_cond b -> MeasResultEUTRA__cond (MeasResultEUTRA__F2 b) /\ MeasResultEUTRA__F1 (MeasResultEUTRA__F2 b) = b).
                     intros. destruct b as [y y1]. unfold MeasResultEUTRA__cond, MeasResultEUTRA__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition MeasResultEUTRA__Format : T_Format MeasResultEUTRA__Type MeasResultEUTRA__cond :=
 proj2_format MeasResultEUTRA__cond MeasResultEUTRA__list_format  MeasResultEUTRA__F1 MeasResultEUTRA__F2 MeasResultEUTRA__helper1 MeasResultEUTRA__helper2 MeasResultEUTRA__helper3.

Opaque MeasResultEUTRA__cond MeasResultEUTRA__Format.

