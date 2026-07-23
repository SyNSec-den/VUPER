Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SchedulingInfo.

Opaque SchedulingInfo__cond SchedulingInfo__Format.

Definition SI_SchedulingInfo__schedulingInfoList__Type := list SchedulingInfo__Type.

Lemma SI_SchedulingInfo__schedulingInfoList__helper1 : (0 <= 1 <= maxSI_Message)%Z. unfold maxSI_Message.
 lia. Qed.
Lemma SI_SchedulingInfo__schedulingInfoList__helper2 : to_bit_sz (Z.to_nat (maxSI_Message - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSI_Message - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SI_SchedulingInfo__schedulingInfoList__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SI_SchedulingInfo__schedulingInfoList__cond (z : SI_SchedulingInfo__schedulingInfoList__Type) :=  (1 <= Z.of_nat (length z) <= maxSI_Message)%Z /\ (list_and SchedulingInfo__cond z) .

Inductive SI_SchedulingInfo__si_WindowLength__Type : Set :=
 | SI_SchedulingInfo__si_WindowLength__s5
 | SI_SchedulingInfo__si_WindowLength__s10
 | SI_SchedulingInfo__si_WindowLength__s20
 | SI_SchedulingInfo__si_WindowLength__s40
 | SI_SchedulingInfo__si_WindowLength__s80
 | SI_SchedulingInfo__si_WindowLength__s160
 | SI_SchedulingInfo__si_WindowLength__s320
 | SI_SchedulingInfo__si_WindowLength__s640
 | SI_SchedulingInfo__si_WindowLength__s1280
 | SI_SchedulingInfo__si_WindowLength__s2560_v1710
 | SI_SchedulingInfo__si_WindowLength__s5120_v1710
.
Definition SI_SchedulingInfo__si_WindowLength__cond := (fun (_ : SI_SchedulingInfo__si_WindowLength__Type) => True).
Lemma SI_SchedulingInfo__si_WindowLength__nat__helper : to_bit_sz 10 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SI_SchedulingInfo__si_WindowLength__nat__Format : T_Format nat (fun z => (z <= 10)) :=
  nat_enum_format 10 SI_SchedulingInfo__si_WindowLength__nat__helper.

Definition SI_SchedulingInfo__si_WindowLength__F1 t :=
  match t with
  | SI_SchedulingInfo__si_WindowLength__s5 => 0
  | SI_SchedulingInfo__si_WindowLength__s10 => 1
  | SI_SchedulingInfo__si_WindowLength__s20 => 2
  | SI_SchedulingInfo__si_WindowLength__s40 => 3
  | SI_SchedulingInfo__si_WindowLength__s80 => 4
  | SI_SchedulingInfo__si_WindowLength__s160 => 5
  | SI_SchedulingInfo__si_WindowLength__s320 => 6
  | SI_SchedulingInfo__si_WindowLength__s640 => 7
  | SI_SchedulingInfo__si_WindowLength__s1280 => 8
  | SI_SchedulingInfo__si_WindowLength__s2560_v1710 => 9
  | SI_SchedulingInfo__si_WindowLength__s5120_v1710 => 10
  end.
Definition SI_SchedulingInfo__si_WindowLength__F2 n :=
  match n with
  | 0 => SI_SchedulingInfo__si_WindowLength__s5
  | 1 => SI_SchedulingInfo__si_WindowLength__s10
  | 2 => SI_SchedulingInfo__si_WindowLength__s20
  | 3 => SI_SchedulingInfo__si_WindowLength__s40
  | 4 => SI_SchedulingInfo__si_WindowLength__s80
  | 5 => SI_SchedulingInfo__si_WindowLength__s160
  | 6 => SI_SchedulingInfo__si_WindowLength__s320
  | 7 => SI_SchedulingInfo__si_WindowLength__s640
  | 8 => SI_SchedulingInfo__si_WindowLength__s1280
  | 9 => SI_SchedulingInfo__si_WindowLength__s2560_v1710
  | 10 => SI_SchedulingInfo__si_WindowLength__s5120_v1710
  | _ => SI_SchedulingInfo__si_WindowLength__s5
  end.
Lemma SI_SchedulingInfo__si_WindowLength__F1F2 : forall x : SI_SchedulingInfo__si_WindowLength__Type, (SI_SchedulingInfo__si_WindowLength__F1 x <= 10) /\ SI_SchedulingInfo__si_WindowLength__F2 (SI_SchedulingInfo__si_WindowLength__F1 x) = x. imp_solve. Qed.
Lemma SI_SchedulingInfo__si_WindowLength__F2F1 : forall (y : nat) (H : y <= 10), SI_SchedulingInfo__si_WindowLength__F1 (SI_SchedulingInfo__si_WindowLength__F2 y) = y. enum_solve H y. Qed.

Require Import NR.SI_RequestConfig.

Opaque SI_RequestConfig__cond SI_RequestConfig__Format.

Require Import NR.SI_RequestConfig.

Opaque SI_RequestConfig__cond SI_RequestConfig__Format.

Definition SI_SchedulingInfo__systemInformationAreaID__Type := bit_string_fixed.
Definition SI_SchedulingInfo__systemInformationAreaID__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 24 /\ bit_string_len_prop (fst z) (snd z)).
Record SI_SchedulingInfo__Type : Set :=
  make__SI_SchedulingInfo__Type {
    SI_SchedulingInfo__schedulingInfoList : SI_SchedulingInfo__schedulingInfoList__Type ;
    SI_SchedulingInfo__si_WindowLength : SI_SchedulingInfo__si_WindowLength__Type ;
    SI_SchedulingInfo__si_RequestConfig : option SI_RequestConfig__Type ;
    SI_SchedulingInfo__si_RequestConfigSUL : option SI_RequestConfig__Type ;
    SI_SchedulingInfo__systemInformationAreaID : option SI_SchedulingInfo__systemInformationAreaID__Type ;
}.
Definition SI_SchedulingInfo__root_list : list seq_elem := (
 Nor SI_SchedulingInfo__schedulingInfoList__Type SI_SchedulingInfo__schedulingInfoList__cond ::
 Nor SI_SchedulingInfo__si_WindowLength__Type SI_SchedulingInfo__si_WindowLength__cond ::
 Opt SI_RequestConfig__Type SI_RequestConfig__cond ::
 Opt SI_RequestConfig__Type SI_RequestConfig__cond ::
 Opt SI_SchedulingInfo__systemInformationAreaID__Type SI_SchedulingInfo__systemInformationAreaID__cond ::
 nil).
Definition SI_SchedulingInfo__ext_list : list typ := (
  nil).
Definition SI_SchedulingInfo__cond (z : SI_SchedulingInfo__Type) := 
(  SI_SchedulingInfo__schedulingInfoList__cond (SI_SchedulingInfo__schedulingInfoList z) /\
  SI_SchedulingInfo__si_WindowLength__cond (SI_SchedulingInfo__si_WindowLength z) /\
  opt_cond SI_RequestConfig__cond (SI_SchedulingInfo__si_RequestConfig z) /\
  opt_cond SI_RequestConfig__cond (SI_SchedulingInfo__si_RequestConfigSUL z) /\
  opt_cond SI_SchedulingInfo__systemInformationAreaID__cond (SI_SchedulingInfo__systemInformationAreaID z) /\
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
Definition SI_SchedulingInfo__schedulingInfoList__Format : T_Format SI_SchedulingInfo__schedulingInfoList__Type SI_SchedulingInfo__schedulingInfoList__cond := seq_of_format SchedulingInfo__Format 1 maxSI_Message SI_SchedulingInfo__schedulingInfoList__helper1 SI_SchedulingInfo__schedulingInfoList__helper2.

Opaque SI_SchedulingInfo__schedulingInfoList__cond SI_SchedulingInfo__schedulingInfoList__Format.

Definition SI_SchedulingInfo__si_WindowLength__Format : T_Format SI_SchedulingInfo__si_WindowLength__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SI_SchedulingInfo__si_WindowLength__nat__Format SI_SchedulingInfo__si_WindowLength__F1 SI_SchedulingInfo__si_WindowLength__F2 SI_SchedulingInfo__si_WindowLength__F1F2 SI_SchedulingInfo__si_WindowLength__F2F1.

Opaque SI_SchedulingInfo__si_WindowLength__cond SI_SchedulingInfo__si_WindowLength__Format.

Definition SI_SchedulingInfo__systemInformationAreaID__Format : T_Format SI_SchedulingInfo__systemInformationAreaID__Type SI_SchedulingInfo__systemInformationAreaID__cond := (* Eval compute in *) bit_string_fixed_format 24.
Opaque SI_SchedulingInfo__systemInformationAreaID__cond SI_SchedulingInfo__systemInformationAreaID__Format.


Definition SI_SchedulingInfo__root_Format_Type := Eval cbn in seq_format_prod SI_SchedulingInfo__root_list.
Definition SI_SchedulingInfo__root_Format_list : SI_SchedulingInfo__root_Format_Type :=
  (SI_SchedulingInfo__schedulingInfoList__Format, (SI_SchedulingInfo__si_WindowLength__Format, (SI_RequestConfig__Format, (SI_RequestConfig__Format, (SI_SchedulingInfo__systemInformationAreaID__Format, unit_format))))).

Definition SI_SchedulingInfo__ext_Format_Type := Eval cbn in get_formats SI_SchedulingInfo__ext_list.
Definition SI_SchedulingInfo__ext_Format_list : SI_SchedulingInfo__ext_Format_Type :=
  unit__Format.

Definition SI_SchedulingInfo__list_type : Set := (seq_type SI_SchedulingInfo__root_list) * (seq_ext_type SI_SchedulingInfo__ext_list).
Definition SI_SchedulingInfo__list_cond (z : SI_SchedulingInfo__list_type) : Prop :=
        (seq_cond SI_SchedulingInfo__root_list (fst z)) /\ (seq_ext_cond SI_SchedulingInfo__ext_list (snd z)).
Definition SI_SchedulingInfo__list_format : T_Format SI_SchedulingInfo__list_type SI_SchedulingInfo__list_cond :=
 (* Eval compute in *) seq_ext_format SI_SchedulingInfo__root_list SI_SchedulingInfo__root_Format_list SI_SchedulingInfo__ext_list SI_SchedulingInfo__ext_Format_list.

Opaque SI_SchedulingInfo__list_format.
Definition SI_SchedulingInfo__F1 (z : SI_SchedulingInfo__Type) : SI_SchedulingInfo__list_type :=
  (((SI_SchedulingInfo__schedulingInfoList z, (SI_SchedulingInfo__si_WindowLength z, (SI_SchedulingInfo__si_RequestConfig z, (SI_SchedulingInfo__si_RequestConfigSUL z, (SI_SchedulingInfo__systemInformationAreaID z, tt)))))), (
tt)).
Definition SI_SchedulingInfo__F2 (y : SI_SchedulingInfo__list_type) : SI_SchedulingInfo__Type :=
  match y with
  | ((j0, (j1, (j2, (j3, (j4, _))))), _)=>
    make__SI_SchedulingInfo__Type j0 j1 j2 j3 j4
  end.
Definition SI_SchedulingInfo__helper1 : (forall a : SI_SchedulingInfo__Type, SI_SchedulingInfo__cond a -> SI_SchedulingInfo__list_cond (SI_SchedulingInfo__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SI_SchedulingInfo__helper2 : (forall a : SI_SchedulingInfo__Type, SI_SchedulingInfo__F2 (SI_SchedulingInfo__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SI_SchedulingInfo__helper3 : (forall b : SI_SchedulingInfo__list_type, SI_SchedulingInfo__list_cond b -> SI_SchedulingInfo__cond (SI_SchedulingInfo__F2 b) /\ SI_SchedulingInfo__F1 (SI_SchedulingInfo__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SI_SchedulingInfo__cond, SI_SchedulingInfo__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SI_SchedulingInfo__Format : T_Format SI_SchedulingInfo__Type SI_SchedulingInfo__cond :=
 proj2_format SI_SchedulingInfo__cond SI_SchedulingInfo__list_format  SI_SchedulingInfo__F1 SI_SchedulingInfo__F2 SI_SchedulingInfo__helper1 SI_SchedulingInfo__helper2 SI_SchedulingInfo__helper3.

Opaque SI_SchedulingInfo__cond SI_SchedulingInfo__Format.

