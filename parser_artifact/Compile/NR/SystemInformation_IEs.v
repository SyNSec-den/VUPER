Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SIB2.

Opaque SIB2__cond SIB2__Format.

Require Import NR.SIB3.

Opaque SIB3__cond SIB3__Format.

Require Import NR.SIB4.

Opaque SIB4__cond SIB4__Format.

Require Import NR.SIB5.

Opaque SIB5__cond SIB5__Format.

Require Import NR.SIB6.

Opaque SIB6__cond SIB6__Format.

Require Import NR.SIB7.

Opaque SIB7__cond SIB7__Format.

Require Import NR.SIB8.

Opaque SIB8__cond SIB8__Format.

Require Import NR.SIB9.

Opaque SIB9__cond SIB9__Format.


Inductive SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type : Set :=
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib2 : SIB2__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib3 : SIB3__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib4 : SIB4__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib5 : SIB5__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib6 : SIB6__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib7 : SIB7__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib8 : SIB8__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib9 : SIB9__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type
.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list : list typ := (
typ_cons SIB2__Type SIB2__cond ::
typ_cons SIB3__Type SIB3__cond ::
typ_cons SIB4__Type SIB4__cond ::
typ_cons SIB5__Type SIB5__cond ::
typ_cons SIB6__Type SIB6__cond ::
typ_cons SIB7__Type SIB7__cond ::
typ_cons SIB8__Type SIB8__cond ::
typ_cons SIB9__Type SIB9__cond ::
 nil).
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__cond (c : SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type) := 
  match c with
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib2 t => SIB2__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib3 t => SIB3__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib4 t => SIB4__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib5 t => SIB5__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib6 t => SIB6__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib7 t => SIB7__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib8 t => SIB8__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib9 t => SIB9__cond t 
  end.

Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__len_helper1 : to_bit_sz (length SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__len_helper2 : 2 <= length2 SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list.
 simpl. lia. Qed.
Require Import NR.SIB10_r16.

Opaque SIB10_r16__cond SIB10_r16__Format.

Require Import NR.SIB11_r16.

Opaque SIB11_r16__cond SIB11_r16__Format.

Require Import NR.SIB12_r16.

Opaque SIB12_r16__cond SIB12_r16__Format.

Require Import NR.SIB13_r16.

Opaque SIB13_r16__cond SIB13_r16__Format.

Require Import NR.SIB14_r16.

Opaque SIB14_r16__cond SIB14_r16__Format.

Require Import NR.SIB15_r17.

Opaque SIB15_r17__cond SIB15_r17__Format.

Require Import NR.SIB16_r17.

Opaque SIB16_r17__cond SIB16_r17__Format.

Require Import NR.SIB17_r17.

Opaque SIB17_r17__cond SIB17_r17__Format.

Require Import NR.SIB18_r17.

Opaque SIB18_r17__cond SIB18_r17__Format.

Require Import NR.SIB19_r17.

Opaque SIB19_r17__cond SIB19_r17__Format.

Require Import NR.SIB20_r17.

Opaque SIB20_r17__cond SIB20_r17__Format.

Require Import NR.SIB21_r17.

Opaque SIB21_r17__cond SIB21_r17__Format.


Inductive SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type : Set :=
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib10_v1610 : SIB10_r16__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib11_v1610 : SIB11_r16__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib12_v1610 : SIB12_r16__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib13_v1610 : SIB13_r16__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib14_v1610 : SIB14_r16__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib15_v1700 : SIB15_r17__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib16_v1700 : SIB16_r17__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib17_v1700 : SIB17_r17__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib18_v1700 : SIB18_r17__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib19_v1700 : SIB19_r17__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib20_v1700 : SIB20_r17__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib21_v1700 : SIB21_r17__Type -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type
.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list : list typ := (
typ_cons SIB10_r16__Type SIB10_r16__cond ::
typ_cons SIB11_r16__Type SIB11_r16__cond ::
typ_cons SIB12_r16__Type SIB12_r16__cond ::
typ_cons SIB13_r16__Type SIB13_r16__cond ::
typ_cons SIB14_r16__Type SIB14_r16__cond ::
typ_cons SIB15_r17__Type SIB15_r17__cond ::
typ_cons SIB16_r17__Type SIB16_r17__cond ::
typ_cons SIB17_r17__Type SIB17_r17__cond ::
typ_cons SIB18_r17__Type SIB18_r17__cond ::
typ_cons SIB19_r17__Type SIB19_r17__cond ::
typ_cons SIB20_r17__Type SIB20_r17__cond ::
typ_cons SIB21_r17__Type SIB21_r17__cond ::
 nil).
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__cond (c : SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type) := 
  match c with
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib10_v1610 t => SIB10_r16__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib11_v1610 t => SIB11_r16__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib12_v1610 t => SIB12_r16__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib13_v1610 t => SIB13_r16__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib14_v1610 t => SIB14_r16__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib15_v1700 t => SIB15_r17__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib16_v1700 t => SIB16_r17__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib17_v1700 t => SIB17_r17__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib18_v1700 t => SIB18_r17__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib19_v1700 t => SIB19_r17__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib20_v1700 t => SIB20_r17__cond t 
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib21_v1700 t => SIB21_r17__cond t 
  end.

Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__len_helper1 : to_bit_sz (length SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__Type : Set := SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type + SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__cond :=
  sum_cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__cond.
Definition SystemInformation_IEs__sib_TypeAndInfo__Type := list SystemInformation_IEs__sib_TypeAndInfo__seq_of__Type.

Lemma SystemInformation_IEs__sib_TypeAndInfo__helper1 : (0 <= 1 <= maxSIB)%Z. unfold maxSIB.
 lia. Qed.
Lemma SystemInformation_IEs__sib_TypeAndInfo__helper2 : to_bit_sz (Z.to_nat (maxSIB - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (maxSIB - 1))%Z). { apply Zorder.Zle_minus_le_0. apply SystemInformation_IEs__sib_TypeAndInfo__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SystemInformation_IEs__sib_TypeAndInfo__cond (z : SystemInformation_IEs__sib_TypeAndInfo__Type) :=  (1 <= Z.of_nat (length z) <= maxSIB)%Z /\ (list_and SystemInformation_IEs__sib_TypeAndInfo__seq_of__cond z) .

Record SystemInformation_IEs__nonCriticalExtension__Type : Set := make__SystemInformation_IEs__nonCriticalExtension__Type {}.
Definition SystemInformation_IEs__nonCriticalExtension__cond (z : SystemInformation_IEs__nonCriticalExtension__Type) := True.
Record SystemInformation_IEs__Type : Set :=
  make__SystemInformation_IEs__Type {
    SystemInformation_IEs__sib_TypeAndInfo : SystemInformation_IEs__sib_TypeAndInfo__Type ;
    SystemInformation_IEs__lateNonCriticalExtension : option octet_string ;
    SystemInformation_IEs__nonCriticalExtension : option SystemInformation_IEs__nonCriticalExtension__Type ;
}.
Definition SystemInformation_IEs__list := (
 Nor SystemInformation_IEs__sib_TypeAndInfo__Type SystemInformation_IEs__sib_TypeAndInfo__cond ::
 Opt octet_string (fun (b : octet_string) => length b < Nat.pow 2 14) ::
 Opt SystemInformation_IEs__nonCriticalExtension__Type SystemInformation_IEs__nonCriticalExtension__cond ::
 nil).
Definition SystemInformation_IEs__cond z := 
  SystemInformation_IEs__sib_TypeAndInfo__cond (SystemInformation_IEs__sib_TypeAndInfo z) /\
  opt_cond (fun (b : octet_string) => length b < Nat.pow 2 14) (SystemInformation_IEs__lateNonCriticalExtension z) /\
  opt_cond SystemInformation_IEs__nonCriticalExtension__cond (SystemInformation_IEs__nonCriticalExtension z) /\
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

Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Format_Type := Eval cbn in get_formats SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Format_list : SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Format_Type :=
  (SIB2__Format, (SIB3__Format, (SIB4__Format, (SIB5__Format, (SIB6__Format, (SIB7__Format, (SIB8__Format, (SIB9__Format, unit__Format)))))))).
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list__Format := Eval compute in choice_format SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__len_helper1 SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__len_helper2  SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Format_list.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F1 (z : SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type) : (choice SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list) :=
  match z with
   | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib2 t => existT _ 0 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib3 t => existT _ 1 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib4 t => existT _ 2 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib5 t => existT _ 3 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib6 t => existT _ 4 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib7 t => existT _ 5 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib8 t => existT _ 6 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib9 t => existT _ 7 t
  end.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__g := (fun n => typ_set (get_nth_typ SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list n)).
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F2 (y : choice SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list) : SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__g n -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type) with
    | 0 => fun (t : SIB2__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib2 t 
    | 1 => fun (t : SIB3__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib3 t 
    | 2 => fun (t : SIB4__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib4 t 
    | 3 => fun (t : SIB5__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib5 t 
    | 4 => fun (t : SIB6__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib6 t 
    | 5 => fun (t : SIB7__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib7 t 
    | 6 => fun (t : SIB8__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib8 t 
    | 7 => fun (t : SIB9__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__sib9 t 
 | (S (S (S (S (S (S (S (S n0)))))))) => (fun (x' : nat) (t'' : SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__g (S (S (S (S (S (S (S (S x'))))))))) =>let t' :=
           eq_rect (get_nth_typ SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list (S (S (S (S (S (S (S (S x')))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list (S (S (S (S (S (S (S (S x'))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))) in match t' return SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type with end) n0
           end t0).

Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__helper2 :  forall (y : SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type), SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__cond y -> choice_cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list (SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__helper3 :  forall (y : SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type), SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F2 (SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__helper4 : (forall b : choice SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list, choice_cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list b -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__cond (SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F2 b) /\ SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F1 (SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F1 SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F2.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Format : T_Format SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Type SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__cond :=
  (* Eval compute in *) proj2_format SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__list__Format SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F1 SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__F2 SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__helper2 SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__helper3 SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__helper4.
Opaque SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Format.


Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Format_Type := Eval cbn in get_formats SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Format_list : SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Format_Type :=
  (SIB10_r16__Format, (SIB11_r16__Format, (SIB12_r16__Format, (SIB13_r16__Format, (SIB14_r16__Format, (SIB15_r17__Format, (SIB16_r17__Format, (SIB17_r17__Format, (SIB18_r17__Format, (SIB19_r17__Format, (SIB20_r17__Format, (SIB21_r17__Format, unit__Format)))))))))))).
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list__Format := Eval compute in choice_ext_format SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Format_list.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F1 (z : SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type) : (choice SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list) :=
  match z with
   | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib10_v1610 t => existT _ 0 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib11_v1610 t => existT _ 1 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib12_v1610 t => existT _ 2 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib13_v1610 t => existT _ 3 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib14_v1610 t => existT _ 4 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib15_v1700 t => existT _ 5 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib16_v1700 t => existT _ 6 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib17_v1700 t => existT _ 7 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib18_v1700 t => existT _ 8 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib19_v1700 t => existT _ 9 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib20_v1700 t => existT _ 10 t
  | SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib21_v1700 t => existT _ 11 t
  end.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__g := (fun n => typ_set (get_nth_typ SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list n)).
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F2 (y : choice SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list) : SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__g n -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type) with
    | 0 => fun (t : SIB10_r16__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib10_v1610 t 
    | 1 => fun (t : SIB11_r16__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib11_v1610 t 
    | 2 => fun (t : SIB12_r16__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib12_v1610 t 
    | 3 => fun (t : SIB13_r16__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib13_v1610 t 
    | 4 => fun (t : SIB14_r16__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib14_v1610 t 
    | 5 => fun (t : SIB15_r17__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib15_v1700 t 
    | 6 => fun (t : SIB16_r17__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib16_v1700 t 
    | 7 => fun (t : SIB17_r17__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib17_v1700 t 
    | 8 => fun (t : SIB18_r17__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib18_v1700 t 
    | 9 => fun (t : SIB19_r17__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib19_v1700 t 
    | 10 => fun (t : SIB20_r17__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib20_v1700 t 
    | 11 => fun (t : SIB21_r17__Type) => SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__sib21_v1700 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S n0)))))))))))) => (fun (x' : nat) (t'' : SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__g (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))) =>let t' :=
                       eq_rect (get_nth_typ SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))
                       (fun t' : typ => typ_set t') t'' empty_typ
                       (get_nth_typ_ge_len SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))
                       (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x')))))))))))))) in match t' return SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type with end) n0
                       end t0).

Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__helper2 :  forall (y : SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type), SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__cond y -> choice_cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list (SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__helper3 :  forall (y : SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type), SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F2 (SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__helper4 : (forall b : choice SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list, choice_cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list b -> SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__cond (SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F2 b) /\ SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F1 (SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F1 SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F2.
Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Format : T_Format SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Type SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__cond :=
          proj2_format SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__list__Format SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F1 SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__F2 SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__helper2 SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__helper3 SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__helper4.
Opaque SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Format.

Definition SystemInformation_IEs__sib_TypeAndInfo__seq_of__Format : T_Format SystemInformation_IEs__sib_TypeAndInfo__seq_of__Type SystemInformation_IEs__sib_TypeAndInfo__seq_of__cond := sum_format SystemInformation_IEs__sib_TypeAndInfo__seq_of__root__Format SystemInformation_IEs__sib_TypeAndInfo__seq_of__ext__Format.
Opaque SystemInformation_IEs__sib_TypeAndInfo__seq_of__cond SystemInformation_IEs__sib_TypeAndInfo__seq_of__Format.

Definition SystemInformation_IEs__sib_TypeAndInfo__Format : T_Format SystemInformation_IEs__sib_TypeAndInfo__Type SystemInformation_IEs__sib_TypeAndInfo__cond := seq_of_format SystemInformation_IEs__sib_TypeAndInfo__seq_of__Format 1 maxSIB SystemInformation_IEs__sib_TypeAndInfo__helper1 SystemInformation_IEs__sib_TypeAndInfo__helper2.

Opaque SystemInformation_IEs__sib_TypeAndInfo__cond SystemInformation_IEs__sib_TypeAndInfo__Format.

Definition SystemInformation_IEs__nonCriticalExtension__helper : forall a : SystemInformation_IEs__nonCriticalExtension__Type, True -> True /\ make__SystemInformation_IEs__nonCriticalExtension__Type = a.
  eq_unit_helper_tact. Qed.
Definition SystemInformation_IEs__nonCriticalExtension__Format : T_Format SystemInformation_IEs__nonCriticalExtension__Type SystemInformation_IEs__nonCriticalExtension__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SystemInformation_IEs__nonCriticalExtension__Type)
    SystemInformation_IEs__nonCriticalExtension__helper unit_unique (fun _ => left I).

Opaque SystemInformation_IEs__nonCriticalExtension__cond SystemInformation_IEs__nonCriticalExtension__Format.


Definition SystemInformation_IEs__Format_Type := Eval cbn in seq_format_prod SystemInformation_IEs__list.
Definition SystemInformation_IEs__Format_list : SystemInformation_IEs__Format_Type :=
  (SystemInformation_IEs__sib_TypeAndInfo__Format, (octet_string_nc__Format, (SystemInformation_IEs__nonCriticalExtension__Format, unit_format))).
Definition SystemInformation_IEs__list__Format := (*Eval compute in *) seq_format SystemInformation_IEs__list SystemInformation_IEs__Format_list.
Definition SystemInformation_IEs__F1 z :=
  (SystemInformation_IEs__sib_TypeAndInfo z, (SystemInformation_IEs__lateNonCriticalExtension z, (SystemInformation_IEs__nonCriticalExtension z, tt))).
Definition SystemInformation_IEs__F2 (y : seq_type SystemInformation_IEs__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SystemInformation_IEs__Type i0 i1 i2
  end.
Lemma SystemInformation_IEs__F1F2_cond (z : SystemInformation_IEs__Type)
  : SystemInformation_IEs__cond z ->
  (seq_cond SystemInformation_IEs__list (SystemInformation_IEs__F1 z)).
intro H. unfold SystemInformation_IEs__cond in H. simpl. auto. Qed.
Lemma SystemInformation_IEs__F1F2_cond2 (z : SystemInformation_IEs__Type)
 : SystemInformation_IEs__F2 (SystemInformation_IEs__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SystemInformation_IEs__F2F1_cond (y : seq_type SystemInformation_IEs__list)
  : seq_cond SystemInformation_IEs__list y ->
 (SystemInformation_IEs__cond (SystemInformation_IEs__F2 y)) /\  SystemInformation_IEs__F1 (SystemInformation_IEs__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SystemInformation_IEs__cond. simpl in *. auto.
 - simpl. unfold SystemInformation_IEs__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SystemInformation_IEs__Format : T_Format SystemInformation_IEs__Type SystemInformation_IEs__cond :=
        proj2_format  SystemInformation_IEs__cond SystemInformation_IEs__list__Format
    SystemInformation_IEs__F1 SystemInformation_IEs__F2 SystemInformation_IEs__F1F2_cond  SystemInformation_IEs__F1F2_cond2 SystemInformation_IEs__F2F1_cond.
Opaque SystemInformation_IEs__cond SystemInformation_IEs__Format.

