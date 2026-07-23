Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Require Import NR.SearchSpaceId.

Opaque SearchSpaceId__cond SearchSpaceId__Format.

Require Import NR.ControlResourceSetId.

Opaque ControlResourceSetId__cond ControlResourceSetId__Format.

Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__cond := (fun z => (0 <= z <= 1)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__cond := (fun z => (0 <= z <= 3)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__cond := (fun z => (0 <= z <= 4)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__cond := (fun z => (0 <= z <= 7)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__Type := Z.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__cond := (fun z => (0 <= z <= 2559)%Z).

Inductive SearchSpace__monitoringSlotPeriodicityAndOffset__Type : Set :=
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl1 : unit -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl2 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl4 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl5 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl8 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl10 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl16 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl20 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl40 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl80 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl160 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl320 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl640 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560 : Z -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type
.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__cond ::
typ_cons Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__cond ::
 nil).
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__cond (c : SearchSpace__monitoringSlotPeriodicityAndOffset__Type) := 
  match c with
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl1 t => (fun _ => True) t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl2 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl4 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl5 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl8 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl10 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl16 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl20 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl40 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl80 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl160 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl320 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl640 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__cond t 
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560 t => SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__cond t 
  end.

Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__len_helper1 : to_bit_sz (length SearchSpace__monitoringSlotPeriodicityAndOffset__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__len_helper2 : 2 <= length2 SearchSpace__monitoringSlotPeriodicityAndOffset__list.
 simpl. lia. Qed.
Lemma SearchSpace__duration__helper1 : (2 <= 2559)%Z.  lia. Qed.
Lemma SearchSpace__duration__helper2 : to_bit_sz (Z.to_nat (2559 - 2)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 2))%Z). { apply Zorder.Zle_minus_le_0. apply SearchSpace__duration__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SearchSpace__duration__Type := Z.
Definition SearchSpace__duration__cond := (fun z => (2 <= z <= 2559)%Z).
Definition SearchSpace__monitoringSymbolsWithinSlot__Type := bit_string_fixed.
Definition SearchSpace__monitoringSymbolsWithinSlot__cond := (fun z : bit_string_fixed => (fst z) = Z.to_nat 14 /\ bit_string_len_prop (fst z) (snd z)).
Inductive SearchSpace__nrofCandidates__aggregationLevel1__Type : Set :=
 | SearchSpace__nrofCandidates__aggregationLevel1__n0
 | SearchSpace__nrofCandidates__aggregationLevel1__n1
 | SearchSpace__nrofCandidates__aggregationLevel1__n2
 | SearchSpace__nrofCandidates__aggregationLevel1__n3
 | SearchSpace__nrofCandidates__aggregationLevel1__n4
 | SearchSpace__nrofCandidates__aggregationLevel1__n5
 | SearchSpace__nrofCandidates__aggregationLevel1__n6
 | SearchSpace__nrofCandidates__aggregationLevel1__n8
.
Definition SearchSpace__nrofCandidates__aggregationLevel1__cond := (fun (_ : SearchSpace__nrofCandidates__aggregationLevel1__Type) => True).
Lemma SearchSpace__nrofCandidates__aggregationLevel1__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__nrofCandidates__aggregationLevel1__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SearchSpace__nrofCandidates__aggregationLevel1__nat__helper.

Definition SearchSpace__nrofCandidates__aggregationLevel1__F1 t :=
  match t with
  | SearchSpace__nrofCandidates__aggregationLevel1__n0 => 0
  | SearchSpace__nrofCandidates__aggregationLevel1__n1 => 1
  | SearchSpace__nrofCandidates__aggregationLevel1__n2 => 2
  | SearchSpace__nrofCandidates__aggregationLevel1__n3 => 3
  | SearchSpace__nrofCandidates__aggregationLevel1__n4 => 4
  | SearchSpace__nrofCandidates__aggregationLevel1__n5 => 5
  | SearchSpace__nrofCandidates__aggregationLevel1__n6 => 6
  | SearchSpace__nrofCandidates__aggregationLevel1__n8 => 7
  end.
Definition SearchSpace__nrofCandidates__aggregationLevel1__F2 n :=
  match n with
  | 0 => SearchSpace__nrofCandidates__aggregationLevel1__n0
  | 1 => SearchSpace__nrofCandidates__aggregationLevel1__n1
  | 2 => SearchSpace__nrofCandidates__aggregationLevel1__n2
  | 3 => SearchSpace__nrofCandidates__aggregationLevel1__n3
  | 4 => SearchSpace__nrofCandidates__aggregationLevel1__n4
  | 5 => SearchSpace__nrofCandidates__aggregationLevel1__n5
  | 6 => SearchSpace__nrofCandidates__aggregationLevel1__n6
  | 7 => SearchSpace__nrofCandidates__aggregationLevel1__n8
  | _ => SearchSpace__nrofCandidates__aggregationLevel1__n0
  end.
Lemma SearchSpace__nrofCandidates__aggregationLevel1__F1F2 : forall x : SearchSpace__nrofCandidates__aggregationLevel1__Type, (SearchSpace__nrofCandidates__aggregationLevel1__F1 x <= 7) /\ SearchSpace__nrofCandidates__aggregationLevel1__F2 (SearchSpace__nrofCandidates__aggregationLevel1__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__nrofCandidates__aggregationLevel1__F2F1 : forall (y : nat) (H : y <= 7), SearchSpace__nrofCandidates__aggregationLevel1__F1 (SearchSpace__nrofCandidates__aggregationLevel1__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__nrofCandidates__aggregationLevel2__Type : Set :=
 | SearchSpace__nrofCandidates__aggregationLevel2__n0
 | SearchSpace__nrofCandidates__aggregationLevel2__n1
 | SearchSpace__nrofCandidates__aggregationLevel2__n2
 | SearchSpace__nrofCandidates__aggregationLevel2__n3
 | SearchSpace__nrofCandidates__aggregationLevel2__n4
 | SearchSpace__nrofCandidates__aggregationLevel2__n5
 | SearchSpace__nrofCandidates__aggregationLevel2__n6
 | SearchSpace__nrofCandidates__aggregationLevel2__n8
.
Definition SearchSpace__nrofCandidates__aggregationLevel2__cond := (fun (_ : SearchSpace__nrofCandidates__aggregationLevel2__Type) => True).
Lemma SearchSpace__nrofCandidates__aggregationLevel2__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__nrofCandidates__aggregationLevel2__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SearchSpace__nrofCandidates__aggregationLevel2__nat__helper.

Definition SearchSpace__nrofCandidates__aggregationLevel2__F1 t :=
  match t with
  | SearchSpace__nrofCandidates__aggregationLevel2__n0 => 0
  | SearchSpace__nrofCandidates__aggregationLevel2__n1 => 1
  | SearchSpace__nrofCandidates__aggregationLevel2__n2 => 2
  | SearchSpace__nrofCandidates__aggregationLevel2__n3 => 3
  | SearchSpace__nrofCandidates__aggregationLevel2__n4 => 4
  | SearchSpace__nrofCandidates__aggregationLevel2__n5 => 5
  | SearchSpace__nrofCandidates__aggregationLevel2__n6 => 6
  | SearchSpace__nrofCandidates__aggregationLevel2__n8 => 7
  end.
Definition SearchSpace__nrofCandidates__aggregationLevel2__F2 n :=
  match n with
  | 0 => SearchSpace__nrofCandidates__aggregationLevel2__n0
  | 1 => SearchSpace__nrofCandidates__aggregationLevel2__n1
  | 2 => SearchSpace__nrofCandidates__aggregationLevel2__n2
  | 3 => SearchSpace__nrofCandidates__aggregationLevel2__n3
  | 4 => SearchSpace__nrofCandidates__aggregationLevel2__n4
  | 5 => SearchSpace__nrofCandidates__aggregationLevel2__n5
  | 6 => SearchSpace__nrofCandidates__aggregationLevel2__n6
  | 7 => SearchSpace__nrofCandidates__aggregationLevel2__n8
  | _ => SearchSpace__nrofCandidates__aggregationLevel2__n0
  end.
Lemma SearchSpace__nrofCandidates__aggregationLevel2__F1F2 : forall x : SearchSpace__nrofCandidates__aggregationLevel2__Type, (SearchSpace__nrofCandidates__aggregationLevel2__F1 x <= 7) /\ SearchSpace__nrofCandidates__aggregationLevel2__F2 (SearchSpace__nrofCandidates__aggregationLevel2__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__nrofCandidates__aggregationLevel2__F2F1 : forall (y : nat) (H : y <= 7), SearchSpace__nrofCandidates__aggregationLevel2__F1 (SearchSpace__nrofCandidates__aggregationLevel2__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__nrofCandidates__aggregationLevel4__Type : Set :=
 | SearchSpace__nrofCandidates__aggregationLevel4__n0
 | SearchSpace__nrofCandidates__aggregationLevel4__n1
 | SearchSpace__nrofCandidates__aggregationLevel4__n2
 | SearchSpace__nrofCandidates__aggregationLevel4__n3
 | SearchSpace__nrofCandidates__aggregationLevel4__n4
 | SearchSpace__nrofCandidates__aggregationLevel4__n5
 | SearchSpace__nrofCandidates__aggregationLevel4__n6
 | SearchSpace__nrofCandidates__aggregationLevel4__n8
.
Definition SearchSpace__nrofCandidates__aggregationLevel4__cond := (fun (_ : SearchSpace__nrofCandidates__aggregationLevel4__Type) => True).
Lemma SearchSpace__nrofCandidates__aggregationLevel4__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__nrofCandidates__aggregationLevel4__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SearchSpace__nrofCandidates__aggregationLevel4__nat__helper.

Definition SearchSpace__nrofCandidates__aggregationLevel4__F1 t :=
  match t with
  | SearchSpace__nrofCandidates__aggregationLevel4__n0 => 0
  | SearchSpace__nrofCandidates__aggregationLevel4__n1 => 1
  | SearchSpace__nrofCandidates__aggregationLevel4__n2 => 2
  | SearchSpace__nrofCandidates__aggregationLevel4__n3 => 3
  | SearchSpace__nrofCandidates__aggregationLevel4__n4 => 4
  | SearchSpace__nrofCandidates__aggregationLevel4__n5 => 5
  | SearchSpace__nrofCandidates__aggregationLevel4__n6 => 6
  | SearchSpace__nrofCandidates__aggregationLevel4__n8 => 7
  end.
Definition SearchSpace__nrofCandidates__aggregationLevel4__F2 n :=
  match n with
  | 0 => SearchSpace__nrofCandidates__aggregationLevel4__n0
  | 1 => SearchSpace__nrofCandidates__aggregationLevel4__n1
  | 2 => SearchSpace__nrofCandidates__aggregationLevel4__n2
  | 3 => SearchSpace__nrofCandidates__aggregationLevel4__n3
  | 4 => SearchSpace__nrofCandidates__aggregationLevel4__n4
  | 5 => SearchSpace__nrofCandidates__aggregationLevel4__n5
  | 6 => SearchSpace__nrofCandidates__aggregationLevel4__n6
  | 7 => SearchSpace__nrofCandidates__aggregationLevel4__n8
  | _ => SearchSpace__nrofCandidates__aggregationLevel4__n0
  end.
Lemma SearchSpace__nrofCandidates__aggregationLevel4__F1F2 : forall x : SearchSpace__nrofCandidates__aggregationLevel4__Type, (SearchSpace__nrofCandidates__aggregationLevel4__F1 x <= 7) /\ SearchSpace__nrofCandidates__aggregationLevel4__F2 (SearchSpace__nrofCandidates__aggregationLevel4__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__nrofCandidates__aggregationLevel4__F2F1 : forall (y : nat) (H : y <= 7), SearchSpace__nrofCandidates__aggregationLevel4__F1 (SearchSpace__nrofCandidates__aggregationLevel4__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__nrofCandidates__aggregationLevel8__Type : Set :=
 | SearchSpace__nrofCandidates__aggregationLevel8__n0
 | SearchSpace__nrofCandidates__aggregationLevel8__n1
 | SearchSpace__nrofCandidates__aggregationLevel8__n2
 | SearchSpace__nrofCandidates__aggregationLevel8__n3
 | SearchSpace__nrofCandidates__aggregationLevel8__n4
 | SearchSpace__nrofCandidates__aggregationLevel8__n5
 | SearchSpace__nrofCandidates__aggregationLevel8__n6
 | SearchSpace__nrofCandidates__aggregationLevel8__n8
.
Definition SearchSpace__nrofCandidates__aggregationLevel8__cond := (fun (_ : SearchSpace__nrofCandidates__aggregationLevel8__Type) => True).
Lemma SearchSpace__nrofCandidates__aggregationLevel8__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__nrofCandidates__aggregationLevel8__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SearchSpace__nrofCandidates__aggregationLevel8__nat__helper.

Definition SearchSpace__nrofCandidates__aggregationLevel8__F1 t :=
  match t with
  | SearchSpace__nrofCandidates__aggregationLevel8__n0 => 0
  | SearchSpace__nrofCandidates__aggregationLevel8__n1 => 1
  | SearchSpace__nrofCandidates__aggregationLevel8__n2 => 2
  | SearchSpace__nrofCandidates__aggregationLevel8__n3 => 3
  | SearchSpace__nrofCandidates__aggregationLevel8__n4 => 4
  | SearchSpace__nrofCandidates__aggregationLevel8__n5 => 5
  | SearchSpace__nrofCandidates__aggregationLevel8__n6 => 6
  | SearchSpace__nrofCandidates__aggregationLevel8__n8 => 7
  end.
Definition SearchSpace__nrofCandidates__aggregationLevel8__F2 n :=
  match n with
  | 0 => SearchSpace__nrofCandidates__aggregationLevel8__n0
  | 1 => SearchSpace__nrofCandidates__aggregationLevel8__n1
  | 2 => SearchSpace__nrofCandidates__aggregationLevel8__n2
  | 3 => SearchSpace__nrofCandidates__aggregationLevel8__n3
  | 4 => SearchSpace__nrofCandidates__aggregationLevel8__n4
  | 5 => SearchSpace__nrofCandidates__aggregationLevel8__n5
  | 6 => SearchSpace__nrofCandidates__aggregationLevel8__n6
  | 7 => SearchSpace__nrofCandidates__aggregationLevel8__n8
  | _ => SearchSpace__nrofCandidates__aggregationLevel8__n0
  end.
Lemma SearchSpace__nrofCandidates__aggregationLevel8__F1F2 : forall x : SearchSpace__nrofCandidates__aggregationLevel8__Type, (SearchSpace__nrofCandidates__aggregationLevel8__F1 x <= 7) /\ SearchSpace__nrofCandidates__aggregationLevel8__F2 (SearchSpace__nrofCandidates__aggregationLevel8__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__nrofCandidates__aggregationLevel8__F2F1 : forall (y : nat) (H : y <= 7), SearchSpace__nrofCandidates__aggregationLevel8__F1 (SearchSpace__nrofCandidates__aggregationLevel8__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__nrofCandidates__aggregationLevel16__Type : Set :=
 | SearchSpace__nrofCandidates__aggregationLevel16__n0
 | SearchSpace__nrofCandidates__aggregationLevel16__n1
 | SearchSpace__nrofCandidates__aggregationLevel16__n2
 | SearchSpace__nrofCandidates__aggregationLevel16__n3
 | SearchSpace__nrofCandidates__aggregationLevel16__n4
 | SearchSpace__nrofCandidates__aggregationLevel16__n5
 | SearchSpace__nrofCandidates__aggregationLevel16__n6
 | SearchSpace__nrofCandidates__aggregationLevel16__n8
.
Definition SearchSpace__nrofCandidates__aggregationLevel16__cond := (fun (_ : SearchSpace__nrofCandidates__aggregationLevel16__Type) => True).
Lemma SearchSpace__nrofCandidates__aggregationLevel16__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__nrofCandidates__aggregationLevel16__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SearchSpace__nrofCandidates__aggregationLevel16__nat__helper.

Definition SearchSpace__nrofCandidates__aggregationLevel16__F1 t :=
  match t with
  | SearchSpace__nrofCandidates__aggregationLevel16__n0 => 0
  | SearchSpace__nrofCandidates__aggregationLevel16__n1 => 1
  | SearchSpace__nrofCandidates__aggregationLevel16__n2 => 2
  | SearchSpace__nrofCandidates__aggregationLevel16__n3 => 3
  | SearchSpace__nrofCandidates__aggregationLevel16__n4 => 4
  | SearchSpace__nrofCandidates__aggregationLevel16__n5 => 5
  | SearchSpace__nrofCandidates__aggregationLevel16__n6 => 6
  | SearchSpace__nrofCandidates__aggregationLevel16__n8 => 7
  end.
Definition SearchSpace__nrofCandidates__aggregationLevel16__F2 n :=
  match n with
  | 0 => SearchSpace__nrofCandidates__aggregationLevel16__n0
  | 1 => SearchSpace__nrofCandidates__aggregationLevel16__n1
  | 2 => SearchSpace__nrofCandidates__aggregationLevel16__n2
  | 3 => SearchSpace__nrofCandidates__aggregationLevel16__n3
  | 4 => SearchSpace__nrofCandidates__aggregationLevel16__n4
  | 5 => SearchSpace__nrofCandidates__aggregationLevel16__n5
  | 6 => SearchSpace__nrofCandidates__aggregationLevel16__n6
  | 7 => SearchSpace__nrofCandidates__aggregationLevel16__n8
  | _ => SearchSpace__nrofCandidates__aggregationLevel16__n0
  end.
Lemma SearchSpace__nrofCandidates__aggregationLevel16__F1F2 : forall x : SearchSpace__nrofCandidates__aggregationLevel16__Type, (SearchSpace__nrofCandidates__aggregationLevel16__F1 x <= 7) /\ SearchSpace__nrofCandidates__aggregationLevel16__F2 (SearchSpace__nrofCandidates__aggregationLevel16__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__nrofCandidates__aggregationLevel16__F2F1 : forall (y : nat) (H : y <= 7), SearchSpace__nrofCandidates__aggregationLevel16__F1 (SearchSpace__nrofCandidates__aggregationLevel16__F2 y) = y. enum_solve H y. Qed.

Record SearchSpace__nrofCandidates__Type : Set :=
  make__SearchSpace__nrofCandidates__Type {
    SearchSpace__nrofCandidates__aggregationLevel1 : SearchSpace__nrofCandidates__aggregationLevel1__Type ;
    SearchSpace__nrofCandidates__aggregationLevel2 : SearchSpace__nrofCandidates__aggregationLevel2__Type ;
    SearchSpace__nrofCandidates__aggregationLevel4 : SearchSpace__nrofCandidates__aggregationLevel4__Type ;
    SearchSpace__nrofCandidates__aggregationLevel8 : SearchSpace__nrofCandidates__aggregationLevel8__Type ;
    SearchSpace__nrofCandidates__aggregationLevel16 : SearchSpace__nrofCandidates__aggregationLevel16__Type ;
}.
Definition SearchSpace__nrofCandidates__list := (
 Nor SearchSpace__nrofCandidates__aggregationLevel1__Type SearchSpace__nrofCandidates__aggregationLevel1__cond ::
 Nor SearchSpace__nrofCandidates__aggregationLevel2__Type SearchSpace__nrofCandidates__aggregationLevel2__cond ::
 Nor SearchSpace__nrofCandidates__aggregationLevel4__Type SearchSpace__nrofCandidates__aggregationLevel4__cond ::
 Nor SearchSpace__nrofCandidates__aggregationLevel8__Type SearchSpace__nrofCandidates__aggregationLevel8__cond ::
 Nor SearchSpace__nrofCandidates__aggregationLevel16__Type SearchSpace__nrofCandidates__aggregationLevel16__cond ::
 nil).
Definition SearchSpace__nrofCandidates__cond z := 
  SearchSpace__nrofCandidates__aggregationLevel1__cond (SearchSpace__nrofCandidates__aggregationLevel1 z) /\
  SearchSpace__nrofCandidates__aggregationLevel2__cond (SearchSpace__nrofCandidates__aggregationLevel2 z) /\
  SearchSpace__nrofCandidates__aggregationLevel4__cond (SearchSpace__nrofCandidates__aggregationLevel4 z) /\
  SearchSpace__nrofCandidates__aggregationLevel8__cond (SearchSpace__nrofCandidates__aggregationLevel8 z) /\
  SearchSpace__nrofCandidates__aggregationLevel16__cond (SearchSpace__nrofCandidates__aggregationLevel16 z) /\
  True.

Record SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Type : Set := make__SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Type {}.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__cond (z : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Type) := True.
Record SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type : Set :=
  make__SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type {
}.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_list : list seq_elem := (
 nil).
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_list : list typ := (
  nil).
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond (z : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type) := 
(  True) /\ 
(  True).

Inductive SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Type : Set :=
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__n1
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__n2
.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__cond := (fun (_ : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Type) => True).
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__nat__helper.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__n1 => 0
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__n2 => 1
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__n1
  | 1 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__n2
  | _ => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__n1
  end.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F1F2 : forall x : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Type, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F1 x <= 1) /\ SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F2 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F2F1 : forall (y : nat) (H : y <= 1), SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F1 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Type : Set :=
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__n1
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__n2
.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__cond := (fun (_ : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Type) => True).
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__nat__helper.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__n1 => 0
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__n2 => 1
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__n1
  | 1 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__n2
  | _ => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__n1
  end.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F1F2 : forall x : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Type, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F1 x <= 1) /\ SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F2 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F2F1 : forall (y : nat) (H : y <= 1), SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F1 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Type : Set :=
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__n1
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__n2
.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__cond := (fun (_ : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Type) => True).
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__nat__helper.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__n1 => 0
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__n2 => 1
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__n1
  | 1 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__n2
  | _ => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__n1
  end.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F1F2 : forall x : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Type, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F1 x <= 1) /\ SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F2 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F2F1 : forall (y : nat) (H : y <= 1), SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F1 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Type : Set :=
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__n1
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__n2
.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__cond := (fun (_ : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Type) => True).
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__nat__helper.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__n1 => 0
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__n2 => 1
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__n1
  | 1 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__n2
  | _ => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__n1
  end.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F1F2 : forall x : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Type, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F1 x <= 1) /\ SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F2 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F2F1 : forall (y : nat) (H : y <= 1), SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F1 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Type : Set :=
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__n1
 | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__n2
.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__cond := (fun (_ : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Type) => True).
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__nat__helper.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__n1 => 0
  | SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__n2 => 1
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__n1
  | 1 => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__n2
  | _ => SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__n1
  end.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F1F2 : forall x : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Type, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F1 x <= 1) /\ SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F2 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F2F1 : forall (y : nat) (H : y <= 1), SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F1 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F2 y) = y. enum_solve H y. Qed.

Record SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Type : Set :=
  make__SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Type {
    SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1 : option SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2 : option SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4 : option SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8 : option SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16 : option SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Type ;
}.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list := (
 Opt SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__cond ::
 Opt SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__cond ::
 Opt SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__cond ::
 Opt SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__cond ::
 Opt SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__cond ::
 nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond z := 
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__cond (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1 z) /\
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__cond (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2 z) /\
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__cond (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4 z) /\
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__cond (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8 z) /\
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__cond (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16 z) /\
  True.

Record SearchSpace__searchSpaceType__common__dci_Format2_0__Type : Set :=
  make__SearchSpace__searchSpaceType__common__dci_Format2_0__Type {
    SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Type ;
}.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__root_list : list seq_elem := (
 Nor SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond ::
 nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__ext_list : list typ := (
  nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__cond (z : SearchSpace__searchSpaceType__common__dci_Format2_0__Type) := 
(  SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI z) /\
  True) /\ 
(  True).

Record SearchSpace__searchSpaceType__common__dci_Format2_1__root__Type : Set := make__SearchSpace__searchSpaceType__common__dci_Format2_1__root__Type {}.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__root__cond (z : SearchSpace__searchSpaceType__common__dci_Format2_1__root__Type) := True.
Record SearchSpace__searchSpaceType__common__dci_Format2_1__Type : Set :=
  make__SearchSpace__searchSpaceType__common__dci_Format2_1__Type {
}.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__root_list : list seq_elem := (
 nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__ext_list : list typ := (
  nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__cond (z : SearchSpace__searchSpaceType__common__dci_Format2_1__Type) := 
(  True) /\ 
(  True).

Record SearchSpace__searchSpaceType__common__dci_Format2_2__root__Type : Set := make__SearchSpace__searchSpaceType__common__dci_Format2_2__root__Type {}.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__root__cond (z : SearchSpace__searchSpaceType__common__dci_Format2_2__root__Type) := True.
Record SearchSpace__searchSpaceType__common__dci_Format2_2__Type : Set :=
  make__SearchSpace__searchSpaceType__common__dci_Format2_2__Type {
}.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__root_list : list seq_elem := (
 nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__ext_list : list typ := (
  nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__cond (z : SearchSpace__searchSpaceType__common__dci_Format2_2__Type) := 
(  True) /\ 
(  True).

Inductive SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Type : Set :=
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl1
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl2
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl4
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl5
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl8
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl10
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl16
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl20
.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__cond := (fun (_ : SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Type) => True).
Lemma SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__nat__helper : to_bit_sz 7 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__nat__Format : T_Format nat (fun z => (z <= 7)) :=
  nat_enum_format 7 SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__nat__helper.

Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl1 => 0
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl2 => 1
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl4 => 2
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl5 => 3
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl8 => 4
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl10 => 5
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl16 => 6
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl20 => 7
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl1
  | 1 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl2
  | 2 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl4
  | 3 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl5
  | 4 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl8
  | 5 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl10
  | 6 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl16
  | 7 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl20
  | _ => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__sl1
  end.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F1F2 : forall x : SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Type, (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F1 x <= 7) /\ SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F2 (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F2F1 : forall (y : nat) (H : y <= 7), SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F1 (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Type : Set :=
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__n1
 | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__n2
.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__cond := (fun (_ : SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Type) => True).
Lemma SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__nat__helper.

Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__n1 => 0
  | SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__n2 => 1
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__n1
  | 1 => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__n2
  | _ => SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__n1
  end.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F1F2 : forall x : SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Type, (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F1 x <= 1) /\ SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F2 (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F2F1 : forall (y : nat) (H : y <= 1), SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F1 (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F2 y) = y. enum_solve H y. Qed.

Record SearchSpace__searchSpaceType__common__dci_Format2_3__Type : Set :=
  make__SearchSpace__searchSpaceType__common__dci_Format2_3__Type {
    SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1 : option SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2 : SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Type ;
}.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__root_list : list seq_elem := (
 Opt SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Type SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__cond ::
 Nor SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Type SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__cond ::
 nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__ext_list : list typ := (
  nil).
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__cond (z : SearchSpace__searchSpaceType__common__dci_Format2_3__Type) := 
(  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__cond (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1 z) /\
  SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__cond (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2 z) /\
  True) /\ 
(  True).

Record SearchSpace__searchSpaceType__common__Type : Set :=
  make__SearchSpace__searchSpaceType__common__Type {
    SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0 : option SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_0 : option SearchSpace__searchSpaceType__common__dci_Format2_0__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_1 : option SearchSpace__searchSpaceType__common__dci_Format2_1__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_2 : option SearchSpace__searchSpaceType__common__dci_Format2_2__Type ;
    SearchSpace__searchSpaceType__common__dci_Format2_3 : option SearchSpace__searchSpaceType__common__dci_Format2_3__Type ;
}.
Definition SearchSpace__searchSpaceType__common__list := (
 Opt SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond ::
 Opt SearchSpace__searchSpaceType__common__dci_Format2_0__Type SearchSpace__searchSpaceType__common__dci_Format2_0__cond ::
 Opt SearchSpace__searchSpaceType__common__dci_Format2_1__Type SearchSpace__searchSpaceType__common__dci_Format2_1__cond ::
 Opt SearchSpace__searchSpaceType__common__dci_Format2_2__Type SearchSpace__searchSpaceType__common__dci_Format2_2__cond ::
 Opt SearchSpace__searchSpaceType__common__dci_Format2_3__Type SearchSpace__searchSpaceType__common__dci_Format2_3__cond ::
 nil).
Definition SearchSpace__searchSpaceType__common__cond z := 
  opt_cond SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond (SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0 z) /\
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_0__cond (SearchSpace__searchSpaceType__common__dci_Format2_0 z) /\
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_1__cond (SearchSpace__searchSpaceType__common__dci_Format2_1 z) /\
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_2__cond (SearchSpace__searchSpaceType__common__dci_Format2_2 z) /\
  opt_cond SearchSpace__searchSpaceType__common__dci_Format2_3__cond (SearchSpace__searchSpaceType__common__dci_Format2_3 z) /\
  True.

Inductive SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Type : Set :=
 | SearchSpace__searchSpaceType__ue_Specific__dci_Formats__formats0_0_And_1_0
 | SearchSpace__searchSpaceType__ue_Specific__dci_Formats__formats0_1_And_1_1
.
Definition SearchSpace__searchSpaceType__ue_Specific__dci_Formats__cond := (fun (_ : SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Type) => True).
Lemma SearchSpace__searchSpaceType__ue_Specific__dci_Formats__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__ue_Specific__dci_Formats__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpace__searchSpaceType__ue_Specific__dci_Formats__nat__helper.

Definition SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__ue_Specific__dci_Formats__formats0_0_And_1_0 => 0
  | SearchSpace__searchSpaceType__ue_Specific__dci_Formats__formats0_1_And_1_1 => 1
  end.
Definition SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__ue_Specific__dci_Formats__formats0_0_And_1_0
  | 1 => SearchSpace__searchSpaceType__ue_Specific__dci_Formats__formats0_1_And_1_1
  | _ => SearchSpace__searchSpaceType__ue_Specific__dci_Formats__formats0_0_And_1_0
  end.
Lemma SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F1F2 : forall x : SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Type, (SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F1 x <= 1) /\ SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F2 (SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F2F1 : forall (y : nat) (H : y <= 1), SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F1 (SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Type : Set :=
 | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__formats2_5
.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__cond := (fun (_ : SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Type) => True).
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__nat__helper : to_bit_sz 0 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__nat__Format : T_Format nat (fun z => (z <= 0)) :=
  nat_enum_format 0 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__nat__helper.

Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__formats2_5 => 0
  end.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__formats2_5
  | _ => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__formats2_5
  end.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F1F2 : forall x : SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Type, (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F1 x <= 0) /\ SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F2 (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F2F1 : forall (y : nat) (H : y <= 0), SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F1 (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Type : Set :=
 | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats0_0_And_1_0
 | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats0_1_And_1_1
 | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_0
 | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_1
 | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_0_And_3_1
.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__cond := (fun (_ : SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Type) => True).
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__nat__helper : to_bit_sz 4 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__nat__Format : T_Format nat (fun z => (z <= 4)) :=
  nat_enum_format 4 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__nat__helper.

Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats0_0_And_1_0 => 0
  | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats0_1_And_1_1 => 1
  | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_0 => 2
  | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_1 => 3
  | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_0_And_3_1 => 4
  end.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats0_0_And_1_0
  | 1 => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats0_1_And_1_1
  | 2 => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_0
  | 3 => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_1
  | 4 => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats3_0_And_3_1
  | _ => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__formats0_0_And_1_0
  end.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F1F2 : forall x : SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Type, (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F1 x <= 4) /\ SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F2 (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F2F1 : forall (y : nat) (H : y <= 4), SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F1 (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F2 y) = y. enum_solve H y. Qed.

Inductive SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Type : Set :=
 | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__formats0_2_And_1_2
 | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__formats0_1_And_1_1And_0_2_And_1_2
.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__cond := (fun (_ : SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Type) => True).
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__nat__helper : to_bit_sz 1 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__nat__Format : T_Format nat (fun z => (z <= 1)) :=
  nat_enum_format 1 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__nat__helper.

Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F1 t :=
  match t with
  | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__formats0_2_And_1_2 => 0
  | SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__formats0_1_And_1_1And_0_2_And_1_2 => 1
  end.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F2 n :=
  match n with
  | 0 => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__formats0_2_And_1_2
  | 1 => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__formats0_1_And_1_1And_0_2_And_1_2
  | _ => SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__formats0_2_And_1_2
  end.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F1F2 : forall x : SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Type, (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F1 x <= 1) /\ SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F2 (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F1 x) = x. imp_solve. Qed.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F2F1 : forall (y : nat) (H : y <= 1), SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F1 (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F2 y) = y. enum_solve H y. Qed.

Record SearchSpace__searchSpaceType__ue_Specific__ext0O__Type : Set :=
  make__SearchSpace__searchSpaceType__ue_Specific__ext0O__Type {
    SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16 : option SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Type ;
    SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16 : option SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Type ;
    SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16 : option SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Type ;
}.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__list := (
 Opt SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Type SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__cond ::
 Opt SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Type SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__cond ::
 Opt SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Type SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__cond ::
 nil).
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__cond z := 
  opt_cond SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__cond (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16 z) /\
  opt_cond SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__cond (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16 z) /\
  opt_cond SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__cond (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16 z) /\
  True.

Definition SearchSpace__searchSpaceType__ue_Specific__ext0__Type := SearchSpace__searchSpaceType__ue_Specific__ext0O__Type.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0__cond := SearchSpace__searchSpaceType__ue_Specific__ext0O__cond.

Record SearchSpace__searchSpaceType__ue_Specific__Type : Set :=
  make__SearchSpace__searchSpaceType__ue_Specific__Type {
    SearchSpace__searchSpaceType__ue_Specific__dci_Formats : SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Type ;
    SearchSpace__searchSpaceType__ue_Specific__ext0 : option SearchSpace__searchSpaceType__ue_Specific__ext0__Type ;
}.
Definition SearchSpace__searchSpaceType__ue_Specific__root_list : list seq_elem := (
 Nor SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Type SearchSpace__searchSpaceType__ue_Specific__dci_Formats__cond ::
 nil).
Definition SearchSpace__searchSpaceType__ue_Specific__ext_list : list typ := (
  typ_cons SearchSpace__searchSpaceType__ue_Specific__ext0__Type SearchSpace__searchSpaceType__ue_Specific__ext0__cond ::
  nil).
Definition SearchSpace__searchSpaceType__ue_Specific__cond (z : SearchSpace__searchSpaceType__ue_Specific__Type) := 
(  SearchSpace__searchSpaceType__ue_Specific__dci_Formats__cond (SearchSpace__searchSpaceType__ue_Specific__dci_Formats z) /\
  True) /\ 
(  opt_cond SearchSpace__searchSpaceType__ue_Specific__ext0__cond (SearchSpace__searchSpaceType__ue_Specific__ext0 z) /\
  True).


Inductive SearchSpace__searchSpaceType__Type : Set :=
  | SearchSpace__searchSpaceType__common : SearchSpace__searchSpaceType__common__Type -> SearchSpace__searchSpaceType__Type
  | SearchSpace__searchSpaceType__ue_Specific : SearchSpace__searchSpaceType__ue_Specific__Type -> SearchSpace__searchSpaceType__Type
.
Definition SearchSpace__searchSpaceType__list : list typ := (
typ_cons SearchSpace__searchSpaceType__common__Type SearchSpace__searchSpaceType__common__cond ::
typ_cons SearchSpace__searchSpaceType__ue_Specific__Type SearchSpace__searchSpaceType__ue_Specific__cond ::
 nil).
Definition SearchSpace__searchSpaceType__cond (c : SearchSpace__searchSpaceType__Type) := 
  match c with
  | SearchSpace__searchSpaceType__common t => SearchSpace__searchSpaceType__common__cond t 
  | SearchSpace__searchSpaceType__ue_Specific t => SearchSpace__searchSpaceType__ue_Specific__cond t 
  end.

Lemma SearchSpace__searchSpaceType__len_helper1 : to_bit_sz (length SearchSpace__searchSpaceType__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SearchSpace__searchSpaceType__len_helper2 : 2 <= length2 SearchSpace__searchSpaceType__list.
 simpl. lia. Qed.
Record SearchSpace__Type : Set :=
  make__SearchSpace__Type {
    SearchSpace__searchSpaceId : SearchSpaceId__Type ;
    SearchSpace__controlResourceSetId : option ControlResourceSetId__Type ;
    SearchSpace__monitoringSlotPeriodicityAndOffset : option SearchSpace__monitoringSlotPeriodicityAndOffset__Type ;
    SearchSpace__duration : option Z ;
    SearchSpace__monitoringSymbolsWithinSlot : option SearchSpace__monitoringSymbolsWithinSlot__Type ;
    SearchSpace__nrofCandidates : option SearchSpace__nrofCandidates__Type ;
    SearchSpace__searchSpaceType : option SearchSpace__searchSpaceType__Type ;
}.
Definition SearchSpace__list := (
 Nor SearchSpaceId__Type SearchSpaceId__cond ::
 Opt ControlResourceSetId__Type ControlResourceSetId__cond ::
 Opt SearchSpace__monitoringSlotPeriodicityAndOffset__Type SearchSpace__monitoringSlotPeriodicityAndOffset__cond ::
 Opt Z SearchSpace__duration__cond ::
 Opt SearchSpace__monitoringSymbolsWithinSlot__Type SearchSpace__monitoringSymbolsWithinSlot__cond ::
 Opt SearchSpace__nrofCandidates__Type SearchSpace__nrofCandidates__cond ::
 Opt SearchSpace__searchSpaceType__Type SearchSpace__searchSpaceType__cond ::
 nil).
Definition SearchSpace__cond z := 
  SearchSpaceId__cond (SearchSpace__searchSpaceId z) /\
  opt_cond ControlResourceSetId__cond (SearchSpace__controlResourceSetId z) /\
  opt_cond SearchSpace__monitoringSlotPeriodicityAndOffset__cond (SearchSpace__monitoringSlotPeriodicityAndOffset z) /\
  opt_cond SearchSpace__duration__cond (SearchSpace__duration z) /\
  opt_cond SearchSpace__monitoringSymbolsWithinSlot__cond (SearchSpace__monitoringSymbolsWithinSlot z) /\
  opt_cond SearchSpace__nrofCandidates__cond (SearchSpace__nrofCandidates z) /\
  opt_cond SearchSpace__searchSpaceType__cond (SearchSpace__searchSpaceType z) /\
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
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__cond :=
 ranged_int_format (0) (1) SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__cond :=
 ranged_int_format (0) (3) SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__cond :=
 ranged_int_format (0) (4) SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__cond :=
 ranged_int_format (0) (7) SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__cond :=
 ranged_int_format (0) (9) SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__cond :=
 ranged_int_format (0) (15) SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__cond :=
 ranged_int_format (0) (19) SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__cond :=
 ranged_int_format (0) (39) SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__cond :=
 ranged_int_format (0) (79) SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__cond :=
 ranged_int_format (0) (159) SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__cond :=
 ranged_int_format (0) (319) SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__cond :=
 ranged_int_format (0) (639) SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__cond :=
 ranged_int_format (0) (1279) SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__Format.

Definition SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__Format : T_Format Z SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__cond :=
 ranged_int_format (0) (2559) SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__helper2.

Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__cond SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__Format.


Definition SearchSpace__monitoringSlotPeriodicityAndOffset__Format_Type := Eval cbn in get_formats SearchSpace__monitoringSlotPeriodicityAndOffset__list.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__Format_list : SearchSpace__monitoringSlotPeriodicityAndOffset__Format_Type :=
  (unit__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl2__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl4__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl5__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl8__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl10__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl16__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl20__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl40__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl80__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl160__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl320__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl640__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560__Format, unit__Format))))))))))))))).
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__list__Format := Eval compute in choice_format SearchSpace__monitoringSlotPeriodicityAndOffset__list SearchSpace__monitoringSlotPeriodicityAndOffset__len_helper1 SearchSpace__monitoringSlotPeriodicityAndOffset__len_helper2  SearchSpace__monitoringSlotPeriodicityAndOffset__Format_list.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__F1 (z : SearchSpace__monitoringSlotPeriodicityAndOffset__Type) : (choice SearchSpace__monitoringSlotPeriodicityAndOffset__list) :=
  match z with
   | SearchSpace__monitoringSlotPeriodicityAndOffset__sl1 t => existT _ 0 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl2 t => existT _ 1 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl4 t => existT _ 2 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl5 t => existT _ 3 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl8 t => existT _ 4 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl10 t => existT _ 5 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl16 t => existT _ 6 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl20 t => existT _ 7 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl40 t => existT _ 8 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl80 t => existT _ 9 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl160 t => existT _ 10 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl320 t => existT _ 11 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl640 t => existT _ 12 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280 t => existT _ 13 t
  | SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560 t => existT _ 14 t
  end.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__g := (fun n => typ_set (get_nth_typ SearchSpace__monitoringSlotPeriodicityAndOffset__list n)).
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__F2 (y : choice SearchSpace__monitoringSlotPeriodicityAndOffset__list) : SearchSpace__monitoringSlotPeriodicityAndOffset__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SearchSpace__monitoringSlotPeriodicityAndOffset__g n -> SearchSpace__monitoringSlotPeriodicityAndOffset__Type) with
    | 0 => fun (t : unit) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl1 t 
    | 1 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl2 t 
    | 2 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl4 t 
    | 3 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl5 t 
    | 4 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl8 t 
    | 5 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl10 t 
    | 6 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl16 t 
    | 7 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl20 t 
    | 8 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl40 t 
    | 9 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl80 t 
    | 10 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl160 t 
    | 11 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl320 t 
    | 12 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl640 t 
    | 13 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl1280 t 
    | 14 => fun (t : Z) => SearchSpace__monitoringSlotPeriodicityAndOffset__sl2560 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))) => (fun (x' : nat) (t'' : SearchSpace__monitoringSlotPeriodicityAndOffset__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ SearchSpace__monitoringSlotPeriodicityAndOffset__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SearchSpace__monitoringSlotPeriodicityAndOffset__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))) in match t' return SearchSpace__monitoringSlotPeriodicityAndOffset__Type with end) n0
           end t0).

Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__helper2 :  forall (y : SearchSpace__monitoringSlotPeriodicityAndOffset__Type), SearchSpace__monitoringSlotPeriodicityAndOffset__cond y -> choice_cond SearchSpace__monitoringSlotPeriodicityAndOffset__list (SearchSpace__monitoringSlotPeriodicityAndOffset__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__helper3 :  forall (y : SearchSpace__monitoringSlotPeriodicityAndOffset__Type), SearchSpace__monitoringSlotPeriodicityAndOffset__F2 (SearchSpace__monitoringSlotPeriodicityAndOffset__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SearchSpace__monitoringSlotPeriodicityAndOffset__helper4 : (forall b : choice SearchSpace__monitoringSlotPeriodicityAndOffset__list, choice_cond SearchSpace__monitoringSlotPeriodicityAndOffset__list b -> SearchSpace__monitoringSlotPeriodicityAndOffset__cond (SearchSpace__monitoringSlotPeriodicityAndOffset__F2 b) /\ SearchSpace__monitoringSlotPeriodicityAndOffset__F1 (SearchSpace__monitoringSlotPeriodicityAndOffset__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SearchSpace__monitoringSlotPeriodicityAndOffset__F1 SearchSpace__monitoringSlotPeriodicityAndOffset__F2.
Definition SearchSpace__monitoringSlotPeriodicityAndOffset__Format : T_Format SearchSpace__monitoringSlotPeriodicityAndOffset__Type SearchSpace__monitoringSlotPeriodicityAndOffset__cond :=
  (* Eval compute in *) proj2_format SearchSpace__monitoringSlotPeriodicityAndOffset__cond SearchSpace__monitoringSlotPeriodicityAndOffset__list__Format SearchSpace__monitoringSlotPeriodicityAndOffset__F1 SearchSpace__monitoringSlotPeriodicityAndOffset__F2 SearchSpace__monitoringSlotPeriodicityAndOffset__helper2 SearchSpace__monitoringSlotPeriodicityAndOffset__helper3 SearchSpace__monitoringSlotPeriodicityAndOffset__helper4.
Opaque SearchSpace__monitoringSlotPeriodicityAndOffset__cond SearchSpace__monitoringSlotPeriodicityAndOffset__Format.

Definition SearchSpace__duration__Format : T_Format Z SearchSpace__duration__cond :=
 ranged_int_format (2) (2559) SearchSpace__duration__helper1 SearchSpace__duration__helper2.

Opaque SearchSpace__duration__cond SearchSpace__duration__Format.

Definition SearchSpace__monitoringSymbolsWithinSlot__Format : T_Format SearchSpace__monitoringSymbolsWithinSlot__Type SearchSpace__monitoringSymbolsWithinSlot__cond := (* Eval compute in *) bit_string_fixed_format 14.
Opaque SearchSpace__monitoringSymbolsWithinSlot__cond SearchSpace__monitoringSymbolsWithinSlot__Format.

Definition SearchSpace__nrofCandidates__aggregationLevel1__Format : T_Format SearchSpace__nrofCandidates__aggregationLevel1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__nrofCandidates__aggregationLevel1__nat__Format SearchSpace__nrofCandidates__aggregationLevel1__F1 SearchSpace__nrofCandidates__aggregationLevel1__F2 SearchSpace__nrofCandidates__aggregationLevel1__F1F2 SearchSpace__nrofCandidates__aggregationLevel1__F2F1.

Opaque SearchSpace__nrofCandidates__aggregationLevel1__cond SearchSpace__nrofCandidates__aggregationLevel1__Format.

Definition SearchSpace__nrofCandidates__aggregationLevel2__Format : T_Format SearchSpace__nrofCandidates__aggregationLevel2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__nrofCandidates__aggregationLevel2__nat__Format SearchSpace__nrofCandidates__aggregationLevel2__F1 SearchSpace__nrofCandidates__aggregationLevel2__F2 SearchSpace__nrofCandidates__aggregationLevel2__F1F2 SearchSpace__nrofCandidates__aggregationLevel2__F2F1.

Opaque SearchSpace__nrofCandidates__aggregationLevel2__cond SearchSpace__nrofCandidates__aggregationLevel2__Format.

Definition SearchSpace__nrofCandidates__aggregationLevel4__Format : T_Format SearchSpace__nrofCandidates__aggregationLevel4__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__nrofCandidates__aggregationLevel4__nat__Format SearchSpace__nrofCandidates__aggregationLevel4__F1 SearchSpace__nrofCandidates__aggregationLevel4__F2 SearchSpace__nrofCandidates__aggregationLevel4__F1F2 SearchSpace__nrofCandidates__aggregationLevel4__F2F1.

Opaque SearchSpace__nrofCandidates__aggregationLevel4__cond SearchSpace__nrofCandidates__aggregationLevel4__Format.

Definition SearchSpace__nrofCandidates__aggregationLevel8__Format : T_Format SearchSpace__nrofCandidates__aggregationLevel8__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__nrofCandidates__aggregationLevel8__nat__Format SearchSpace__nrofCandidates__aggregationLevel8__F1 SearchSpace__nrofCandidates__aggregationLevel8__F2 SearchSpace__nrofCandidates__aggregationLevel8__F1F2 SearchSpace__nrofCandidates__aggregationLevel8__F2F1.

Opaque SearchSpace__nrofCandidates__aggregationLevel8__cond SearchSpace__nrofCandidates__aggregationLevel8__Format.

Definition SearchSpace__nrofCandidates__aggregationLevel16__Format : T_Format SearchSpace__nrofCandidates__aggregationLevel16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__nrofCandidates__aggregationLevel16__nat__Format SearchSpace__nrofCandidates__aggregationLevel16__F1 SearchSpace__nrofCandidates__aggregationLevel16__F2 SearchSpace__nrofCandidates__aggregationLevel16__F1F2 SearchSpace__nrofCandidates__aggregationLevel16__F2F1.

Opaque SearchSpace__nrofCandidates__aggregationLevel16__cond SearchSpace__nrofCandidates__aggregationLevel16__Format.


Definition SearchSpace__nrofCandidates__Format_Type := Eval cbn in seq_format_prod SearchSpace__nrofCandidates__list.
Definition SearchSpace__nrofCandidates__Format_list : SearchSpace__nrofCandidates__Format_Type :=
  (SearchSpace__nrofCandidates__aggregationLevel1__Format, (SearchSpace__nrofCandidates__aggregationLevel2__Format, (SearchSpace__nrofCandidates__aggregationLevel4__Format, (SearchSpace__nrofCandidates__aggregationLevel8__Format, (SearchSpace__nrofCandidates__aggregationLevel16__Format, unit_format))))).
Definition SearchSpace__nrofCandidates__list__Format := (*Eval compute in *) seq_format SearchSpace__nrofCandidates__list SearchSpace__nrofCandidates__Format_list.
Definition SearchSpace__nrofCandidates__F1 z :=
  (SearchSpace__nrofCandidates__aggregationLevel1 z, (SearchSpace__nrofCandidates__aggregationLevel2 z, (SearchSpace__nrofCandidates__aggregationLevel4 z, (SearchSpace__nrofCandidates__aggregationLevel8 z, (SearchSpace__nrofCandidates__aggregationLevel16 z, tt))))).
Definition SearchSpace__nrofCandidates__F2 (y : seq_type SearchSpace__nrofCandidates__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SearchSpace__nrofCandidates__Type i0 i1 i2 i3 i4
  end.
Lemma SearchSpace__nrofCandidates__F1F2_cond (z : SearchSpace__nrofCandidates__Type)
  : SearchSpace__nrofCandidates__cond z ->
  (seq_cond SearchSpace__nrofCandidates__list (SearchSpace__nrofCandidates__F1 z)).
intro H. unfold SearchSpace__nrofCandidates__cond in H. simpl. auto. Qed.
Lemma SearchSpace__nrofCandidates__F1F2_cond2 (z : SearchSpace__nrofCandidates__Type)
 : SearchSpace__nrofCandidates__F2 (SearchSpace__nrofCandidates__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpace__nrofCandidates__F2F1_cond (y : seq_type SearchSpace__nrofCandidates__list)
  : seq_cond SearchSpace__nrofCandidates__list y ->
 (SearchSpace__nrofCandidates__cond (SearchSpace__nrofCandidates__F2 y)) /\  SearchSpace__nrofCandidates__F1 (SearchSpace__nrofCandidates__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpace__nrofCandidates__cond. simpl in *. auto.
 - simpl. unfold SearchSpace__nrofCandidates__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpace__nrofCandidates__Format : T_Format SearchSpace__nrofCandidates__Type SearchSpace__nrofCandidates__cond :=
        proj2_format  SearchSpace__nrofCandidates__cond SearchSpace__nrofCandidates__list__Format
    SearchSpace__nrofCandidates__F1 SearchSpace__nrofCandidates__F2 SearchSpace__nrofCandidates__F1F2_cond  SearchSpace__nrofCandidates__F1F2_cond2 SearchSpace__nrofCandidates__F2F1_cond.
Opaque SearchSpace__nrofCandidates__cond SearchSpace__nrofCandidates__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__helper : forall a : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Type, True -> True /\ make__SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Type SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Type)
    SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__helper unit_unique (fun _ => left I).

Opaque SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__cond SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root__Format.


Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_list.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_Format_list : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_Format_Type :=
  unit_format.

Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_Format_Type := Eval cbn in get_formats SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_list.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_Format_list : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_Format_Type :=
  unit__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_type : Set := (seq_type SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_list) * (seq_ext_type SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_list).
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_cond (z : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_type) : Prop :=
        (seq_cond SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_list (fst z)) /\ (seq_ext_cond SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_list (snd z)).
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_format : T_Format SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_type SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_list SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__root_Format_list SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_list SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__ext_Format_list.

Opaque SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_format.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F1 (z : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type) : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_type :=
  ((tt), (
tt)).
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F2 (y : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_type) : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type :=
  match y with
  | (_, _)=>
    make__SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__helper1 : (forall a : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type, SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond a -> SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_cond (SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__helper2 : (forall a : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type, SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F2 (SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__helper3 : (forall b : SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_type, SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_cond b -> SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond (SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F2 b) /\ SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F1 (SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond, SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Type SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond :=
 proj2_format SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__list_format  SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F1 SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__F2 SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__helper1 SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__helper2 SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__helper3.

Opaque SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__cond SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__nat__Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F1F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__F2F1.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__nat__Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F1F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__F2F1.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__nat__Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F1F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__F2F1.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__nat__Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F1F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__F2F1.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__nat__Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F1F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__F2F1.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Format.


Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Format_list : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Format_Type :=
  (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1__Format, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2__Format, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4__Format, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8__Format, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16__Format, unit_format))))).
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list__Format := (*Eval compute in *) seq_format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Format_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1 z :=
  (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel1 z, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel2 z, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel4 z, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel8 z, (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__aggregationLevel16 z, tt))))).
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F2 (y : seq_type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Type i0 i1 i2 i3 i4
  end.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1F2_cond (z : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Type)
  : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond z ->
  (seq_cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1 z)).
intro H. unfold SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond in H. simpl. auto. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1F2_cond2 (z : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Type)
 : SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F2 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F2F1_cond (y : seq_type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list)
  : seq_cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list y ->
 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F2 y)) /\  SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1 (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond. simpl in *. auto.
 - simpl. unfold SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Type SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond :=
        proj2_format  SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__list__Format
    SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1F2_cond  SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F1F2_cond2 SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__F2F1_cond.
Opaque SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__cond SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Format.


Definition SearchSpace__searchSpaceType__common__dci_Format2_0__root_Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__common__dci_Format2_0__root_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__root_Format_list : SearchSpace__searchSpaceType__common__dci_Format2_0__root_Format_Type :=
  (SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI__Format, unit_format).

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__ext_Format_Type := Eval cbn in get_formats SearchSpace__searchSpaceType__common__dci_Format2_0__ext_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__ext_Format_list : SearchSpace__searchSpaceType__common__dci_Format2_0__ext_Format_Type :=
  unit__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_0__list_type : Set := (seq_type SearchSpace__searchSpaceType__common__dci_Format2_0__root_list) * (seq_ext_type SearchSpace__searchSpaceType__common__dci_Format2_0__ext_list).
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__list_cond (z : SearchSpace__searchSpaceType__common__dci_Format2_0__list_type) : Prop :=
        (seq_cond SearchSpace__searchSpaceType__common__dci_Format2_0__root_list (fst z)) /\ (seq_ext_cond SearchSpace__searchSpaceType__common__dci_Format2_0__ext_list (snd z)).
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__list_format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_0__list_type SearchSpace__searchSpaceType__common__dci_Format2_0__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpace__searchSpaceType__common__dci_Format2_0__root_list SearchSpace__searchSpaceType__common__dci_Format2_0__root_Format_list SearchSpace__searchSpaceType__common__dci_Format2_0__ext_list SearchSpace__searchSpaceType__common__dci_Format2_0__ext_Format_list.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_0__list_format.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__F1 (z : SearchSpace__searchSpaceType__common__dci_Format2_0__Type) : SearchSpace__searchSpaceType__common__dci_Format2_0__list_type :=
  (((SearchSpace__searchSpaceType__common__dci_Format2_0__nrofCandidates_SFI z, tt)), (
tt)).
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__F2 (y : SearchSpace__searchSpaceType__common__dci_Format2_0__list_type) : SearchSpace__searchSpaceType__common__dci_Format2_0__Type :=
  match y with
  | ((j0, _), _)=>
    make__SearchSpace__searchSpaceType__common__dci_Format2_0__Type j0
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__helper1 : (forall a : SearchSpace__searchSpaceType__common__dci_Format2_0__Type, SearchSpace__searchSpaceType__common__dci_Format2_0__cond a -> SearchSpace__searchSpaceType__common__dci_Format2_0__list_cond (SearchSpace__searchSpaceType__common__dci_Format2_0__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__helper2 : (forall a : SearchSpace__searchSpaceType__common__dci_Format2_0__Type, SearchSpace__searchSpaceType__common__dci_Format2_0__F2 (SearchSpace__searchSpaceType__common__dci_Format2_0__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__helper3 : (forall b : SearchSpace__searchSpaceType__common__dci_Format2_0__list_type, SearchSpace__searchSpaceType__common__dci_Format2_0__list_cond b -> SearchSpace__searchSpaceType__common__dci_Format2_0__cond (SearchSpace__searchSpaceType__common__dci_Format2_0__F2 b) /\ SearchSpace__searchSpaceType__common__dci_Format2_0__F1 (SearchSpace__searchSpaceType__common__dci_Format2_0__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpace__searchSpaceType__common__dci_Format2_0__cond, SearchSpace__searchSpaceType__common__dci_Format2_0__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_0__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_0__Type SearchSpace__searchSpaceType__common__dci_Format2_0__cond :=
 proj2_format SearchSpace__searchSpaceType__common__dci_Format2_0__cond SearchSpace__searchSpaceType__common__dci_Format2_0__list_format  SearchSpace__searchSpaceType__common__dci_Format2_0__F1 SearchSpace__searchSpaceType__common__dci_Format2_0__F2 SearchSpace__searchSpaceType__common__dci_Format2_0__helper1 SearchSpace__searchSpaceType__common__dci_Format2_0__helper2 SearchSpace__searchSpaceType__common__dci_Format2_0__helper3.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_0__cond SearchSpace__searchSpaceType__common__dci_Format2_0__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_1__root__helper : forall a : SearchSpace__searchSpaceType__common__dci_Format2_1__root__Type, True -> True /\ make__SearchSpace__searchSpaceType__common__dci_Format2_1__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__root__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_1__root__Type SearchSpace__searchSpaceType__common__dci_Format2_1__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SearchSpace__searchSpaceType__common__dci_Format2_1__root__Type)
    SearchSpace__searchSpaceType__common__dci_Format2_1__root__helper unit_unique (fun _ => left I).

Opaque SearchSpace__searchSpaceType__common__dci_Format2_1__root__cond SearchSpace__searchSpaceType__common__dci_Format2_1__root__Format.


Definition SearchSpace__searchSpaceType__common__dci_Format2_1__root_Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__common__dci_Format2_1__root_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__root_Format_list : SearchSpace__searchSpaceType__common__dci_Format2_1__root_Format_Type :=
  unit_format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_1__ext_Format_Type := Eval cbn in get_formats SearchSpace__searchSpaceType__common__dci_Format2_1__ext_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__ext_Format_list : SearchSpace__searchSpaceType__common__dci_Format2_1__ext_Format_Type :=
  unit__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_1__list_type : Set := (seq_type SearchSpace__searchSpaceType__common__dci_Format2_1__root_list) * (seq_ext_type SearchSpace__searchSpaceType__common__dci_Format2_1__ext_list).
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__list_cond (z : SearchSpace__searchSpaceType__common__dci_Format2_1__list_type) : Prop :=
        (seq_cond SearchSpace__searchSpaceType__common__dci_Format2_1__root_list (fst z)) /\ (seq_ext_cond SearchSpace__searchSpaceType__common__dci_Format2_1__ext_list (snd z)).
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__list_format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_1__list_type SearchSpace__searchSpaceType__common__dci_Format2_1__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpace__searchSpaceType__common__dci_Format2_1__root_list SearchSpace__searchSpaceType__common__dci_Format2_1__root_Format_list SearchSpace__searchSpaceType__common__dci_Format2_1__ext_list SearchSpace__searchSpaceType__common__dci_Format2_1__ext_Format_list.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_1__list_format.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__F1 (z : SearchSpace__searchSpaceType__common__dci_Format2_1__Type) : SearchSpace__searchSpaceType__common__dci_Format2_1__list_type :=
  ((tt), (
tt)).
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__F2 (y : SearchSpace__searchSpaceType__common__dci_Format2_1__list_type) : SearchSpace__searchSpaceType__common__dci_Format2_1__Type :=
  match y with
  | (_, _)=>
    make__SearchSpace__searchSpaceType__common__dci_Format2_1__Type
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__helper1 : (forall a : SearchSpace__searchSpaceType__common__dci_Format2_1__Type, SearchSpace__searchSpaceType__common__dci_Format2_1__cond a -> SearchSpace__searchSpaceType__common__dci_Format2_1__list_cond (SearchSpace__searchSpaceType__common__dci_Format2_1__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__helper2 : (forall a : SearchSpace__searchSpaceType__common__dci_Format2_1__Type, SearchSpace__searchSpaceType__common__dci_Format2_1__F2 (SearchSpace__searchSpaceType__common__dci_Format2_1__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__helper3 : (forall b : SearchSpace__searchSpaceType__common__dci_Format2_1__list_type, SearchSpace__searchSpaceType__common__dci_Format2_1__list_cond b -> SearchSpace__searchSpaceType__common__dci_Format2_1__cond (SearchSpace__searchSpaceType__common__dci_Format2_1__F2 b) /\ SearchSpace__searchSpaceType__common__dci_Format2_1__F1 (SearchSpace__searchSpaceType__common__dci_Format2_1__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpace__searchSpaceType__common__dci_Format2_1__cond, SearchSpace__searchSpaceType__common__dci_Format2_1__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_1__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_1__Type SearchSpace__searchSpaceType__common__dci_Format2_1__cond :=
 proj2_format SearchSpace__searchSpaceType__common__dci_Format2_1__cond SearchSpace__searchSpaceType__common__dci_Format2_1__list_format  SearchSpace__searchSpaceType__common__dci_Format2_1__F1 SearchSpace__searchSpaceType__common__dci_Format2_1__F2 SearchSpace__searchSpaceType__common__dci_Format2_1__helper1 SearchSpace__searchSpaceType__common__dci_Format2_1__helper2 SearchSpace__searchSpaceType__common__dci_Format2_1__helper3.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_1__cond SearchSpace__searchSpaceType__common__dci_Format2_1__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_2__root__helper : forall a : SearchSpace__searchSpaceType__common__dci_Format2_2__root__Type, True -> True /\ make__SearchSpace__searchSpaceType__common__dci_Format2_2__root__Type = a.
  eq_unit_helper_tact. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__root__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_2__root__Type SearchSpace__searchSpaceType__common__dci_Format2_2__root__cond :=
 (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__SearchSpace__searchSpaceType__common__dci_Format2_2__root__Type)
    SearchSpace__searchSpaceType__common__dci_Format2_2__root__helper unit_unique (fun _ => left I).

Opaque SearchSpace__searchSpaceType__common__dci_Format2_2__root__cond SearchSpace__searchSpaceType__common__dci_Format2_2__root__Format.


Definition SearchSpace__searchSpaceType__common__dci_Format2_2__root_Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__common__dci_Format2_2__root_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__root_Format_list : SearchSpace__searchSpaceType__common__dci_Format2_2__root_Format_Type :=
  unit_format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_2__ext_Format_Type := Eval cbn in get_formats SearchSpace__searchSpaceType__common__dci_Format2_2__ext_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__ext_Format_list : SearchSpace__searchSpaceType__common__dci_Format2_2__ext_Format_Type :=
  unit__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_2__list_type : Set := (seq_type SearchSpace__searchSpaceType__common__dci_Format2_2__root_list) * (seq_ext_type SearchSpace__searchSpaceType__common__dci_Format2_2__ext_list).
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__list_cond (z : SearchSpace__searchSpaceType__common__dci_Format2_2__list_type) : Prop :=
        (seq_cond SearchSpace__searchSpaceType__common__dci_Format2_2__root_list (fst z)) /\ (seq_ext_cond SearchSpace__searchSpaceType__common__dci_Format2_2__ext_list (snd z)).
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__list_format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_2__list_type SearchSpace__searchSpaceType__common__dci_Format2_2__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpace__searchSpaceType__common__dci_Format2_2__root_list SearchSpace__searchSpaceType__common__dci_Format2_2__root_Format_list SearchSpace__searchSpaceType__common__dci_Format2_2__ext_list SearchSpace__searchSpaceType__common__dci_Format2_2__ext_Format_list.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_2__list_format.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__F1 (z : SearchSpace__searchSpaceType__common__dci_Format2_2__Type) : SearchSpace__searchSpaceType__common__dci_Format2_2__list_type :=
  ((tt), (
tt)).
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__F2 (y : SearchSpace__searchSpaceType__common__dci_Format2_2__list_type) : SearchSpace__searchSpaceType__common__dci_Format2_2__Type :=
  match y with
  | (_, _)=>
    make__SearchSpace__searchSpaceType__common__dci_Format2_2__Type
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__helper1 : (forall a : SearchSpace__searchSpaceType__common__dci_Format2_2__Type, SearchSpace__searchSpaceType__common__dci_Format2_2__cond a -> SearchSpace__searchSpaceType__common__dci_Format2_2__list_cond (SearchSpace__searchSpaceType__common__dci_Format2_2__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__helper2 : (forall a : SearchSpace__searchSpaceType__common__dci_Format2_2__Type, SearchSpace__searchSpaceType__common__dci_Format2_2__F2 (SearchSpace__searchSpaceType__common__dci_Format2_2__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__helper3 : (forall b : SearchSpace__searchSpaceType__common__dci_Format2_2__list_type, SearchSpace__searchSpaceType__common__dci_Format2_2__list_cond b -> SearchSpace__searchSpaceType__common__dci_Format2_2__cond (SearchSpace__searchSpaceType__common__dci_Format2_2__F2 b) /\ SearchSpace__searchSpaceType__common__dci_Format2_2__F1 (SearchSpace__searchSpaceType__common__dci_Format2_2__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpace__searchSpaceType__common__dci_Format2_2__cond, SearchSpace__searchSpaceType__common__dci_Format2_2__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_2__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_2__Type SearchSpace__searchSpaceType__common__dci_Format2_2__cond :=
 proj2_format SearchSpace__searchSpaceType__common__dci_Format2_2__cond SearchSpace__searchSpaceType__common__dci_Format2_2__list_format  SearchSpace__searchSpaceType__common__dci_Format2_2__F1 SearchSpace__searchSpaceType__common__dci_Format2_2__F2 SearchSpace__searchSpaceType__common__dci_Format2_2__helper1 SearchSpace__searchSpaceType__common__dci_Format2_2__helper2 SearchSpace__searchSpaceType__common__dci_Format2_2__helper3.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_2__cond SearchSpace__searchSpaceType__common__dci_Format2_2__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__nat__Format SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F1 SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F2 SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F1F2 SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__F2F1.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__cond SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__nat__Format SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F1 SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F2 SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F1F2 SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__F2F1.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__cond SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Format.


Definition SearchSpace__searchSpaceType__common__dci_Format2_3__root_Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__common__dci_Format2_3__root_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__root_Format_list : SearchSpace__searchSpaceType__common__dci_Format2_3__root_Format_Type :=
  (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1__Format, (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2__Format, unit_format)).

Definition SearchSpace__searchSpaceType__common__dci_Format2_3__ext_Format_Type := Eval cbn in get_formats SearchSpace__searchSpaceType__common__dci_Format2_3__ext_list.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__ext_Format_list : SearchSpace__searchSpaceType__common__dci_Format2_3__ext_Format_Type :=
  unit__Format.

Definition SearchSpace__searchSpaceType__common__dci_Format2_3__list_type : Set := (seq_type SearchSpace__searchSpaceType__common__dci_Format2_3__root_list) * (seq_ext_type SearchSpace__searchSpaceType__common__dci_Format2_3__ext_list).
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__list_cond (z : SearchSpace__searchSpaceType__common__dci_Format2_3__list_type) : Prop :=
        (seq_cond SearchSpace__searchSpaceType__common__dci_Format2_3__root_list (fst z)) /\ (seq_ext_cond SearchSpace__searchSpaceType__common__dci_Format2_3__ext_list (snd z)).
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__list_format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_3__list_type SearchSpace__searchSpaceType__common__dci_Format2_3__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpace__searchSpaceType__common__dci_Format2_3__root_list SearchSpace__searchSpaceType__common__dci_Format2_3__root_Format_list SearchSpace__searchSpaceType__common__dci_Format2_3__ext_list SearchSpace__searchSpaceType__common__dci_Format2_3__ext_Format_list.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_3__list_format.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__F1 (z : SearchSpace__searchSpaceType__common__dci_Format2_3__Type) : SearchSpace__searchSpaceType__common__dci_Format2_3__list_type :=
  (((SearchSpace__searchSpaceType__common__dci_Format2_3__dummy1 z, (SearchSpace__searchSpaceType__common__dci_Format2_3__dummy2 z, tt))), (
tt)).
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__F2 (y : SearchSpace__searchSpaceType__common__dci_Format2_3__list_type) : SearchSpace__searchSpaceType__common__dci_Format2_3__Type :=
  match y with
  | ((j0, (j1, _)), _)=>
    make__SearchSpace__searchSpaceType__common__dci_Format2_3__Type j0 j1
  end.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__helper1 : (forall a : SearchSpace__searchSpaceType__common__dci_Format2_3__Type, SearchSpace__searchSpaceType__common__dci_Format2_3__cond a -> SearchSpace__searchSpaceType__common__dci_Format2_3__list_cond (SearchSpace__searchSpaceType__common__dci_Format2_3__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__helper2 : (forall a : SearchSpace__searchSpaceType__common__dci_Format2_3__Type, SearchSpace__searchSpaceType__common__dci_Format2_3__F2 (SearchSpace__searchSpaceType__common__dci_Format2_3__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__helper3 : (forall b : SearchSpace__searchSpaceType__common__dci_Format2_3__list_type, SearchSpace__searchSpaceType__common__dci_Format2_3__list_cond b -> SearchSpace__searchSpaceType__common__dci_Format2_3__cond (SearchSpace__searchSpaceType__common__dci_Format2_3__F2 b) /\ SearchSpace__searchSpaceType__common__dci_Format2_3__F1 (SearchSpace__searchSpaceType__common__dci_Format2_3__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpace__searchSpaceType__common__dci_Format2_3__cond, SearchSpace__searchSpaceType__common__dci_Format2_3__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpace__searchSpaceType__common__dci_Format2_3__Format : T_Format SearchSpace__searchSpaceType__common__dci_Format2_3__Type SearchSpace__searchSpaceType__common__dci_Format2_3__cond :=
 proj2_format SearchSpace__searchSpaceType__common__dci_Format2_3__cond SearchSpace__searchSpaceType__common__dci_Format2_3__list_format  SearchSpace__searchSpaceType__common__dci_Format2_3__F1 SearchSpace__searchSpaceType__common__dci_Format2_3__F2 SearchSpace__searchSpaceType__common__dci_Format2_3__helper1 SearchSpace__searchSpaceType__common__dci_Format2_3__helper2 SearchSpace__searchSpaceType__common__dci_Format2_3__helper3.

Opaque SearchSpace__searchSpaceType__common__dci_Format2_3__cond SearchSpace__searchSpaceType__common__dci_Format2_3__Format.


Definition SearchSpace__searchSpaceType__common__Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__common__list.
Definition SearchSpace__searchSpaceType__common__Format_list : SearchSpace__searchSpaceType__common__Format_Type :=
  (SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0__Format, (SearchSpace__searchSpaceType__common__dci_Format2_0__Format, (SearchSpace__searchSpaceType__common__dci_Format2_1__Format, (SearchSpace__searchSpaceType__common__dci_Format2_2__Format, (SearchSpace__searchSpaceType__common__dci_Format2_3__Format, unit_format))))).
Definition SearchSpace__searchSpaceType__common__list__Format := (*Eval compute in *) seq_format SearchSpace__searchSpaceType__common__list SearchSpace__searchSpaceType__common__Format_list.
Definition SearchSpace__searchSpaceType__common__F1 z :=
  (SearchSpace__searchSpaceType__common__dci_Format0_0_AndFormat1_0 z, (SearchSpace__searchSpaceType__common__dci_Format2_0 z, (SearchSpace__searchSpaceType__common__dci_Format2_1 z, (SearchSpace__searchSpaceType__common__dci_Format2_2 z, (SearchSpace__searchSpaceType__common__dci_Format2_3 z, tt))))).
Definition SearchSpace__searchSpaceType__common__F2 (y : seq_type SearchSpace__searchSpaceType__common__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__SearchSpace__searchSpaceType__common__Type i0 i1 i2 i3 i4
  end.
Lemma SearchSpace__searchSpaceType__common__F1F2_cond (z : SearchSpace__searchSpaceType__common__Type)
  : SearchSpace__searchSpaceType__common__cond z ->
  (seq_cond SearchSpace__searchSpaceType__common__list (SearchSpace__searchSpaceType__common__F1 z)).
intro H. unfold SearchSpace__searchSpaceType__common__cond in H. simpl. auto. Qed.
Lemma SearchSpace__searchSpaceType__common__F1F2_cond2 (z : SearchSpace__searchSpaceType__common__Type)
 : SearchSpace__searchSpaceType__common__F2 (SearchSpace__searchSpaceType__common__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpace__searchSpaceType__common__F2F1_cond (y : seq_type SearchSpace__searchSpaceType__common__list)
  : seq_cond SearchSpace__searchSpaceType__common__list y ->
 (SearchSpace__searchSpaceType__common__cond (SearchSpace__searchSpaceType__common__F2 y)) /\  SearchSpace__searchSpaceType__common__F1 (SearchSpace__searchSpaceType__common__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpace__searchSpaceType__common__cond. simpl in *. auto.
 - simpl. unfold SearchSpace__searchSpaceType__common__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpace__searchSpaceType__common__Format : T_Format SearchSpace__searchSpaceType__common__Type SearchSpace__searchSpaceType__common__cond :=
        proj2_format  SearchSpace__searchSpaceType__common__cond SearchSpace__searchSpaceType__common__list__Format
    SearchSpace__searchSpaceType__common__F1 SearchSpace__searchSpaceType__common__F2 SearchSpace__searchSpaceType__common__F1F2_cond  SearchSpace__searchSpaceType__common__F1F2_cond2 SearchSpace__searchSpaceType__common__F2F1_cond.
Opaque SearchSpace__searchSpaceType__common__cond SearchSpace__searchSpaceType__common__Format.

Definition SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Format : T_Format SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__ue_Specific__dci_Formats__nat__Format SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F1 SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F2 SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F1F2 SearchSpace__searchSpaceType__ue_Specific__dci_Formats__F2F1.

Opaque SearchSpace__searchSpaceType__ue_Specific__dci_Formats__cond SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Format.

Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Format : T_Format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__nat__Format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F1 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F2 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F1F2 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__F2F1.

Opaque SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__cond SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Format.

Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Format : T_Format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__nat__Format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F1 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F2 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F1F2 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__F2F1.

Opaque SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__cond SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Format.

Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Format : T_Format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Type (fun _ => True) :=
(* Eval compute in *) proj3_format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__nat__Format SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F1 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F2 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F1F2 SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__F2F1.

Opaque SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__cond SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Format.


Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__ue_Specific__ext0O__list.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__Format_list : SearchSpace__searchSpaceType__ue_Specific__ext0O__Format_Type :=
  (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16__Format, (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16__Format, (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16__Format, unit_format))).
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__list__Format := (*Eval compute in *) seq_format SearchSpace__searchSpaceType__ue_Specific__ext0O__list SearchSpace__searchSpaceType__ue_Specific__ext0O__Format_list.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__F1 z :=
  (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_Formats_MT_r16 z, (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsSL_r16 z, (SearchSpace__searchSpaceType__ue_Specific__ext0O__dci_FormatsExt_r16 z, tt))).
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__F2 (y : seq_type SearchSpace__searchSpaceType__ue_Specific__ext0O__list) :=
  match y with
  | (i0, (i1, (i2, _)))=>
    make__SearchSpace__searchSpaceType__ue_Specific__ext0O__Type i0 i1 i2
  end.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__F1F2_cond (z : SearchSpace__searchSpaceType__ue_Specific__ext0O__Type)
  : SearchSpace__searchSpaceType__ue_Specific__ext0O__cond z ->
  (seq_cond SearchSpace__searchSpaceType__ue_Specific__ext0O__list (SearchSpace__searchSpaceType__ue_Specific__ext0O__F1 z)).
intro H. unfold SearchSpace__searchSpaceType__ue_Specific__ext0O__cond in H. simpl. auto. Qed.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__F1F2_cond2 (z : SearchSpace__searchSpaceType__ue_Specific__ext0O__Type)
 : SearchSpace__searchSpaceType__ue_Specific__ext0O__F2 (SearchSpace__searchSpaceType__ue_Specific__ext0O__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpace__searchSpaceType__ue_Specific__ext0O__F2F1_cond (y : seq_type SearchSpace__searchSpaceType__ue_Specific__ext0O__list)
  : seq_cond SearchSpace__searchSpaceType__ue_Specific__ext0O__list y ->
 (SearchSpace__searchSpaceType__ue_Specific__ext0O__cond (SearchSpace__searchSpaceType__ue_Specific__ext0O__F2 y)) /\  SearchSpace__searchSpaceType__ue_Specific__ext0O__F1 (SearchSpace__searchSpaceType__ue_Specific__ext0O__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpace__searchSpaceType__ue_Specific__ext0O__cond. simpl in *. auto.
 - simpl. unfold SearchSpace__searchSpaceType__ue_Specific__ext0O__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0O__Format : T_Format SearchSpace__searchSpaceType__ue_Specific__ext0O__Type SearchSpace__searchSpaceType__ue_Specific__ext0O__cond :=
        proj2_format  SearchSpace__searchSpaceType__ue_Specific__ext0O__cond SearchSpace__searchSpaceType__ue_Specific__ext0O__list__Format
    SearchSpace__searchSpaceType__ue_Specific__ext0O__F1 SearchSpace__searchSpaceType__ue_Specific__ext0O__F2 SearchSpace__searchSpaceType__ue_Specific__ext0O__F1F2_cond  SearchSpace__searchSpaceType__ue_Specific__ext0O__F1F2_cond2 SearchSpace__searchSpaceType__ue_Specific__ext0O__F2F1_cond.
Opaque SearchSpace__searchSpaceType__ue_Specific__ext0O__cond SearchSpace__searchSpaceType__ue_Specific__ext0O__Format.

Definition SearchSpace__searchSpaceType__ue_Specific__ext0__check_all_none (b : SearchSpace__searchSpaceType__ue_Specific__ext0O__Type) : bool :=
match b with 
  | make__SearchSpace__searchSpaceType__ue_Specific__ext0O__Type None None None  => false 
  | _ => true 
 end.
Definition SearchSpace__searchSpaceType__ue_Specific__ext0__Format : T_Format SearchSpace__searchSpaceType__ue_Specific__ext0__Type SearchSpace__searchSpaceType__ue_Specific__ext0__cond :=
  restrict_add_format SearchSpace__searchSpaceType__ue_Specific__ext0__check_all_none SearchSpace__searchSpaceType__ue_Specific__ext0O__Format.

Opaque SearchSpace__searchSpaceType__ue_Specific__ext0__cond SearchSpace__searchSpaceType__ue_Specific__ext0__Format.


Definition SearchSpace__searchSpaceType__ue_Specific__root_Format_Type := Eval cbn in seq_format_prod SearchSpace__searchSpaceType__ue_Specific__root_list.
Definition SearchSpace__searchSpaceType__ue_Specific__root_Format_list : SearchSpace__searchSpaceType__ue_Specific__root_Format_Type :=
  (SearchSpace__searchSpaceType__ue_Specific__dci_Formats__Format, unit_format).

Definition SearchSpace__searchSpaceType__ue_Specific__ext_Format_Type := Eval cbn in get_formats SearchSpace__searchSpaceType__ue_Specific__ext_list.
Definition SearchSpace__searchSpaceType__ue_Specific__ext_Format_list : SearchSpace__searchSpaceType__ue_Specific__ext_Format_Type :=
  (SearchSpace__searchSpaceType__ue_Specific__ext0__Format, unit__Format).

Definition SearchSpace__searchSpaceType__ue_Specific__list_type : Set := (seq_type SearchSpace__searchSpaceType__ue_Specific__root_list) * (seq_ext_type SearchSpace__searchSpaceType__ue_Specific__ext_list).
Definition SearchSpace__searchSpaceType__ue_Specific__list_cond (z : SearchSpace__searchSpaceType__ue_Specific__list_type) : Prop :=
        (seq_cond SearchSpace__searchSpaceType__ue_Specific__root_list (fst z)) /\ (seq_ext_cond SearchSpace__searchSpaceType__ue_Specific__ext_list (snd z)).
Definition SearchSpace__searchSpaceType__ue_Specific__list_format : T_Format SearchSpace__searchSpaceType__ue_Specific__list_type SearchSpace__searchSpaceType__ue_Specific__list_cond :=
 (* Eval compute in *) seq_ext_format SearchSpace__searchSpaceType__ue_Specific__root_list SearchSpace__searchSpaceType__ue_Specific__root_Format_list SearchSpace__searchSpaceType__ue_Specific__ext_list SearchSpace__searchSpaceType__ue_Specific__ext_Format_list.

Opaque SearchSpace__searchSpaceType__ue_Specific__list_format.
Definition SearchSpace__searchSpaceType__ue_Specific__F1 (z : SearchSpace__searchSpaceType__ue_Specific__Type) : SearchSpace__searchSpaceType__ue_Specific__list_type :=
  (((SearchSpace__searchSpaceType__ue_Specific__dci_Formats z, tt)), (
(SearchSpace__searchSpaceType__ue_Specific__ext0 z, tt))).
Definition SearchSpace__searchSpaceType__ue_Specific__F2 (y : SearchSpace__searchSpaceType__ue_Specific__list_type) : SearchSpace__searchSpaceType__ue_Specific__Type :=
  match y with
  | ((j0, _), (i0, _))=>
    make__SearchSpace__searchSpaceType__ue_Specific__Type j0 i0
  end.
Definition SearchSpace__searchSpaceType__ue_Specific__helper1 : (forall a : SearchSpace__searchSpaceType__ue_Specific__Type, SearchSpace__searchSpaceType__ue_Specific__cond a -> SearchSpace__searchSpaceType__ue_Specific__list_cond (SearchSpace__searchSpaceType__ue_Specific__F1 a)).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__ue_Specific__helper2 : (forall a : SearchSpace__searchSpaceType__ue_Specific__Type, SearchSpace__searchSpaceType__ue_Specific__F2 (SearchSpace__searchSpaceType__ue_Specific__F1 a) = a).
                     intros. destruct a. auto. Qed.
Definition SearchSpace__searchSpaceType__ue_Specific__helper3 : (forall b : SearchSpace__searchSpaceType__ue_Specific__list_type, SearchSpace__searchSpaceType__ue_Specific__list_cond b -> SearchSpace__searchSpaceType__ue_Specific__cond (SearchSpace__searchSpaceType__ue_Specific__F2 b) /\ SearchSpace__searchSpaceType__ue_Specific__F1 (SearchSpace__searchSpaceType__ue_Specific__F2 b) = b).
                     intros. destruct b as [y y1]. unfold SearchSpace__searchSpaceType__ue_Specific__cond, SearchSpace__searchSpaceType__ue_Specific__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). 

                     Qed.
Definition SearchSpace__searchSpaceType__ue_Specific__Format : T_Format SearchSpace__searchSpaceType__ue_Specific__Type SearchSpace__searchSpaceType__ue_Specific__cond :=
 proj2_format SearchSpace__searchSpaceType__ue_Specific__cond SearchSpace__searchSpaceType__ue_Specific__list_format  SearchSpace__searchSpaceType__ue_Specific__F1 SearchSpace__searchSpaceType__ue_Specific__F2 SearchSpace__searchSpaceType__ue_Specific__helper1 SearchSpace__searchSpaceType__ue_Specific__helper2 SearchSpace__searchSpaceType__ue_Specific__helper3.

Opaque SearchSpace__searchSpaceType__ue_Specific__cond SearchSpace__searchSpaceType__ue_Specific__Format.


Definition SearchSpace__searchSpaceType__Format_Type := Eval cbn in get_formats SearchSpace__searchSpaceType__list.
Definition SearchSpace__searchSpaceType__Format_list : SearchSpace__searchSpaceType__Format_Type :=
  (SearchSpace__searchSpaceType__common__Format, (SearchSpace__searchSpaceType__ue_Specific__Format, unit__Format)).
Definition SearchSpace__searchSpaceType__list__Format := Eval compute in choice_format SearchSpace__searchSpaceType__list SearchSpace__searchSpaceType__len_helper1 SearchSpace__searchSpaceType__len_helper2  SearchSpace__searchSpaceType__Format_list.
Definition SearchSpace__searchSpaceType__F1 (z : SearchSpace__searchSpaceType__Type) : (choice SearchSpace__searchSpaceType__list) :=
  match z with
   | SearchSpace__searchSpaceType__common t => existT _ 0 t
  | SearchSpace__searchSpaceType__ue_Specific t => existT _ 1 t
  end.
Definition SearchSpace__searchSpaceType__g := (fun n => typ_set (get_nth_typ SearchSpace__searchSpaceType__list n)).
Definition SearchSpace__searchSpaceType__F2 (y : choice SearchSpace__searchSpaceType__list) : SearchSpace__searchSpaceType__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SearchSpace__searchSpaceType__g n -> SearchSpace__searchSpaceType__Type) with
    | 0 => fun (t : SearchSpace__searchSpaceType__common__Type) => SearchSpace__searchSpaceType__common t 
    | 1 => fun (t : SearchSpace__searchSpaceType__ue_Specific__Type) => SearchSpace__searchSpaceType__ue_Specific t 
 | (S (S n0)) => (fun (x' : nat) (t'' : SearchSpace__searchSpaceType__g (S (S x'))) =>let t' :=
           eq_rect (get_nth_typ SearchSpace__searchSpaceType__list (S (S x')))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SearchSpace__searchSpaceType__list (S (S x'))
           (le_n_S _ _ (le_n_S _ _ (le_0_n x')))) in match t' return SearchSpace__searchSpaceType__Type with end) n0
           end t0).

Lemma SearchSpace__searchSpaceType__helper2 :  forall (y : SearchSpace__searchSpaceType__Type), SearchSpace__searchSpaceType__cond y -> choice_cond SearchSpace__searchSpaceType__list (SearchSpace__searchSpaceType__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SearchSpace__searchSpaceType__helper3 :  forall (y : SearchSpace__searchSpaceType__Type), SearchSpace__searchSpaceType__F2 (SearchSpace__searchSpaceType__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SearchSpace__searchSpaceType__helper4 : (forall b : choice SearchSpace__searchSpaceType__list, choice_cond SearchSpace__searchSpaceType__list b -> SearchSpace__searchSpaceType__cond (SearchSpace__searchSpaceType__F2 b) /\ SearchSpace__searchSpaceType__F1 (SearchSpace__searchSpaceType__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SearchSpace__searchSpaceType__F1 SearchSpace__searchSpaceType__F2.
Definition SearchSpace__searchSpaceType__Format : T_Format SearchSpace__searchSpaceType__Type SearchSpace__searchSpaceType__cond :=
  (* Eval compute in *) proj2_format SearchSpace__searchSpaceType__cond SearchSpace__searchSpaceType__list__Format SearchSpace__searchSpaceType__F1 SearchSpace__searchSpaceType__F2 SearchSpace__searchSpaceType__helper2 SearchSpace__searchSpaceType__helper3 SearchSpace__searchSpaceType__helper4.
Opaque SearchSpace__searchSpaceType__cond SearchSpace__searchSpaceType__Format.


Definition SearchSpace__Format_Type := Eval cbn in seq_format_prod SearchSpace__list.
Definition SearchSpace__Format_list : SearchSpace__Format_Type :=
  (SearchSpaceId__Format, (ControlResourceSetId__Format, (SearchSpace__monitoringSlotPeriodicityAndOffset__Format, (SearchSpace__duration__Format, (SearchSpace__monitoringSymbolsWithinSlot__Format, (SearchSpace__nrofCandidates__Format, (SearchSpace__searchSpaceType__Format, unit_format))))))).
Definition SearchSpace__list__Format := (*Eval compute in *) seq_format SearchSpace__list SearchSpace__Format_list.
Definition SearchSpace__F1 z :=
  (SearchSpace__searchSpaceId z, (SearchSpace__controlResourceSetId z, (SearchSpace__monitoringSlotPeriodicityAndOffset z, (SearchSpace__duration z, (SearchSpace__monitoringSymbolsWithinSlot z, (SearchSpace__nrofCandidates z, (SearchSpace__searchSpaceType z, tt))))))).
Definition SearchSpace__F2 (y : seq_type SearchSpace__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, (i5, (i6, _)))))))=>
    make__SearchSpace__Type i0 i1 i2 i3 i4 i5 i6
  end.
Lemma SearchSpace__F1F2_cond (z : SearchSpace__Type)
  : SearchSpace__cond z ->
  (seq_cond SearchSpace__list (SearchSpace__F1 z)).
intro H. unfold SearchSpace__cond in H. simpl. auto. Qed.
Lemma SearchSpace__F1F2_cond2 (z : SearchSpace__Type)
 : SearchSpace__F2 (SearchSpace__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma SearchSpace__F2F1_cond (y : seq_type SearchSpace__list)
  : seq_cond SearchSpace__list y ->
 (SearchSpace__cond (SearchSpace__F2 y)) /\  SearchSpace__F1 (SearchSpace__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold SearchSpace__cond. simpl in *. auto.
 - simpl. unfold SearchSpace__F1. simpl. destruct_all_unit. auto.   Qed.
Definition SearchSpace__Format : T_Format SearchSpace__Type SearchSpace__cond :=
        proj2_format  SearchSpace__cond SearchSpace__list__Format
    SearchSpace__F1 SearchSpace__F2 SearchSpace__F1F2_cond  SearchSpace__F1F2_cond2 SearchSpace__F2F1_cond.
Opaque SearchSpace__cond SearchSpace__Format.

