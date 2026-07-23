Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma SRS_PeriodicityAndOffset_r16__root__sl2__helper1 : (0 <= 1)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl2__helper2 : to_bit_sz (Z.to_nat (1 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl2__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl2__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl2__cond := (fun z => (0 <= z <= 1)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl4__helper1 : (0 <= 3)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl4__helper2 : to_bit_sz (Z.to_nat (3 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (3 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl4__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl4__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl4__cond := (fun z => (0 <= z <= 3)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl5__helper1 : (0 <= 4)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl5__helper2 : to_bit_sz (Z.to_nat (4 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (4 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl5__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl5__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl5__cond := (fun z => (0 <= z <= 4)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl8__helper1 : (0 <= 7)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl8__helper2 : to_bit_sz (Z.to_nat (7 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (7 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl8__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl8__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl8__cond := (fun z => (0 <= z <= 7)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl10__helper1 : (0 <= 9)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl10__helper2 : to_bit_sz (Z.to_nat (9 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (9 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl10__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl10__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl10__cond := (fun z => (0 <= z <= 9)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl16__helper1 : (0 <= 15)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl16__helper2 : to_bit_sz (Z.to_nat (15 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (15 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl16__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl16__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl16__cond := (fun z => (0 <= z <= 15)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl20__helper1 : (0 <= 19)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl20__helper2 : to_bit_sz (Z.to_nat (19 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (19 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl20__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl20__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl20__cond := (fun z => (0 <= z <= 19)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl32__helper1 : (0 <= 31)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl32__helper2 : to_bit_sz (Z.to_nat (31 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (31 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl32__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl32__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl32__cond := (fun z => (0 <= z <= 31)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl40__helper1 : (0 <= 39)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl40__helper2 : to_bit_sz (Z.to_nat (39 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (39 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl40__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl40__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl40__cond := (fun z => (0 <= z <= 39)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl64__helper1 : (0 <= 63)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl64__helper2 : to_bit_sz (Z.to_nat (63 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (63 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl64__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl64__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl64__cond := (fun z => (0 <= z <= 63)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl80__helper1 : (0 <= 79)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl80__helper2 : to_bit_sz (Z.to_nat (79 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (79 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl80__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl80__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl80__cond := (fun z => (0 <= z <= 79)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl160__helper1 : (0 <= 159)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl160__helper2 : to_bit_sz (Z.to_nat (159 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (159 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl160__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl160__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl160__cond := (fun z => (0 <= z <= 159)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl320__helper1 : (0 <= 319)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl320__helper2 : to_bit_sz (Z.to_nat (319 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (319 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl320__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl320__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl320__cond := (fun z => (0 <= z <= 319)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl640__helper1 : (0 <= 639)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl640__helper2 : to_bit_sz (Z.to_nat (639 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (639 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl640__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl640__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl640__cond := (fun z => (0 <= z <= 639)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl1280__helper1 : (0 <= 1279)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl1280__helper2 : to_bit_sz (Z.to_nat (1279 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (1279 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl1280__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl1280__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl1280__cond := (fun z => (0 <= z <= 1279)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl2560__helper1 : (0 <= 2559)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl2560__helper2 : to_bit_sz (Z.to_nat (2559 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (2559 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl2560__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl2560__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl2560__cond := (fun z => (0 <= z <= 2559)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl5120__helper1 : (0 <= 5119)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl5120__helper2 : to_bit_sz (Z.to_nat (5119 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (5119 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl5120__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl5120__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl5120__cond := (fun z => (0 <= z <= 5119)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl10240__helper1 : (0 <= 10239)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl10240__helper2 : to_bit_sz (Z.to_nat (10239 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (10239 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl10240__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl10240__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl10240__cond := (fun z => (0 <= z <= 10239)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl40960__helper1 : (0 <= 40959)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl40960__helper2 : to_bit_sz (Z.to_nat (40959 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (40959 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl40960__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl40960__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl40960__cond := (fun z => (0 <= z <= 40959)%Z).
Lemma SRS_PeriodicityAndOffset_r16__root__sl81920__helper1 : (0 <= 81919)%Z.  lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__sl81920__helper2 : to_bit_sz (Z.to_nat (81919 - 0)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (81919 - 0))%Z). { apply Zorder.Zle_minus_le_0. apply SRS_PeriodicityAndOffset_r16__root__sl81920__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition SRS_PeriodicityAndOffset_r16__root__sl81920__Type := Z.
Definition SRS_PeriodicityAndOffset_r16__root__sl81920__cond := (fun z => (0 <= z <= 81919)%Z).

Inductive SRS_PeriodicityAndOffset_r16__root__Type : Set :=
  | SRS_PeriodicityAndOffset_r16__root__sl1 : unit -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl2 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl4 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl5 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl8 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl10 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl16 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl20 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl32 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl40 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl64 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl80 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl160 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl320 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl640 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl1280 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl2560 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl5120 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl10240 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl40960 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
  | SRS_PeriodicityAndOffset_r16__root__sl81920 : Z -> SRS_PeriodicityAndOffset_r16__root__Type
.
Definition SRS_PeriodicityAndOffset_r16__root__list : list typ := (
typ_cons unit (fun _ => True) ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl2__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl4__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl5__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl8__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl10__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl16__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl20__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl32__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl40__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl64__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl80__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl160__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl320__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl640__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl1280__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl2560__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl5120__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl10240__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl40960__cond ::
typ_cons Z SRS_PeriodicityAndOffset_r16__root__sl81920__cond ::
 nil).
Definition SRS_PeriodicityAndOffset_r16__root__cond (c : SRS_PeriodicityAndOffset_r16__root__Type) := 
  match c with
  | SRS_PeriodicityAndOffset_r16__root__sl1 t => (fun _ => True) t 
  | SRS_PeriodicityAndOffset_r16__root__sl2 t => SRS_PeriodicityAndOffset_r16__root__sl2__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl4 t => SRS_PeriodicityAndOffset_r16__root__sl4__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl5 t => SRS_PeriodicityAndOffset_r16__root__sl5__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl8 t => SRS_PeriodicityAndOffset_r16__root__sl8__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl10 t => SRS_PeriodicityAndOffset_r16__root__sl10__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl16 t => SRS_PeriodicityAndOffset_r16__root__sl16__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl20 t => SRS_PeriodicityAndOffset_r16__root__sl20__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl32 t => SRS_PeriodicityAndOffset_r16__root__sl32__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl40 t => SRS_PeriodicityAndOffset_r16__root__sl40__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl64 t => SRS_PeriodicityAndOffset_r16__root__sl64__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl80 t => SRS_PeriodicityAndOffset_r16__root__sl80__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl160 t => SRS_PeriodicityAndOffset_r16__root__sl160__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl320 t => SRS_PeriodicityAndOffset_r16__root__sl320__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl640 t => SRS_PeriodicityAndOffset_r16__root__sl640__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl1280 t => SRS_PeriodicityAndOffset_r16__root__sl1280__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl2560 t => SRS_PeriodicityAndOffset_r16__root__sl2560__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl5120 t => SRS_PeriodicityAndOffset_r16__root__sl5120__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl10240 t => SRS_PeriodicityAndOffset_r16__root__sl10240__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl40960 t => SRS_PeriodicityAndOffset_r16__root__sl40960__cond t 
  | SRS_PeriodicityAndOffset_r16__root__sl81920 t => SRS_PeriodicityAndOffset_r16__root__sl81920__cond t 
  end.

Lemma SRS_PeriodicityAndOffset_r16__root__len_helper1 : to_bit_sz (length SRS_PeriodicityAndOffset_r16__root__list - 1) <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.
Lemma SRS_PeriodicityAndOffset_r16__root__len_helper2 : 2 <= length2 SRS_PeriodicityAndOffset_r16__root__list.
 simpl. lia. Qed.

Definition SRS_PeriodicityAndOffset_r16__ext__Type : Set := Empty_set.
Definition SRS_PeriodicityAndOffset_r16__ext__cond (c : SRS_PeriodicityAndOffset_r16__ext__Type) := True.
Definition SRS_PeriodicityAndOffset_r16__Type : Set := SRS_PeriodicityAndOffset_r16__root__Type + SRS_PeriodicityAndOffset_r16__ext__Type.
Definition SRS_PeriodicityAndOffset_r16__cond :=
  sum_cond SRS_PeriodicityAndOffset_r16__root__cond SRS_PeriodicityAndOffset_r16__ext__cond.

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
Definition SRS_PeriodicityAndOffset_r16__root__sl2__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl2__cond :=
 ranged_int_format (0) (1) SRS_PeriodicityAndOffset_r16__root__sl2__helper1 SRS_PeriodicityAndOffset_r16__root__sl2__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl2__cond SRS_PeriodicityAndOffset_r16__root__sl2__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl4__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl4__cond :=
 ranged_int_format (0) (3) SRS_PeriodicityAndOffset_r16__root__sl4__helper1 SRS_PeriodicityAndOffset_r16__root__sl4__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl4__cond SRS_PeriodicityAndOffset_r16__root__sl4__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl5__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl5__cond :=
 ranged_int_format (0) (4) SRS_PeriodicityAndOffset_r16__root__sl5__helper1 SRS_PeriodicityAndOffset_r16__root__sl5__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl5__cond SRS_PeriodicityAndOffset_r16__root__sl5__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl8__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl8__cond :=
 ranged_int_format (0) (7) SRS_PeriodicityAndOffset_r16__root__sl8__helper1 SRS_PeriodicityAndOffset_r16__root__sl8__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl8__cond SRS_PeriodicityAndOffset_r16__root__sl8__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl10__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl10__cond :=
 ranged_int_format (0) (9) SRS_PeriodicityAndOffset_r16__root__sl10__helper1 SRS_PeriodicityAndOffset_r16__root__sl10__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl10__cond SRS_PeriodicityAndOffset_r16__root__sl10__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl16__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl16__cond :=
 ranged_int_format (0) (15) SRS_PeriodicityAndOffset_r16__root__sl16__helper1 SRS_PeriodicityAndOffset_r16__root__sl16__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl16__cond SRS_PeriodicityAndOffset_r16__root__sl16__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl20__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl20__cond :=
 ranged_int_format (0) (19) SRS_PeriodicityAndOffset_r16__root__sl20__helper1 SRS_PeriodicityAndOffset_r16__root__sl20__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl20__cond SRS_PeriodicityAndOffset_r16__root__sl20__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl32__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl32__cond :=
 ranged_int_format (0) (31) SRS_PeriodicityAndOffset_r16__root__sl32__helper1 SRS_PeriodicityAndOffset_r16__root__sl32__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl32__cond SRS_PeriodicityAndOffset_r16__root__sl32__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl40__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl40__cond :=
 ranged_int_format (0) (39) SRS_PeriodicityAndOffset_r16__root__sl40__helper1 SRS_PeriodicityAndOffset_r16__root__sl40__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl40__cond SRS_PeriodicityAndOffset_r16__root__sl40__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl64__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl64__cond :=
 ranged_int_format (0) (63) SRS_PeriodicityAndOffset_r16__root__sl64__helper1 SRS_PeriodicityAndOffset_r16__root__sl64__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl64__cond SRS_PeriodicityAndOffset_r16__root__sl64__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl80__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl80__cond :=
 ranged_int_format (0) (79) SRS_PeriodicityAndOffset_r16__root__sl80__helper1 SRS_PeriodicityAndOffset_r16__root__sl80__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl80__cond SRS_PeriodicityAndOffset_r16__root__sl80__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl160__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl160__cond :=
 ranged_int_format (0) (159) SRS_PeriodicityAndOffset_r16__root__sl160__helper1 SRS_PeriodicityAndOffset_r16__root__sl160__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl160__cond SRS_PeriodicityAndOffset_r16__root__sl160__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl320__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl320__cond :=
 ranged_int_format (0) (319) SRS_PeriodicityAndOffset_r16__root__sl320__helper1 SRS_PeriodicityAndOffset_r16__root__sl320__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl320__cond SRS_PeriodicityAndOffset_r16__root__sl320__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl640__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl640__cond :=
 ranged_int_format (0) (639) SRS_PeriodicityAndOffset_r16__root__sl640__helper1 SRS_PeriodicityAndOffset_r16__root__sl640__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl640__cond SRS_PeriodicityAndOffset_r16__root__sl640__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl1280__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl1280__cond :=
 ranged_int_format (0) (1279) SRS_PeriodicityAndOffset_r16__root__sl1280__helper1 SRS_PeriodicityAndOffset_r16__root__sl1280__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl1280__cond SRS_PeriodicityAndOffset_r16__root__sl1280__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl2560__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl2560__cond :=
 ranged_int_format (0) (2559) SRS_PeriodicityAndOffset_r16__root__sl2560__helper1 SRS_PeriodicityAndOffset_r16__root__sl2560__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl2560__cond SRS_PeriodicityAndOffset_r16__root__sl2560__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl5120__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl5120__cond :=
 ranged_int_format (0) (5119) SRS_PeriodicityAndOffset_r16__root__sl5120__helper1 SRS_PeriodicityAndOffset_r16__root__sl5120__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl5120__cond SRS_PeriodicityAndOffset_r16__root__sl5120__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl10240__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl10240__cond :=
 ranged_int_format (0) (10239) SRS_PeriodicityAndOffset_r16__root__sl10240__helper1 SRS_PeriodicityAndOffset_r16__root__sl10240__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl10240__cond SRS_PeriodicityAndOffset_r16__root__sl10240__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl40960__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl40960__cond :=
 ranged_int_format (0) (40959) SRS_PeriodicityAndOffset_r16__root__sl40960__helper1 SRS_PeriodicityAndOffset_r16__root__sl40960__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl40960__cond SRS_PeriodicityAndOffset_r16__root__sl40960__Format.

Definition SRS_PeriodicityAndOffset_r16__root__sl81920__Format : T_Format Z SRS_PeriodicityAndOffset_r16__root__sl81920__cond :=
 ranged_int_format (0) (81919) SRS_PeriodicityAndOffset_r16__root__sl81920__helper1 SRS_PeriodicityAndOffset_r16__root__sl81920__helper2.

Opaque SRS_PeriodicityAndOffset_r16__root__sl81920__cond SRS_PeriodicityAndOffset_r16__root__sl81920__Format.


Definition SRS_PeriodicityAndOffset_r16__root__Format_Type := Eval cbn in get_formats SRS_PeriodicityAndOffset_r16__root__list.
Definition SRS_PeriodicityAndOffset_r16__root__Format_list : SRS_PeriodicityAndOffset_r16__root__Format_Type :=
  (unit__Format, (SRS_PeriodicityAndOffset_r16__root__sl2__Format, (SRS_PeriodicityAndOffset_r16__root__sl4__Format, (SRS_PeriodicityAndOffset_r16__root__sl5__Format, (SRS_PeriodicityAndOffset_r16__root__sl8__Format, (SRS_PeriodicityAndOffset_r16__root__sl10__Format, (SRS_PeriodicityAndOffset_r16__root__sl16__Format, (SRS_PeriodicityAndOffset_r16__root__sl20__Format, (SRS_PeriodicityAndOffset_r16__root__sl32__Format, (SRS_PeriodicityAndOffset_r16__root__sl40__Format, (SRS_PeriodicityAndOffset_r16__root__sl64__Format, (SRS_PeriodicityAndOffset_r16__root__sl80__Format, (SRS_PeriodicityAndOffset_r16__root__sl160__Format, (SRS_PeriodicityAndOffset_r16__root__sl320__Format, (SRS_PeriodicityAndOffset_r16__root__sl640__Format, (SRS_PeriodicityAndOffset_r16__root__sl1280__Format, (SRS_PeriodicityAndOffset_r16__root__sl2560__Format, (SRS_PeriodicityAndOffset_r16__root__sl5120__Format, (SRS_PeriodicityAndOffset_r16__root__sl10240__Format, (SRS_PeriodicityAndOffset_r16__root__sl40960__Format, (SRS_PeriodicityAndOffset_r16__root__sl81920__Format, unit__Format))))))))))))))))))))).
Definition SRS_PeriodicityAndOffset_r16__root__list__Format := Eval compute in choice_format SRS_PeriodicityAndOffset_r16__root__list SRS_PeriodicityAndOffset_r16__root__len_helper1 SRS_PeriodicityAndOffset_r16__root__len_helper2  SRS_PeriodicityAndOffset_r16__root__Format_list.
Definition SRS_PeriodicityAndOffset_r16__root__F1 (z : SRS_PeriodicityAndOffset_r16__root__Type) : (choice SRS_PeriodicityAndOffset_r16__root__list) :=
  match z with
   | SRS_PeriodicityAndOffset_r16__root__sl1 t => existT _ 0 t
  | SRS_PeriodicityAndOffset_r16__root__sl2 t => existT _ 1 t
  | SRS_PeriodicityAndOffset_r16__root__sl4 t => existT _ 2 t
  | SRS_PeriodicityAndOffset_r16__root__sl5 t => existT _ 3 t
  | SRS_PeriodicityAndOffset_r16__root__sl8 t => existT _ 4 t
  | SRS_PeriodicityAndOffset_r16__root__sl10 t => existT _ 5 t
  | SRS_PeriodicityAndOffset_r16__root__sl16 t => existT _ 6 t
  | SRS_PeriodicityAndOffset_r16__root__sl20 t => existT _ 7 t
  | SRS_PeriodicityAndOffset_r16__root__sl32 t => existT _ 8 t
  | SRS_PeriodicityAndOffset_r16__root__sl40 t => existT _ 9 t
  | SRS_PeriodicityAndOffset_r16__root__sl64 t => existT _ 10 t
  | SRS_PeriodicityAndOffset_r16__root__sl80 t => existT _ 11 t
  | SRS_PeriodicityAndOffset_r16__root__sl160 t => existT _ 12 t
  | SRS_PeriodicityAndOffset_r16__root__sl320 t => existT _ 13 t
  | SRS_PeriodicityAndOffset_r16__root__sl640 t => existT _ 14 t
  | SRS_PeriodicityAndOffset_r16__root__sl1280 t => existT _ 15 t
  | SRS_PeriodicityAndOffset_r16__root__sl2560 t => existT _ 16 t
  | SRS_PeriodicityAndOffset_r16__root__sl5120 t => existT _ 17 t
  | SRS_PeriodicityAndOffset_r16__root__sl10240 t => existT _ 18 t
  | SRS_PeriodicityAndOffset_r16__root__sl40960 t => existT _ 19 t
  | SRS_PeriodicityAndOffset_r16__root__sl81920 t => existT _ 20 t
  end.
Definition SRS_PeriodicityAndOffset_r16__root__g := (fun n => typ_set (get_nth_typ SRS_PeriodicityAndOffset_r16__root__list n)).
Definition SRS_PeriodicityAndOffset_r16__root__F2 (y : choice SRS_PeriodicityAndOffset_r16__root__list) : SRS_PeriodicityAndOffset_r16__root__Type :=
  let (x0, t0) := y in
    (match x0 as n return  (SRS_PeriodicityAndOffset_r16__root__g n -> SRS_PeriodicityAndOffset_r16__root__Type) with
    | 0 => fun (t : unit) => SRS_PeriodicityAndOffset_r16__root__sl1 t 
    | 1 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl2 t 
    | 2 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl4 t 
    | 3 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl5 t 
    | 4 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl8 t 
    | 5 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl10 t 
    | 6 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl16 t 
    | 7 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl20 t 
    | 8 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl32 t 
    | 9 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl40 t 
    | 10 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl64 t 
    | 11 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl80 t 
    | 12 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl160 t 
    | 13 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl320 t 
    | 14 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl640 t 
    | 15 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl1280 t 
    | 16 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl2560 t 
    | 17 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl5120 t 
    | 18 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl10240 t 
    | 19 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl40960 t 
    | 20 => fun (t : Z) => SRS_PeriodicityAndOffset_r16__root__sl81920 t 
 | (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n0))))))))))))))))))))) => (fun (x' : nat) (t'' : SRS_PeriodicityAndOffset_r16__root__g (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))))))) =>let t' :=
           eq_rect (get_nth_typ SRS_PeriodicityAndOffset_r16__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x'))))))))))))))))))))))
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len SRS_PeriodicityAndOffset_r16__root__list (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S x')))))))))))))))))))))
           (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_n_S _ _ (le_0_n x'))))))))))))))))))))))) in match t' return SRS_PeriodicityAndOffset_r16__root__Type with end) n0
           end t0).

Lemma SRS_PeriodicityAndOffset_r16__root__helper2 :  forall (y : SRS_PeriodicityAndOffset_r16__root__Type), SRS_PeriodicityAndOffset_r16__root__cond y -> choice_cond SRS_PeriodicityAndOffset_r16__root__list (SRS_PeriodicityAndOffset_r16__root__F1 y).
  choice_helper_tact_dec y. Qed.

Lemma SRS_PeriodicityAndOffset_r16__root__helper3 :  forall (y : SRS_PeriodicityAndOffset_r16__root__Type), SRS_PeriodicityAndOffset_r16__root__F2 (SRS_PeriodicityAndOffset_r16__root__F1 y) = y.
  choice_helper_tact_dec y. Qed.

Transparent length.
Lemma SRS_PeriodicityAndOffset_r16__root__helper4 : (forall b : choice SRS_PeriodicityAndOffset_r16__root__list, choice_cond SRS_PeriodicityAndOffset_r16__root__list b -> SRS_PeriodicityAndOffset_r16__root__cond (SRS_PeriodicityAndOffset_r16__root__F2 b) /\ SRS_PeriodicityAndOffset_r16__root__F1 (SRS_PeriodicityAndOffset_r16__root__F2 b) = b).
Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.
Opaque length SRS_PeriodicityAndOffset_r16__root__F1 SRS_PeriodicityAndOffset_r16__root__F2.
Definition SRS_PeriodicityAndOffset_r16__root__Format : T_Format SRS_PeriodicityAndOffset_r16__root__Type SRS_PeriodicityAndOffset_r16__root__cond :=
  (* Eval compute in *) proj2_format SRS_PeriodicityAndOffset_r16__root__cond SRS_PeriodicityAndOffset_r16__root__list__Format SRS_PeriodicityAndOffset_r16__root__F1 SRS_PeriodicityAndOffset_r16__root__F2 SRS_PeriodicityAndOffset_r16__root__helper2 SRS_PeriodicityAndOffset_r16__root__helper3 SRS_PeriodicityAndOffset_r16__root__helper4.
Opaque SRS_PeriodicityAndOffset_r16__root__cond SRS_PeriodicityAndOffset_r16__root__Format.

Definition SRS_PeriodicityAndOffset_r16__ext__Format : T_Format SRS_PeriodicityAndOffset_r16__ext__Type SRS_PeriodicityAndOffset_r16__ext__cond := empty_format.
Opaque SRS_PeriodicityAndOffset_r16__ext__cond SRS_PeriodicityAndOffset_r16__ext__Format.

Definition SRS_PeriodicityAndOffset_r16__Format : T_Format SRS_PeriodicityAndOffset_r16__Type SRS_PeriodicityAndOffset_r16__cond := sum_format SRS_PeriodicityAndOffset_r16__root__Format SRS_PeriodicityAndOffset_r16__ext__Format.
Opaque SRS_PeriodicityAndOffset_r16__cond SRS_PeriodicityAndOffset_r16__Format.

