Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

Require Import NR.NR_RRC_Definitions.
Lemma DummyA__maxNumberNZP_CSI_RS_PerCC__helper1 : (1 <= 32)%Z.  lia. Qed.
Lemma DummyA__maxNumberNZP_CSI_RS_PerCC__helper2 : to_bit_sz (Z.to_nat (32 - 1)) <= INT_MAX_LEN.
unfold to_bit_sz, INT_MAX_LEN. 
        assert (H : (0 <= (32 - 1))%Z). { apply Zorder.Zle_minus_le_0. apply DummyA__maxNumberNZP_CSI_RS_PerCC__helper1. }
        assert (G := log2_same _ H). rewrite <- G.
        simpl. lia. Qed.
Definition DummyA__maxNumberNZP_CSI_RS_PerCC__Type := Z.
Definition DummyA__maxNumberNZP_CSI_RS_PerCC__cond := (fun z => (1 <= z <= 32)%Z).
Inductive DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Type : Set :=
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p2
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p4
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p8
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p12
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p16
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p24
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p32
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p40
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p48
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p56
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p64
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p72
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p80
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p88
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p96
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p104
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p112
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p120
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p128
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p136
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p144
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p152
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p160
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p168
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p176
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p184
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p192
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p200
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p208
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p216
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p224
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p232
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p240
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p248
 | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p256
.
Definition DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__cond := (fun (_ : DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Type) => True).
Lemma DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__nat__helper : to_bit_sz 34 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__nat__Format : T_Format nat (fun z => (z <= 34)) :=
  nat_enum_format 34 DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__nat__helper.

Definition DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F1 t :=
  match t with
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p2 => 0
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p4 => 1
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p8 => 2
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p12 => 3
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p16 => 4
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p24 => 5
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p32 => 6
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p40 => 7
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p48 => 8
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p56 => 9
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p64 => 10
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p72 => 11
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p80 => 12
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p88 => 13
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p96 => 14
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p104 => 15
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p112 => 16
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p120 => 17
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p128 => 18
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p136 => 19
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p144 => 20
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p152 => 21
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p160 => 22
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p168 => 23
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p176 => 24
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p184 => 25
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p192 => 26
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p200 => 27
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p208 => 28
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p216 => 29
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p224 => 30
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p232 => 31
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p240 => 32
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p248 => 33
  | DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p256 => 34
  end.
Definition DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F2 n :=
  match n with
  | 0 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p2
  | 1 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p4
  | 2 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p8
  | 3 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p12
  | 4 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p16
  | 5 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p24
  | 6 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p32
  | 7 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p40
  | 8 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p48
  | 9 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p56
  | 10 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p64
  | 11 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p72
  | 12 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p80
  | 13 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p88
  | 14 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p96
  | 15 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p104
  | 16 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p112
  | 17 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p120
  | 18 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p128
  | 19 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p136
  | 20 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p144
  | 21 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p152
  | 22 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p160
  | 23 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p168
  | 24 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p176
  | 25 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p184
  | 26 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p192
  | 27 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p200
  | 28 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p208
  | 29 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p216
  | 30 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p224
  | 31 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p232
  | 32 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p240
  | 33 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p248
  | 34 => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p256
  | _ => DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__p2
  end.
Lemma DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F1F2 : forall x : DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Type, (DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F1 x <= 34) /\ DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F2 (DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F1 x) = x. imp_solve. Qed.
Lemma DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F2F1 : forall (y : nat) (H : y <= 34), DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F1 (DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F2 y) = y. enum_solve H y. Qed.

Inductive DummyA__maxNumberCS_IM_PerCC__Type : Set :=
 | DummyA__maxNumberCS_IM_PerCC__n1
 | DummyA__maxNumberCS_IM_PerCC__n2
 | DummyA__maxNumberCS_IM_PerCC__n4
 | DummyA__maxNumberCS_IM_PerCC__n8
 | DummyA__maxNumberCS_IM_PerCC__n16
 | DummyA__maxNumberCS_IM_PerCC__n32
.
Definition DummyA__maxNumberCS_IM_PerCC__cond := (fun (_ : DummyA__maxNumberCS_IM_PerCC__Type) => True).
Lemma DummyA__maxNumberCS_IM_PerCC__nat__helper : to_bit_sz 5 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyA__maxNumberCS_IM_PerCC__nat__Format : T_Format nat (fun z => (z <= 5)) :=
  nat_enum_format 5 DummyA__maxNumberCS_IM_PerCC__nat__helper.

Definition DummyA__maxNumberCS_IM_PerCC__F1 t :=
  match t with
  | DummyA__maxNumberCS_IM_PerCC__n1 => 0
  | DummyA__maxNumberCS_IM_PerCC__n2 => 1
  | DummyA__maxNumberCS_IM_PerCC__n4 => 2
  | DummyA__maxNumberCS_IM_PerCC__n8 => 3
  | DummyA__maxNumberCS_IM_PerCC__n16 => 4
  | DummyA__maxNumberCS_IM_PerCC__n32 => 5
  end.
Definition DummyA__maxNumberCS_IM_PerCC__F2 n :=
  match n with
  | 0 => DummyA__maxNumberCS_IM_PerCC__n1
  | 1 => DummyA__maxNumberCS_IM_PerCC__n2
  | 2 => DummyA__maxNumberCS_IM_PerCC__n4
  | 3 => DummyA__maxNumberCS_IM_PerCC__n8
  | 4 => DummyA__maxNumberCS_IM_PerCC__n16
  | 5 => DummyA__maxNumberCS_IM_PerCC__n32
  | _ => DummyA__maxNumberCS_IM_PerCC__n1
  end.
Lemma DummyA__maxNumberCS_IM_PerCC__F1F2 : forall x : DummyA__maxNumberCS_IM_PerCC__Type, (DummyA__maxNumberCS_IM_PerCC__F1 x <= 5) /\ DummyA__maxNumberCS_IM_PerCC__F2 (DummyA__maxNumberCS_IM_PerCC__F1 x) = x. imp_solve. Qed.
Lemma DummyA__maxNumberCS_IM_PerCC__F2F1 : forall (y : nat) (H : y <= 5), DummyA__maxNumberCS_IM_PerCC__F1 (DummyA__maxNumberCS_IM_PerCC__F2 y) = y. enum_solve H y. Qed.

Inductive DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Type : Set :=
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n5
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n6
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n7
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n8
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n9
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n10
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n12
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n14
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n16
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n18
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n20
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n22
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n24
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n26
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n28
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n30
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n32
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n34
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n36
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n38
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n40
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n42
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n44
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n46
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n48
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n50
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n52
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n54
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n56
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n58
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n60
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n62
 | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n64
.
Definition DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__cond := (fun (_ : DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Type) => True).
Lemma DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__nat__helper : to_bit_sz 32 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__nat__Format : T_Format nat (fun z => (z <= 32)) :=
  nat_enum_format 32 DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__nat__helper.

Definition DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F1 t :=
  match t with
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n5 => 0
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n6 => 1
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n7 => 2
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n8 => 3
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n9 => 4
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n10 => 5
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n12 => 6
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n14 => 7
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n16 => 8
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n18 => 9
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n20 => 10
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n22 => 11
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n24 => 12
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n26 => 13
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n28 => 14
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n30 => 15
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n32 => 16
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n34 => 17
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n36 => 18
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n38 => 19
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n40 => 20
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n42 => 21
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n44 => 22
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n46 => 23
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n48 => 24
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n50 => 25
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n52 => 26
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n54 => 27
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n56 => 28
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n58 => 29
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n60 => 30
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n62 => 31
  | DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n64 => 32
  end.
Definition DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F2 n :=
  match n with
  | 0 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n5
  | 1 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n6
  | 2 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n7
  | 3 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n8
  | 4 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n9
  | 5 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n10
  | 6 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n12
  | 7 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n14
  | 8 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n16
  | 9 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n18
  | 10 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n20
  | 11 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n22
  | 12 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n24
  | 13 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n26
  | 14 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n28
  | 15 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n30
  | 16 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n32
  | 17 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n34
  | 18 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n36
  | 19 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n38
  | 20 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n40
  | 21 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n42
  | 22 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n44
  | 23 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n46
  | 24 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n48
  | 25 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n50
  | 26 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n52
  | 27 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n54
  | 28 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n56
  | 29 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n58
  | 30 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n60
  | 31 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n62
  | 32 => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n64
  | _ => DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__n5
  end.
Lemma DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F1F2 : forall x : DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Type, (DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F1 x <= 32) /\ DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F2 (DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F1 x) = x. imp_solve. Qed.
Lemma DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F2F1 : forall (y : nat) (H : y <= 32), DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F1 (DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F2 y) = y. enum_solve H y. Qed.

Inductive DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Type : Set :=
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p8
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p12
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p16
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p24
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p32
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p40
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p48
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p56
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p64
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p72
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p80
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p88
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p96
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p104
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p112
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p120
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p128
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p136
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p144
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p152
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p160
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p168
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p176
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p184
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p192
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p200
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p208
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p216
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p224
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p232
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p240
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p248
 | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p256
.
Definition DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__cond := (fun (_ : DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Type) => True).
Lemma DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__nat__helper : to_bit_sz 32 <= INT_MAX_LEN.
  unfold to_bit_sz, INT_MAX_LEN. simpl. lia.
Qed.
Definition DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__nat__Format : T_Format nat (fun z => (z <= 32)) :=
  nat_enum_format 32 DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__nat__helper.

Definition DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F1 t :=
  match t with
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p8 => 0
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p12 => 1
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p16 => 2
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p24 => 3
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p32 => 4
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p40 => 5
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p48 => 6
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p56 => 7
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p64 => 8
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p72 => 9
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p80 => 10
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p88 => 11
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p96 => 12
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p104 => 13
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p112 => 14
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p120 => 15
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p128 => 16
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p136 => 17
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p144 => 18
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p152 => 19
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p160 => 20
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p168 => 21
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p176 => 22
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p184 => 23
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p192 => 24
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p200 => 25
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p208 => 26
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p216 => 27
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p224 => 28
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p232 => 29
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p240 => 30
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p248 => 31
  | DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p256 => 32
  end.
Definition DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F2 n :=
  match n with
  | 0 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p8
  | 1 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p12
  | 2 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p16
  | 3 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p24
  | 4 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p32
  | 5 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p40
  | 6 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p48
  | 7 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p56
  | 8 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p64
  | 9 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p72
  | 10 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p80
  | 11 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p88
  | 12 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p96
  | 13 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p104
  | 14 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p112
  | 15 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p120
  | 16 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p128
  | 17 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p136
  | 18 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p144
  | 19 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p152
  | 20 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p160
  | 21 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p168
  | 22 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p176
  | 23 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p184
  | 24 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p192
  | 25 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p200
  | 26 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p208
  | 27 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p216
  | 28 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p224
  | 29 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p232
  | 30 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p240
  | 31 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p248
  | 32 => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p256
  | _ => DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__p8
  end.
Lemma DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F1F2 : forall x : DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Type, (DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F1 x <= 32) /\ DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F2 (DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F1 x) = x. imp_solve. Qed.
Lemma DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F2F1 : forall (y : nat) (H : y <= 32), DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F1 (DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F2 y) = y. enum_solve H y. Qed.

Record DummyA__Type : Set :=
  make__DummyA__Type {
    DummyA__maxNumberNZP_CSI_RS_PerCC : Z ;
    DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC : DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Type ;
    DummyA__maxNumberCS_IM_PerCC : DummyA__maxNumberCS_IM_PerCC__Type ;
    DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC : DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Type ;
    DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC : DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Type ;
}.
Definition DummyA__list := (
 Nor Z DummyA__maxNumberNZP_CSI_RS_PerCC__cond ::
 Nor DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Type DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__cond ::
 Nor DummyA__maxNumberCS_IM_PerCC__Type DummyA__maxNumberCS_IM_PerCC__cond ::
 Nor DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Type DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__cond ::
 Nor DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Type DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__cond ::
 nil).
Definition DummyA__cond z := 
  DummyA__maxNumberNZP_CSI_RS_PerCC__cond (DummyA__maxNumberNZP_CSI_RS_PerCC z) /\
  DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__cond (DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC z) /\
  DummyA__maxNumberCS_IM_PerCC__cond (DummyA__maxNumberCS_IM_PerCC z) /\
  DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__cond (DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC z) /\
  DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__cond (DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC z) /\
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
Definition DummyA__maxNumberNZP_CSI_RS_PerCC__Format : T_Format Z DummyA__maxNumberNZP_CSI_RS_PerCC__cond :=
 ranged_int_format (1) (32) DummyA__maxNumberNZP_CSI_RS_PerCC__helper1 DummyA__maxNumberNZP_CSI_RS_PerCC__helper2.

Opaque DummyA__maxNumberNZP_CSI_RS_PerCC__cond DummyA__maxNumberNZP_CSI_RS_PerCC__Format.

Definition DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Format : T_Format DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__nat__Format DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F1 DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F2 DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F1F2 DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__F2F1.

Opaque DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__cond DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Format.

Definition DummyA__maxNumberCS_IM_PerCC__Format : T_Format DummyA__maxNumberCS_IM_PerCC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyA__maxNumberCS_IM_PerCC__nat__Format DummyA__maxNumberCS_IM_PerCC__F1 DummyA__maxNumberCS_IM_PerCC__F2 DummyA__maxNumberCS_IM_PerCC__F1F2 DummyA__maxNumberCS_IM_PerCC__F2F1.

Opaque DummyA__maxNumberCS_IM_PerCC__cond DummyA__maxNumberCS_IM_PerCC__Format.

Definition DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Format : T_Format DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__nat__Format DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F1 DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F2 DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F1F2 DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__F2F1.

Opaque DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__cond DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Format.

Definition DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Format : T_Format DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Type (fun _ => True) :=
(* Eval compute in *) proj3_format DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__nat__Format DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F1 DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F2 DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F1F2 DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__F2F1.

Opaque DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__cond DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Format.


Definition DummyA__Format_Type := Eval cbn in seq_format_prod DummyA__list.
Definition DummyA__Format_list : DummyA__Format_Type :=
  (DummyA__maxNumberNZP_CSI_RS_PerCC__Format, (DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC__Format, (DummyA__maxNumberCS_IM_PerCC__Format, (DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC__Format, (DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC__Format, unit_format))))).
Definition DummyA__list__Format := (*Eval compute in *) seq_format DummyA__list DummyA__Format_list.
Definition DummyA__F1 z :=
  (DummyA__maxNumberNZP_CSI_RS_PerCC z, (DummyA__maxNumberPortsAcrossNZP_CSI_RS_PerCC z, (DummyA__maxNumberCS_IM_PerCC z, (DummyA__maxNumberSimultaneousCSI_RS_ActBWP_AllCC z, (DummyA__totalNumberPortsSimultaneousCSI_RS_ActBWP_AllCC z, tt))))).
Definition DummyA__F2 (y : seq_type DummyA__list) :=
  match y with
  | (i0, (i1, (i2, (i3, (i4, _)))))=>
    make__DummyA__Type i0 i1 i2 i3 i4
  end.
Lemma DummyA__F1F2_cond (z : DummyA__Type)
  : DummyA__cond z ->
  (seq_cond DummyA__list (DummyA__F1 z)).
intro H. unfold DummyA__cond in H. simpl. auto. Qed.
Lemma DummyA__F1F2_cond2 (z : DummyA__Type)
 : DummyA__F2 (DummyA__F1 z) = z.
destruct z. simpl. auto. Qed.
Lemma DummyA__F2F1_cond (y : seq_type DummyA__list)
  : seq_cond DummyA__list y ->
 (DummyA__cond (DummyA__F2 y)) /\  DummyA__F1 (DummyA__F2 y) = y.
  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.
 - unfold DummyA__cond. simpl in *. auto.
 - simpl. unfold DummyA__F1. simpl. destruct_all_unit. auto.   Qed.
Definition DummyA__Format : T_Format DummyA__Type DummyA__cond :=
        proj2_format  DummyA__cond DummyA__list__Format
    DummyA__F1 DummyA__F2 DummyA__F1F2_cond  DummyA__F1F2_cond2 DummyA__F2F1_cond.
Opaque DummyA__cond DummyA__Format.

