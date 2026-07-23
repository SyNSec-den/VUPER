Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat.

(* Some form of combinator would result in parse-to-same-ver *)
Definition parse_to_SameVer {A : Set} {P : A -> Prop} (par : Parse A P) :=
   forall bf pos pos' x pf_x f, 
     par bf pos =
    Some (exist _ x pf_x, pos', f) -> f = SameVer.

Definition basic_bit_SameVer n:
  parse_to_SameVer (ByteBuffer.read_n_nat n).
Proof.
  unfold parse_to_SameVer.  intros.  simpl in H.
  eapply ByteBufferProp.BPP.read_n_nat_SameVer.
  apply H.
Qed. 

Require Import ASN1Parser.tact.

Lemma proj_SameVer
   {A B : Set} {P2 : B -> Prop} {P1 : A -> Prop}
   (b_par :  Parse B P2) (f : B -> A)
   (imp : forall a : B, P2 a -> P1 (f a)) :
  parse_to_SameVer b_par -> 
  parse_to_SameVer (proj_parse b_par f imp).
Proof.
  intros.  unfold parse_to_SameVer, proj_parse in *.
  intros. destruct_enc. inversion H0.  subst. apply H in E.
  auto.
Qed.

Lemma restrict_SameVer
  {A : Set} {P R : A -> Prop}
  (par : Parse A P)  (r_dec : dec_P R) : 
  parse_to_SameVer par -> 
  parse_to_SameVer (restrict_parse r_dec par).
Proof.
  intros. unfold parse_to_SameVer, restrict_parse in *. intros.
  destruct_enc.  destruct_match_dec_new.  inversion H0.
  subst.  eapply H. eauto.
Qed.

Lemma sigma_SameVer
  {A B : Set} {P1 : A -> Prop} (par1 : Parse A P1)
  (P2 : A -> B -> Prop)
  (pser2 : forall a : A, P1 a -> Parse B (P2 a)) :
  parse_to_SameVer par1 ->
  (forall a pf_a, parse_to_SameVer (pser2 a pf_a)) -> 
  parse_to_SameVer (sigma_parse par1 P2 pser2).
Proof.
  intros.  unfold parse_to_SameVer.  intros.
  unfold sigma_parse, bind_parse, return_parse in H1.
  repeat destruct_enc.  inversion H1. subst.

  assert (f0 = SameVer).
  { eapply H.  apply E. }
  assert (f1 = SameVer).
  { eapply H0. apply E0. }
  subst. simpl. auto.
Qed.  

Require Import ASN1Parser.Formats.Comb.ListFormatProp.

Lemma list_SameVer n
  {A : Set} {P R : A -> Prop}
  (fmt : T_Format A P)  : 
  parse_to_SameVer (T_Parse _ _ fmt) -> 
  parse_to_SameVer (T_Parse _ _ (list_format fmt n)).
Proof.
  intros. 
  induction n.
  - unfold parse_to_SameVer in *.
    simpl. intros. unfold ListFormat.read_fixed_item in H0.
    destruct_enc. inversion H0.  auto.
  - simpl. unfold bind_parse, return_parse, parse_to_SameVer.
    intros.
    repeat destruct_enc. inversion H0. subst.
    clear H0. 
    assert (f0 = SameVer).
    { eapply H. apply E. }
    assert (f1 = SameVer).
    { eapply IHn. simpl. apply E0. }
    subst. simpl. auto.
Qed.

(*Require Import ASN1Parser.Array.BitRep.

(* Now we consider the valid_enc_if property *)
Definition valid_enc_if {A : Set} {P : A -> Prop} (ser : Serialize A P) :=
  forall pos, 
  exists min_len,
  forall bf a pf_a,
    min_len <= BA.len bf ->
    (exists bf' pos',  ser bf pos a = Some (bf', pos', pf_a)).

Lemma put_n_nat_valid n (pf_n : n <= 48):
  valid_enc_if (ByteBuffer.put_n_nat n).
Proof.
  unfold valid_enc_if. intros.
  exists (BA.to_nat pos + n + 7). intros.
  unfold ByteBuffer.put_n_nat.
  rewrite <- PeanoNat.Nat.leb_le in pf_n.
  rewrite pf_n. 
  eassert (G := ByteBufferProp.BPP.put_n_bits_valid_if
                  n _ _ _ pf_a H ).
  destruct_ex. split_and. 
  exists x. exists x0.  auto. 
Qed. *)
