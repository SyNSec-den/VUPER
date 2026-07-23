
Require Export Lia.

Require Export BinInt List.

Require Export
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Array.ByteBuffer
  ASN1Parser.Array.BitRep
  
  ASN1Parser.Formats.Term.Boolean
  ASN1Parser.Formats.Term.NonNeg
  ASN1Parser.Formats.Term.Integer
  ASN1Parser.Formats.Term.Unit
  ASN1Parser.Formats.Term.OctetString
  ASN1Parser.Formats.Term.BoolList
  ASN1Parser.Formats.Term.BitString
  ASN1Parser.Formats.Term.LengthDet
  ASN1Parser.Formats.Term.RestrictString

  ASN1Parser.Formats.Comb.HelperComb
  ASN1Parser.Formats.Comb.Choice
  ASN1Parser.Formats.Comb.ChoiceProp
  ASN1Parser.Formats.Comb.ChoiceExt
  ASN1Parser.Formats.Comb.SeqOf
  ASN1Parser.Formats.Comb.Seq
  ASN1Parser.Formats.Comb.SeqExt
  ASN1Parser.Formats.Comb.SeqProd
  ASN1Parser.Formats.Comb.OpenType

  ASN1Parser.Formats.Comb.ListFormat
  ASN1Parser.Formats.Comb.ListFormatProp
  ASN1Parser.Formats.Comb.ChoiceFormat
  ASN1Parser.Formats.Comb.SeqFormat
  ASN1Parser.Formats.Comb.SeqExtFormat
  (*
 ASN1Parser.Formats.Comb.OpenType
ASN1Parser.Formats.Comb.SequenceExt
    ASN1Parser.Formats.Comb.ChoiceExt  *)
.

Require Export ASN1Parser.tact.

Ltac solve_le_Z :=
  match goal with
  | [ |- (?x <= ?y)%Z ] =>
      lazymatch x with
      | _ => unfold x || idtac
      end;
      lazymatch y with
      | _ => unfold y || idtac
      end;
      lia
  end.


Ltac destruct_prod :=
  match goal with
  | [ y : (_ * _) |- _ ] => 
      let y' := fresh "y" in
      let i := fresh "i" in
      destruct y as [i y']
  end.


Ltac imp_solve :=
  let x := fresh "x" in 
  intro x; destruct x; simpl; split; auto; try lia. 


Ltac enum_solve P n :=
    first    
    [ lia |
      (let n' := fresh "n" in
       destruct n as [|n'];
       auto; enum_solve P n' ) ].


Definition proj3_format {A A' : Set} {P2 : A' -> Prop}
  (s :  T_Format A' P2)
  (f : A -> A')
  (f_inv : A' -> A)
  (imp : forall a : A, P2 (f a) /\ f_inv (f a) = a)
  (imp_inv : forall a' : A', P2 a' -> f (f_inv a') = a')
  := proj_format (fun _ => True) s f f_inv
       (fun x _ => (imp x))
       (fun y py => conj I (imp_inv y py))
       (fun z => left I).

Ltac eq_unit_helper_tact :=
  let a := fresh "a" in
  let H := fresh "H" in
  intros a H; destruct a; split; auto.


Lemma unit_unique :  (forall a' : unit, (fun _ => True) a' -> True /\ tt = a').
  eq_unit_helper_tact. Defined.


Lemma get_nth_typ_ge_len l n :
  (length l <= n) -> 
  get_nth_typ l n  = empty_typ.
  generalize dependent n. 
  induction l.
  - intros. unfold get_nth_typ.  simpl.
    destruct n; auto.
  - simpl.
    intros.
    simpl.
    destruct n.
    + lia.
    + apply IHl. lia.
Qed.

Ltac choice_helper_tact_dec y :=
   destruct y; intros; compute; auto.

Ltac choice_helper_tact0 H0 x t :=
  first
  [ simpl in *;
     (exfalso; clear H0; rewrite get_nth_typ_ge_len in t; simpl; try lia; destruct t)
  | let x' := fresh "x" in
    destruct x as [| x'] ; try (simpl in *; auto);
     choice_helper_tact0 H0 x' t ].

(*
Lemma get_nth_typ_ce_ge_len l n :
  (length l <= n) -> 
  get_nth_typ_ce l n  = os_typ.
  generalize dependent n. 
  induction l.
  - intros. unfold get_nth_typ_ce.  simpl.
    destruct n; auto.
  - simpl.
    intros.
    unfold get_nth_typ_ce.  simpl.
    destruct n.
    + lia.
    + apply IHl. lia.
Qed. *)

Ltac choice_helper_tact H0 x :=
  first
    [ simpl in *; discriminate |
      let x' := fresh "x" in
      let E := fresh "E" in 
      destruct x as [| x' ] eqn:E;
      try (simpl in *; inversion H0; split; auto);
      choice_helper_tact H0 x'
    ].

Ltac choice_helper_tact2 b H :=
  intros; unfold choice_cond in H; destruct b; simpl in *; auto.

(*
Ltac choice_ext_helper_tact2 a :=
  destruct a; simpl; auto;
  unfold choice_cond_ext; simpl;
  rewrite (get_nth_typ_ce_ge_len); auto.
 *)

Definition unit__Format := unit_format. 
Definition bool__Format := bool_format.
Definition int__Format := int_format.
Definition octet_string_nc__Format := octet_string_no_cons_format. 
Definition bit_string_nc__Format := bit_string_no_cons_format. 

Ltac solve_le :=
  try (match goal with
       | [ |- (Z.to_nat ?x) <= _ ] =>
           unfold x
       end);
  try (match goal with
       | [ |- _ <= (Z.to_nat ?y) ] =>
           unfold y
       end);
  lia.

Ltac destruct_all_unit :=
  repeat match goal with
         | [ H : unit |- _ ] => destruct H
    end.


Ltac prove_n_le_S := repeat apply le_n_S; apply le_0_n. 

Require Import Logic.ProofIrrelevance.
Ltac choice_ext_helper_tact3 fnS pf x :=
  first
    [ let H := fresh "H" in
      assert (H : pf = fnS x); (try apply proof_irrelevance);
      f_equal; auto; 
      rewrite H, rew_opp_r; auto 
                                 
    | let x' := fresh "x" in
      destruct x as [| x' ];
      try lia;
      choice_ext_helper_tact3 fnS pf x'
    ].

(*
Ltac choice_ext_helper_tact4 x t :=
  first
    [ simpl in *; rewrite rew_opp_l; split; auto;
      generalize dependent t; rewrite get_nth_typ_ce_ge_len; simpl; auto
                                                                      
    | let x' := fresh "x" in
      destruct x as [| x' ];
      auto;
      choice_ext_helper_tact4 x' t
    ].
*)
Ltac enum_ext_solve1 n :=
    first    
    [ simpl; f_equal; apply proof_irrelevance |
      (let n' := fresh "n" in
       destruct n as [|n'];
       try lia; enum_ext_solve1 n' ) ].

Ltac enum_ext_solve2 b :=
 repeat (destruct b; simpl; auto).

(* I need to add one more format combinator here, sum format
   A + B, 
   first encode a bit, if bit is false, then, encode A,
   else encode B.
 *)

Definition sum_cond  {A B : Set} (P1 : A -> Prop) (P2 : B -> Prop) :=
  (fun z => match z with
            | inl a => P1 a
            | inr b => P2 b
            end).

Lemma x  {A B : Set} (P1 : A -> Prop) (P2 : B -> Prop)
  : forall a, P1 a -> sum_cond P1 P2 (inl a).
intros. simpl. apply H. Defined.

Definition sum_serial
  {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop} (sa : Serialize A P1) (sb : Serialize B P2) :
  Serialize (A + B) (sum_cond P1 P2) :=
  fun bf pos z =>
    match z as s return (option (BA.Buffer * BA.Pos * sum_cond P1 P2 s)) with
    | inl a =>
        (fun a0 : A => prepend_serialize_fixed false (T_Serial _ _ bool_format) sa bf pos a0) a
    | inr b =>
        (fun b0 : B => prepend_serialize_fixed true (T_Serial _ _ bool_format) sb bf pos b0) b
    end.      

Definition sum_parse
  {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop} (sa : Parse A P1) (sb : Parse B P2) :
  Parse (A + B) (sum_cond P1 P2) :=
    bind_parse
      (T_Parse _ _ bool_format)
      (fun b0 _ _ =>
         if b0
         then
           bind_parse sb
             (fun b pf_b flg =>  return_parse (exist _ (inr b) pf_b) flg)
         else
           bind_parse sa
             (fun a pf_a flg =>  return_parse (exist _ (inl a) pf_a) flg)
      ).

Definition sum_to_len
  {A B : Set} (sa : A -> option nat) (sb : B -> option nat) :
  (A + B) -> option nat :=
  fun z => 
    add_opt (Some 1)
      (match z with
       | inl a => sa a
       | inr b => sb b
       end).

Section sum_format_proofs.
  Context {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop} (sa : T_Format A P1) (sb : T_Format B P2).

  Lemma sum_enc_consist : encode_consistent (A + B)%type (sum_cond P1 P2)
                            (sum_serial (T_Serial A P1 sa) (T_Serial B P2 sb)).
  Proof.
    unfold encode_consistent. intros.
    unfold sum_serial in *.
    destruct a.
    - unfold prepend_serialize_fixed in *. repeat destruct_enc.
      inversion H0. inversion H. subst. 
      eapply CombProp.append_encode_consist.
      + eapply (CombProp.fmt_enc_consist). apply (T_Correct _ _ bool_format).
      + eapply (CombProp.fmt_enc_consist).
        apply (T_Correct _ _ sa).
      + eapply (CombProp.fmt_enc_ni). apply (T_Correct _ _ sa).
      + apply E0.
      + rewrite E. encode_eq.
    - unfold prepend_serialize_fixed in *. repeat destruct_enc.
      inversion H. inversion H0. subst.
      eapply CombProp.append_encode_consist.
      + apply (CombProp.fmt_enc_consist (T_Correct _ _ bool_format)).
      + apply (CombProp.fmt_enc_consist (T_Correct _ _ sb)).
      + apply (CombProp.fmt_enc_ni (T_Correct _ _ sb)).
      + apply E0.
      + rewrite E. encode_eq.
  Qed.
      
  Lemma sum_dec_consist : decode_consistent (A + B)%type (sum_cond P1 P2)
                           (sum_parse (T_Parse A P1 sa) (T_Parse B P2 sb)).
  Proof.
    unfold sum_parse. 
    apply CombProp.bind_parse_consist.
    - apply (CombProp.fmt_dec_consist (T_Correct _ _ bool_format)).
    - intros.
      destruct a; apply CombProp.bind_parse_consist; try (intros; apply CombProp.return_parse_consist).
      + apply (CombProp.fmt_dec_consist (T_Correct _ _ sb)).
      + apply (CombProp.fmt_dec_consist (T_Correct _ _ sa)).
  Qed.
      
  Lemma sum_enc_ni : encode_non_inter (A + B)%type (sum_cond P1 P2)
                       (sum_serial (T_Serial A P1 sa) (T_Serial B P2 sb)).
  Proof.
    unfold encode_non_inter. intros.
    unfold sum_serial, prepend_serialize_fixed in H. 
    destruct a; destruct_enc; inversion H; subst.
    - eapply CombProp.append_non_inter.
      + apply (CombProp.fmt_enc_ni (T_Correct _ _ bool_format)).
      + apply (CombProp.fmt_enc_ni (T_Correct _ _ sa)).
      + apply E.
    - eapply CombProp.append_non_inter.
      + apply (CombProp.fmt_enc_ni (T_Correct _ _ bool_format)).
      + apply (CombProp.fmt_enc_ni (T_Correct _ _ sb)).
      + apply E.
  Qed.
      
  Lemma sum_surj :
    format_correct_surj (A + B)%type (sum_cond P1 P2)
    (sum_serial (T_Serial A P1 sa) (T_Serial B P2 sb))
    (sum_parse (T_Parse A P1 sa) (T_Parse B P2 sb)).
  Proof.
    unfold format_correct_surj. intros. unfold sum_serial, prepend_serialize_fixed in H.
    destruct a; destruct_enc; inversion H; subst.
    + (* inl a0: bool=false, then sa *)
      unfold sum_parse.
      eassert (K := CombProp.append_correct_surj _ _ _ _ _ _
                      (CombProp.fmt_surj (T_Correct _ _ bool_format))
                      (CombProp.fmt_surj (T_Correct _ _ sa))
                      (CombProp.fmt_dec_consist (T_Correct _ _ bool_format))
                      (CombProp.fmt_enc_ni (T_Correct _ _ sa))
                      _ _ _ _ _ _ E).
      unfold Comb.append_parse in K.
      unfold bind_parse, return_parse in K.
      repeat destruct_enc. inversion K. subst.
      match goal with
      | [ Hf : flg_add _ _ = SameVer |- _ ] =>
          destruct (CombProp.flg_add_to_same _ _ Hf) as [? ?]; subst
      end.
      unfold bind_parse, return_parse.
      rewrite E0. simpl. rewrite E1. simpl. decode_eq.
    + (* inr b0: bool=true, then sb *)
      unfold sum_parse.
      eassert (K := CombProp.append_correct_surj _ _ _ _ _ _
                      (CombProp.fmt_surj (T_Correct _ _ bool_format))
                      (CombProp.fmt_surj (T_Correct _ _ sb))
                      (CombProp.fmt_dec_consist (T_Correct _ _ bool_format))
                      (CombProp.fmt_enc_ni (T_Correct _ _ sb))
                      _ _ _ _ _ _ E).
      unfold Comb.append_parse in K.
      unfold bind_parse, return_parse in K.
      repeat destruct_enc. inversion K. subst.
      match goal with
      | [ Hf : flg_add _ _ = SameVer |- _ ] =>
          destruct (CombProp.flg_add_to_same _ _ Hf) as [? ?]; subst
      end.
      unfold bind_parse, return_parse.
      rewrite E0. simpl. rewrite E1. simpl. decode_eq.
  Qed.

  Lemma sum_inj_same : format_correct_inj_same (A + B)%type (sum_cond P1 P2)
    (sum_serial (T_Serial A P1 sa) (T_Serial B P2 sb))
    (sum_parse (T_Parse A P1 sa) (T_Parse B P2 sb)).
  Proof.
    unfold format_correct_inj_same. intros.
    unfold sum_parse in H.
    unfold bind_parse, return_parse in H.
    destruct_enc.
    destruct x0.
    + (* bool=true → inr *)
      destruct_enc. inversion H. subst.
      unfold sum_serial, prepend_serialize_fixed.
      assert (K : Comb.append_parse
                    (T_Parse bool (fun _ : bool => True) bool_format)
                    (T_Parse B P2 sb) bf pos = Some (exist _ (true, x0) (conj I p1), pos', SameVer)).
      { unfold Comb.append_parse. unfold bind_parse, return_parse.
        rewrite E. rewrite E0.
        eassert (J := bool_parse_SameVer _ _ _ _ _ _ E). subst.
        simpl. decode_eq.
      }
      eassert (G := CombProp.append_correct_inj _ _ _ _ _ _
                      (CombProp.fmt_inj_same (T_Correct _ _ bool_format))
                      (CombProp.fmt_inj_same (T_Correct _ _ sb))
                      (CombProp.fmt_enc_ni (T_Correct _ _ bool_format))
                      (CombProp.fmt_enc_ni (T_Correct _ _ sb))
                      _ _ _ _ _ K _ H0).
      destruct G.
      exists x1. split_and.
      rewrite H2. split; auto. encode_eq.
    + (* bool=false → inl *)
      destruct_enc. inversion H. subst.
      unfold sum_serial, prepend_serialize_fixed.
      assert (K : Comb.append_parse
                    (T_Parse bool (fun _ : bool => True) bool_format)
                    (T_Parse A P1 sa) bf pos = Some (exist _ (false, x0) (conj I p1), pos', SameVer)).
      { unfold Comb.append_parse. unfold bind_parse, return_parse.
        rewrite E. rewrite E0.
        eassert (J := bool_parse_SameVer _ _ _ _ _ _ E). subst.
        simpl. decode_eq.
      }
      eassert (G := CombProp.append_correct_inj _ _ _ _ _ _
                      (CombProp.fmt_inj_same (T_Correct _ _ bool_format))
                      (CombProp.fmt_inj_same (T_Correct _ _ sa))
                      (CombProp.fmt_enc_ni (T_Correct _ _ bool_format))
                      (CombProp.fmt_enc_ni (T_Correct _ _ sa))
                      _ _ _ _ _ K _ H0).
      destruct G.
      exists x1. split_and.
      rewrite H2. split; auto. encode_eq.
  Qed.

  Lemma sum_to_len_correct :
    format_to_len_correct (A + B)%type (sum_cond P1 P2)
      (sum_serial (T_Serial A P1 sa) (T_Serial B P2 sb))
      (sum_parse (T_Parse A P1 sa) (T_Parse B P2 sb))
      (sum_to_len (T_to_len A P1 sa) (T_to_len B P2 sb)).
  Proof.
    unfold format_to_len_correct.
    eassert (G := CombProp.append_to_len_correct
                    _ _ _ _ _ _
                    (CombProp.fmt_len_c (T_Correct _ _ bool_format))
                    (CombProp.fmt_len_c (T_Correct _ _ sa))
                    (CombProp.fmt_enc_ni (T_Correct _ _ bool_format))
                    (CombProp.fmt_enc_ni (T_Correct _ _ sa))
           ).
    eassert (G' := CombProp.append_to_len_correct
                     _ _ _ _ _ _
                     (CombProp.fmt_len_c (T_Correct _ _ bool_format))
                     (CombProp.fmt_len_c (T_Correct _ _ sb))
                     (CombProp.fmt_enc_ni (T_Correct _ _ bool_format))
                     (CombProp.fmt_enc_ni (T_Correct _ _ sb))
                  ).
    split.
    - intros. unfold sum_serial, prepend_serialize_fixed in H.
      destruct a; destruct G, G'; unfold sum_to_len.
      + destruct_enc. inversion H; subst.
        apply H0 in E. simpl in E. unfold append_to_len, snd in E.
        auto.
      + destruct_enc. apply H2 in E.
        simpl in E. unfold append_to_len, snd in E.
        inversion H; subst. auto.
    - destruct G as [_ Gdec]. destruct G' as [_ G'dec].
      intros a bf pos pos' pf flg Hdec.
      unfold sum_parse in Hdec. unfold bind_parse, return_parse in Hdec.
      destruct a.
      + (* inl a0 *)
        destruct_enc. destruct x0.
        * destruct_enc. inversion Hdec.
        * destruct_enc. inversion Hdec. subst.
          eassert (J := proj2 (CombProp.fmt_len_c (T_Correct _ _ sa)) _ _ _ _ _ _ E0).
          destruct J as [n Jn]. exists (1 + n).
          unfold sum_to_len. simpl. rewrite Jn. reflexivity.
      + (* inr b0 *)
        destruct_enc. destruct x0.
        * destruct_enc. inversion Hdec. subst.
          eassert (J := proj2 (CombProp.fmt_len_c (T_Correct _ _ sb)) _ _ _ _ _ _ E0).
          destruct J as [n Jn]. exists (1 + n).
          unfold sum_to_len. simpl. rewrite Jn. reflexivity.
        * destruct_enc. inversion Hdec.
  Qed.

  Lemma flag_add_same_id f : flg_add SameVer f = f.
  Proof.
    destruct f; simpl; auto.
  Qed. 
  
  Lemma sum_inj_diff :
    format_correct_inj_diff (A + B)%type (sum_cond P1 P2)
      (sum_serial (T_Serial A P1 sa) (T_Serial B P2 sb))
      (sum_parse (T_Parse A P1 sa) (T_Parse B P2 sb))
      (sum_to_len (T_to_len A P1 sa) (T_to_len B P2 sb)).
  Proof.
    eassert (Ga := CombProp.append_correct_inj_diff
                     _ _ _ _ _ _
                     (CombProp.fmt_inj_diff (T_Correct _ _ bool_format))
                     (CombProp.fmt_inj_diff (T_Correct _ _ sa))
                     (CombProp.fmt_enc_ni (T_Correct _ _ bool_format))
                     (CombProp.fmt_len_c (T_Correct _ _ bool_format))
                     (CombProp.fmt_len_c (T_Correct _ _ sa))).
    eassert (Gb := CombProp.append_correct_inj_diff
                     _ _ _ _ _ _
                     (CombProp.fmt_inj_diff (T_Correct _ _ bool_format))
                     (CombProp.fmt_inj_diff (T_Correct _ _ sb))
                     (CombProp.fmt_enc_ni (T_Correct _ _ bool_format))
                     (CombProp.fmt_len_c (T_Correct _ _ bool_format))
                     (CombProp.fmt_len_c (T_Correct _ _ sb))).
    unfold format_correct_inj_diff.
    intros a bf pos pos' pf flg Hdec.
    unfold sum_parse in Hdec. unfold bind_parse, return_parse in Hdec.
    destruct a.
    - (* inl a0: after inversion+subst, E has bool flag f, E0 has sa flag flg *)
      destruct_enc. destruct x0.
      + destruct_enc. inversion Hdec.
      + destruct_enc. inversion Hdec. subst.
        assert (K : Comb.append_parse (T_Parse bool _ bool_format) (T_Parse A P1 sa) bf pos
                    = Some (exist _ (false, a) (conj t pf), pos', flg_add f flg)).
        { unfold Comb.append_parse, bind_parse, return_parse.
          rewrite E. simpl. rewrite E0. 

          f_equal. f_equal. f_equal. f_equal. apply proof_irrelevance. 
        }
        eassert (J := Ga _ _ _ _ _ _ K).
        destruct J as [min_len Jmin].
        exists min_len. intros pos0 bf0 Hlen.
        pose proof (Jmin pos0 bf0 Hlen) as Jk.
      destruct Jk as [Hleft | Jright].
      * left. unfold sum_to_len, append_to_len in *. simpl in *. exact Hleft.
      * right. destruct_ex. split_and.
        exists x0. exists x1. split. 
        -- unfold sum_serial, prepend_serialize_fixed. rewrite H0. simpl. reflexivity.
        -- exact H1.
  - (* inr b0 *)
    destruct_enc. destruct x0.
    + destruct_enc. inversion Hdec. subst.
      assert (K : Comb.append_parse (T_Parse bool _ bool_format) (T_Parse B P2 sb) bf pos
                  = Some (exist _ (true, b) (conj t pf), pos', flg_add f flg)).
      { unfold Comb.append_parse, bind_parse, return_parse.
        rewrite E. simpl. rewrite E0.
        f_equal. f_equal. f_equal. f_equal. apply proof_irrelevance. }
      eassert (J := Gb _ _ _ _ _ _ K).
      destruct J as [min_len Jmin].
      exists min_len. intros pos0 bf0 Hlen.
      pose proof (Jmin pos0 bf0 Hlen) as Jk.
      destruct Jk as [Hleft | Jright].
      * left. unfold sum_to_len, append_to_len in *. simpl in *. exact Hleft.
      * right. destruct_ex. split_and.
        exists x0. exists x1. split.
        -- unfold sum_serial, prepend_serialize_fixed. rewrite H0. simpl. reflexivity.
        -- exact H1.
    + destruct_enc. inversion Hdec.
  Qed.
  Definition sum_format_correct :
    format_correct (sum_serial (T_Serial A P1 sa) (T_Serial B P2 sb))
      (sum_parse (T_Parse A P1 sa) (T_Parse B P2 sb))
      (sum_to_len (T_to_len A P1 sa) (T_to_len B P2 sb)) :=
    conj sum_enc_consist
      (conj sum_dec_consist
        (conj sum_enc_ni
          (conj sum_surj
            (conj sum_inj_same
              (conj sum_inj_diff sum_to_len_correct))))).

End sum_format_proofs.

Definition sum_format {A B : Set} {P1 : A -> Prop} {P2 : B -> Prop} (sa : T_Format A P1) (sb : T_Format B P2)
  : T_Format (A + B) (sum_cond P1 P2) :=
  mk_format
    _ _
    (sum_serial (T_Serial _ _ sa) (T_Serial _ _ sb))
    (sum_parse (T_Parse _ _ sa) (T_Parse _ _ sb))
    (sum_to_len (T_to_len _ _ sa) (T_to_len _ _ sb))
    (sum_format_correct sa sb).

Definition restrict_add_serialize 
  {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : Serialize A P) : Serialize A P :=
  fun (bf : BA.Buffer) (pos : BA.Pos) (a : A) =>
    if r_dec a
    then
      s bf pos a 
    else
      None.

Definition restrict_add_parse
  {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : Parse A P) : Parse A P :=
  fun (bf : BA.Buffer) (pos : BA.Pos) =>
    match s bf pos with
    | Some (exist _ a pf_p, pos', flg) =>
        if r_dec a then
          Some (exist _ a pf_p, pos', flg)
        else None
    | None => None
    end.

Lemma restrict_add_enc_ni {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P)
  : encode_non_inter _ _ (restrict_add_serialize r_dec (T_Serial A P s)).
Proof.
  unfold encode_non_inter. intros.
  unfold restrict_add_serialize in H.
  destruct (r_dec a); [| inversion H].
  eapply (CombProp.fmt_enc_ni (T_Correct _ _ s)). exact H.
Qed.

Lemma restrict_add_enc_consist {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P)
  : encode_consistent _ _ (restrict_add_serialize r_dec (T_Serial A P s)).
Proof.
  unfold encode_consistent. intros.
  unfold restrict_add_serialize in H, H0.
  destruct (r_dec a); [| inversion H].
  eapply (CombProp.fmt_enc_consist (T_Correct _ _ s)); eassumption.
Qed.

Lemma restrict_add_dec_consist {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P)
  : decode_consistent _ _ (restrict_add_parse r_dec (T_Parse A P s)).
Proof.
  unfold decode_consistent. intros.
  unfold restrict_add_parse in H.
  destruct_enc. destruct_if_in.
  destruct (CombProp.fmt_dec_consist (T_Correct _ _ s) _ _ _ _ _ _ E) as [Hle Huni].
  split; auto. intros.
  unfold restrict_add_parse.
  rewrite (Huni _ _ _ H0), E0. decode_eq.
Qed.

Lemma restrict_add_surj {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P)
  : format_correct_surj _ _ (restrict_add_serialize r_dec (T_Serial A P s))
      (restrict_add_parse r_dec (T_Parse A P s)).
Proof.
  unfold format_correct_surj. intros.
  unfold restrict_add_serialize in H.
  destruct (r_dec a) eqn:Hr; [| inversion H].
  assert (G := CombProp.fmt_surj (T_Correct _ _ s) _ _ _ _ _ _ H).
  unfold restrict_add_parse. rewrite G, Hr. decode_eq.
Qed.

Lemma restrict_add_inj_same {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P)
  : format_correct_inj_same _ _ (restrict_add_serialize r_dec (T_Serial A P s))
      (restrict_add_parse r_dec (T_Parse A P s)).
Proof.
  unfold format_correct_inj_same. intros.
  unfold restrict_add_parse in H.
  destruct_enc. destruct_if_in.
  pose proof (CombProp.fmt_inj_same (T_Correct _ _ s) _ _ _ _ _ E _ H0) as J.
  destruct J as [x J2]. destruct J2 as [Henc Hequiv].
  unfold restrict_add_serialize. rewrite E0, Henc.
  exists x. split; auto. encode_eq.
Qed.

Lemma restrict_add_to_len {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P)
  : format_to_len_correct _ _ (restrict_add_serialize r_dec (T_Serial A P s))
      (restrict_add_parse r_dec (T_Parse A P s)) (T_to_len A P s).
Proof.
  pose proof (CombProp.fmt_len_c (T_Correct _ _ s)) as Len.
  unfold format_to_len_correct in *. destruct Len as [Lenc Ldec].
  split.
  - intros. unfold restrict_add_serialize in H.
    destruct (r_dec a); [| inversion H].
    apply Lenc in H. exact H.
  - intros. unfold restrict_add_parse in H.
    destruct_enc. destruct_if_in.
    apply Ldec in E. exact E.
Qed.

Lemma restrict_add_inj_diff {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P)
  : format_correct_inj_diff _ _ (restrict_add_serialize r_dec (T_Serial A P s))
      (restrict_add_parse r_dec (T_Parse A P s)) (T_to_len A P s).
Proof.
  unfold format_correct_inj_diff. intros.
  unfold restrict_add_parse in H.
  destruct_enc. destruct_if_in.
  pose proof (CombProp.fmt_inj_diff (T_Correct _ _ s) _ _ _ _ _ _ E) as J.
  destruct J as [min_len Jmin]. exists min_len. intros.
  pose proof (Jmin pos0 bf0 H0) as Jk.
  destruct Jk as [Hleft | Jright].
  - left. exact Hleft.
  - right. destruct_ex. (*destruct Jright as [Henc Hle]. *)
    unfold restrict_add_serialize. rewrite E0.
    exists x0. exists x1. destruct H1.  split; auto.
    rewrite H1. encode_eq. 
Qed.

Lemma restrict_add_format_correct
  {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P)
  : format_correct (restrict_add_serialize r_dec (T_Serial A P s))
      (restrict_add_parse r_dec (T_Parse A P s)) (T_to_len A P s).
Proof.
  exact (conj (restrict_add_enc_consist r_dec s)
    (conj (restrict_add_dec_consist r_dec s)
      (conj (restrict_add_enc_ni r_dec s)
        (conj (restrict_add_surj r_dec s)
          (conj (restrict_add_inj_same r_dec s)
            (conj (restrict_add_inj_diff r_dec s)
                  (restrict_add_to_len r_dec s))))))).
Qed.

Definition restrict_add_format
  {A : Set} {P : A -> Prop}
  (r_dec : A -> bool) (s : T_Format A P) : T_Format A P
  :=
  mk_format
    _ _
    (restrict_add_serialize r_dec (T_Serial _ _ s))
    (restrict_add_parse r_dec (T_Parse _ _ s))
    (T_to_len _ _ s)
    (restrict_add_format_correct r_dec s).


Module Type Param_MT.
  Parameter P_Type : Set.
  Parameter P_Cond : P_Type -> Prop.
  Parameter P_Format : T_Format P_Type P_Cond.
End Param_MT.


Lemma log2_same z (pfz : (0 <= z)%Z) : 
  Z.to_nat (Z.log2 z) = Nat.log2 (Z.to_nat z).
Proof. 
  unfold Z.log2.
  destruct z.
  - simpl. compute.  auto.
  - clear pfz.
    induction p.
    + simpl.
      rewrite Pos2Nat.inj_xI.
      rewrite <- (PeanoNat.Nat.add_1_r (2 * Pos.to_nat p)).
      rewrite PeanoNat.Nat.log2_succ_double; try lia.
      destruct p; simpl in *.
      * rewrite Pos2Nat.inj_succ. rewrite IHp. auto.
      * rewrite Pos2Nat.inj_succ. rewrite IHp. auto.
      * compute. auto.
    + simpl.
      rewrite Pos2Nat.inj_xO.
      rewrite  PeanoNat.Nat.log2_double; try lia.
      destruct p; simpl in *.
      * rewrite Pos2Nat.inj_succ.  rewrite IHp. auto.
      * rewrite Pos2Nat.inj_succ. rewrite IHp.  auto.
      * compute. auto.
    + compute. auto.
  - lia.
Qed.

Definition bit_string_eq_dec
  : (forall a b : bit_string_fixed, {a = b} + {a <> b}).
  intros. decide equality.
  - destruct b0, p.
    decide equality.
    + apply PeanoNat.Nat.eq_dec.
    + apply list_eq_dec.
      intros. apply Byte.byte_eq_dec.
  - apply PeanoNat.Nat.eq_dec. 
Defined.
