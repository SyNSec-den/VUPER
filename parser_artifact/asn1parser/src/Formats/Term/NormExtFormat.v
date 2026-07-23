Require Import
  BinInt
  Lia
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Term.Boolean
  ASN1Parser.tact.

Definition sumbool_neg :  forall {P1  : Prop},
       {P1} + {~ P1} ->
       {~P1} + {~ ~P1}.
  intros.
  destruct H.
  - right. intro. destruct (H p).
  - left. auto.
Defined.

Definition sumbool_or1 : forall {P1 P2 : Prop},
  {P1} + {~ P1} ->
  {P2} + {~ P2} -> {P1 \/ P2} + {~ (P1 \/ P2)}.
  intros.
  destruct H.
  - left.  left. auto.
  - destruct H0.
    + left. right. auto.
    + right. intro.
      destruct H.
      * apply (n H).
      * apply (n0 H).
Defined.

(* This is the choosing of the format *)
Definition choose_norm_ext_format
  {A : Set} {P : A -> Prop}
  {P_ext : A -> Prop}
  (fmt_normal : T_Format A P)
  (fmt_ext : T_Format A P_ext)
  (p_dec : dec_P P)
  (p_ext_dec : dec_P P_ext)
  : T_Format (bool * A)
      (fun z : bool * A =>
         (fun _ : bool => True) (fst z) /\
           (fun (a : bool) (z0 : A) =>
              if a
              then
                ~ P z0 /\
                  P_ext z0
              else (P z0)) (fst z) (snd z)) :=
  sigma_format bool_format
    _
    (fun a =>
       if a as b
                 return
                 (T_Format A
                    (fun z : A =>
                       if b
                       then
                         ~ P z /\
                           P_ext z
                       else (P z)))
       then
         restrict_format
           (fun z : A =>
              ~ P z /\ P_ext z)
           fmt_ext
           (fun a H => proj2 H)
           (fun a0 : A =>
              sumbool_and1
                (sumbool_neg
                   (p_dec a0)
                )
                (p_ext_dec a0)
           )
       else fmt_normal).

Lemma normal_ext_format_helper1  {A : Set} {P : A -> Prop}
  {P_ext : A -> Prop} (p_dec : dec_P P)
  :  (forall a : A,
         (fun z : A => P z \/ ~ P z /\ P_ext z) a ->
         (fun z : bool * A =>
            (fun _ : bool => True) (fst z) /\
              (fun (a0 : bool) (z0 : A) =>
                 if a0 then ~ P z0 /\ P_ext z0 else P z0) 
                (fst z) (snd z))
           ((fun z : A =>
               if p_dec z then (false, z) else (true, z)) a) /\
           (fun x : bool * A => snd x)
             ((fun z : A =>
                 if p_dec z then (false, z) else (true, z)) a) =
             a).
Proof.  
  intros.
  simpl in *.  repeat split; auto.
  - destruct (p_dec a); simpl; auto. 
    split; auto.
    destruct H.
    + destruct (n H).
    + split_and; auto.
  - destruct (p_dec a); simpl; auto. 
Qed.

Lemma normal_ext_format_helper2  {A : Set} {P : A -> Prop}
  {P_ext : A -> Prop} (p_dec : dec_P P)
  : (forall b : bool * A,
        (fun z : bool * A =>
           (fun _ : bool => True) (fst z) /\
             (fun (a : bool) (z0 : A) =>
                if a then ~ P z0 /\ P_ext z0 else P z0) 
               (fst z) (snd z)) b ->
        (fun z : A => P z \/ ~ P z /\ P_ext z)
          ((fun x : bool * A => snd x) b) /\
          (fun z : A =>
             if p_dec z then (false, z) else (true, z))
            ((fun x : bool * A => snd x) b) = b).
Proof.
  intros. simpl in *. split_and. destruct b. destruct b eqn:Eb.
  - simpl in *.
    destruct (p_dec a).
    + split_and. destruct (H p).
    + split; auto.
  - simpl in *.
    destruct (p_dec a).
    + split; auto.
    + destruct (n H1).
Qed.

Definition normal_ext_format_dec {A : Set} {P : A -> Prop}
  {P_ext : A -> Prop}
  (p_dec : dec_P P)
  (p_ext_dec : dec_P P_ext)                      
  : dec_P (fun z : A => P z \/ ~ P z /\ P_ext z).
  unfold dec_P. intros.
  apply sumbool_or1.
  - apply p_dec.
  - apply sumbool_and1.
    + apply sumbool_neg.
      apply p_dec.
    + apply p_ext_dec.
Defined.

Definition normal_ext_format
  {A : Set} {P : A -> Prop}
  {P_ext : A -> Prop}
  (fmt_normal : T_Format A P)
  (fmt_ext : T_Format A P_ext)
  (p_dec : dec_P P)
  (p_ext_dec : dec_P P_ext)
  (*: T_Format A (fun z : A => (P z) \/ (~ (P z) /\ (P_ext z))) *)
  :=
   proj_format
      (fun z : A => (P z) \/ (~ (P z) /\ (P_ext z))) 
     (choose_norm_ext_format fmt_normal fmt_ext p_dec p_ext_dec )
     (fun z => match p_dec z with
               | left _ => (false, z) 
               | right _  =>  (true, z) 
     end)
     (fun x => snd x)
     (normal_ext_format_helper1 p_dec)
     (normal_ext_format_helper2 p_dec)
     (normal_ext_format_dec p_dec p_ext_dec).
    
