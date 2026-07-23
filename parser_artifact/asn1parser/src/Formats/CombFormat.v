Require Import
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombProp
  ASN1Parser.Array.ByteBuffer
  ASN1Parser.Array.ByteBufferProp.

Require Import ASN1Parser.tact
  Lia.

Definition basic_n_bit_format n (pf_n : n <= INT_MAX_LEN)
  : T_Format nat (fun a : nat => a < Nat.pow 2 n) :=
  mk_format nat (fun a => a < Nat.pow 2 n)
    (put_n_nat n)
    (read_n_nat n)
    (n_nat_to_len n)
    (BPP.basic_n_bit_format_correct n pf_n).

Definition proj_format_correct
  {A B : Set}
  {P2 : B -> Prop}
  (P1 : A -> Prop)
  (f : A -> B)
  (f_inv : B -> A)
  (imp : forall a : A, P1 a -> (P2 (f a) /\ f_inv (f a) = a))
  (imp_inv : forall b : B, P2 b -> (P1 (f_inv b) /\ f (f_inv b) = b))
  (p1_dec : dec_P P1)
  (b_format : T_Format B P2)
  : format_correct (proj_serialize (T_Serial B P2 b_format) f p1_dec)
      (proj_parse (T_Parse B P2 b_format) f_inv
         (fun (b : B) (pf_b : P2 b) => proj1 (imp_inv b pf_b)))
      (fun a : A => T_to_len B P2 b_format (f a)).
Proof.
  destruct b_format. simpl.  
  unfold format_correct in *. split_and.
  split. apply proj_encode_consist; auto.
  split. apply proj_decode_consist; auto.
  split. apply proj_non_inter; auto.
  { apply (fun a pf_a => proj1 (imp a pf_a)). }
  split. apply proj_correct_surj; auto.
  split. apply proj_correct_inj; auto.
  split. apply proj_correct_inj_diff; auto.
  apply proj_correct_to_len; auto.
Qed.

(* Here, given the format of B, we can derive a format for A *)
Definition proj_format {A B : Set}
  {P2 : B -> Prop}
  (P1 : A -> Prop)
  (b_format : T_Format B P2)
  (f : A -> B)
  (f_inv : B -> A)
  (imp : forall a : A, P1 a -> (P2 (f a) /\ f_inv (f a) = a))
  (imp_inv : forall b : B, P2 b -> (P1 (f_inv b) /\ f (f_inv b) = b))
  (p1_dec : dec_P P1)
   : T_Format A P1 := 
  mk_format A P1
    (proj_serialize (T_Serial _ _ b_format) f p1_dec)
    (proj_parse (T_Parse _ _ b_format) f_inv (fun b pf_b => proj1 (imp_inv b pf_b)))
    (fun a => T_to_len _ _ b_format (f a))
    (proj_format_correct _ f f_inv imp imp_inv p1_dec b_format).

Ltac sigma_helper_tact fs :=
  let a := fresh "x" in
  let pf_a := fresh "pf_a" in
  intros a pf_a; destruct (fs a);
      unfold format_correct in *; split_and; simpl; auto.


Definition sigma_format_correct :
  forall {A A' : Set} {P1 : A -> Prop}
    (s : T_Format A P1)
    (P2 : A -> A' -> Prop) (fs : forall a : A, T_Format A' (P2 a)),
    format_correct
      (sigma_serialize (T_Serial A P1 s) P2
         (fun (a : A) (_ : P1 a) => T_Serial A' (P2 a) (fs a)))
      (sigma_parse (T_Parse A P1 s) P2
         (fun (a : A) (_ : P1 a) => T_Parse A' (P2 a) (fs a)))
      (sigma_to_len
         (T_to_len A P1 s)
           (fun (a : A)  => T_to_len A' (P2 a) (fs a))).
Proof. 
  intros. destruct s; simpl. unfold format_correct in *. split_and. split.
  { apply sigma_encode_consist; auto; sigma_helper_tact fs. } split.
  { apply sigma_decode_consist; auto; sigma_helper_tact fs. } split.
  { apply sigma_non_inter; auto; sigma_helper_tact fs. } split.
  { apply sigma_correct_surj; auto; sigma_helper_tact fs. } split.
  { apply sigma_correct_inj; auto; sigma_helper_tact fs. } split.
  { apply sigma_correct_inj_diff; auto; sigma_helper_tact fs. } 
  apply sigma_to_len_correct; auto; sigma_helper_tact fs. 
Qed.

Definition sigma_format {A A': Set} {P1 : A -> Prop} 
  (s : T_Format A P1)
    (P2 : A -> A' -> Prop)
    (fs : forall (a : A), T_Format A' (P2 a))
  : T_Format (A * A') (fun z => P1 (fst z) /\ P2 (fst z) (snd z)) :=
  mk_format (A * A') 
    (fun z => P1 (fst z) /\ P2 (fst z) (snd z))
    (sigma_serialize (T_Serial _ _  s)
       P2 (fun a pf => T_Serial _ _ (fs a)))
    (sigma_parse (T_Parse _ _  s)
       P2 (fun a pf => T_Parse _ _  (fs a)))
    (fun z => add_opt (T_to_len _ _ s (fst z))
             (T_to_len _ _ (fs (fst z)) (snd z)))
    (sigma_format_correct s P2 fs).

Definition append_format_correct :
  forall {A A' : Set} {P1 : A -> Prop}
    {P2 : A' -> Prop}
    (s1 : T_Format A P1)
    (s2 : T_Format A' P2),
    format_correct
      (append_serialize (T_Serial A P1 s1) 
         (T_Serial A' P2 s2))
      (append_parse (T_Parse A P1 s1)
         (T_Parse A' P2 s2))
      (fun z : A * A' =>
         add_opt (T_to_len A P1 s1 (fst z))
           (T_to_len A' P2 s2 (snd z))).
Proof.
  intros. 
  destruct s1, s2. simpl in *.
  unfold format_correct in *.
  split_and. split.
  { apply append_encode_consist; auto.  } split.
  { apply append_decode_consist; auto. } split.
  { apply append_non_inter; auto. } split.
  { apply append_correct_surj; auto. } split.
  { apply append_correct_inj; auto . } split.
  { apply append_correct_inj_diff; auto. }
  apply append_to_len_correct; auto. 
Qed.

Definition append_format 
  {A A' : Set} {P1 : A -> Prop}
  {P2 : A' -> Prop}
  (s1 : T_Format A P1)
  (s2 : T_Format A' P2)
  : T_Format (A * A') (fun z => P1 (fst z) /\ P2 (snd z)) :=
  mk_format (A * A') 
    (fun z => P1 (fst z) /\ P2 (snd z))
    (append_serialize (T_Serial A P1 s1) 
       (T_Serial A' P2 s2))
    (append_parse (T_Parse A P1 s1)
       (T_Parse A' P2 s2))
    (fun z : A * A' =>
       add_opt (T_to_len A P1 s1 (fst z))
         (T_to_len A' P2 s2 (snd z)))
    (append_format_correct s1 s2).

Lemma restrict_format_correct :
  forall {A : Set} {P : A -> Prop}
    (R : A -> Prop)
    (s : T_Format A P)
    (imp : forall a : A, R a -> P a)
    (r_dec : forall a : A, sumbool (R a) (~ (R a))), 
    format_correct (restrict_serialize r_dec (T_Serial A P s))
      (restrict_parse r_dec (T_Parse A P s)) (T_to_len A P s).
Proof.
  intros. destruct s. simpl. unfold format_correct in *.  split_and. split.
  { apply restrict_encode_consist; auto.  } split.
  { apply restrict_decode_consist; auto. } split.
  { apply restrict_non_inter; auto. } split.
  { apply restrict_correct_surj; auto. } split.
  { apply restrict_correct_inj; auto . } split.
  { apply restrict_correct_inj_diff; auto. }
  apply restrict_to_len_correct; auto. 
Qed.

Definition restrict_format
  {A : Set} {P : A -> Prop}
  (R : A -> Prop)
  (s : T_Format A P)
  (imp : forall a : A, R a -> P a)
  (r_dec : forall a : A, sumbool (R a) (~ (R a)))
  :  T_Format A R :=
  mk_format A R
    (restrict_serialize r_dec (T_Serial _ _ s))
    (restrict_parse r_dec (T_Parse _ _ s))
    (T_to_len _ _ s)
    (restrict_format_correct R s imp r_dec).
