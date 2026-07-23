(* We setup a list bool here. *)
Require Import
  ASN1Parser.tact
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.CombFormat
  ASN1Parser.Formats.Term.Boolean
  ASN1Parser.Formats.Comb.ListFormat 
  ASN1Parser.Formats.Comb.ListFormatProp. 

(* If there is a easier way to represent the proposition, 
   we should use it. 
 *)
Lemma list_and_true_is_true (n : nat)
  : forall l : list bool, (fun l : list bool =>
       list_and (fun _ : bool => True) l /\ length l = n) l <->
      (fun l => length l = n) l.
Proof.
  intros. generalize dependent n.   induction l; intros. simpl.
  - split; auto. intro. destruct H; auto. 
  - split.
    + intro. destruct H.  apply H0.
    + intros. simpl in H.  destruct n; inversion H.
      rewrite <- IHl in H1.
       destruct H1. repeat split; auto. 
Qed.

Definition list_bool_format (n : nat)
  :=
  restrict_format
    (fun bl => length bl = n)
    (list_format bool_format n)
    (fun bl => proj2 (list_and_true_is_true n bl))
    (fun bl => PeanoNat.Nat.eq_dec (length bl) n). 

Definition bool_list_serialize (n : nat) :=
  T_Serial _ _ (list_bool_format n). 

Definition bool_list_parse (n : nat) :=
  T_Parse _ _  (list_bool_format n).

Opaque bool_format.

Require Import ASN1Parser.Formats.SameVerProp.

Lemma bool_list_SameVer n :
  parse_to_SameVer (bool_list_parse n).
Proof.
  unfold bool_list_parse, list_bool_format.
  apply restrict_SameVer.
   apply list_SameVer.
  - apply (fun _ => True).
  - apply bool_parse_SameVer.
Qed.
