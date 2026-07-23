Require Import
          ASN1Parser.Array.ByteBuffer
          ASN1Parser.Formats.Comb.

Fixpoint list_to_prod {X : Type}  (l : list X)
  (f : X -> Type)  (default : X)  : Type  :=
  match l with
  | nil => f default
  | cons h t =>
      prod (f h) (list_to_prod t f default)
  end.

(* Here, to be honest, we do not need to use any
   new definitions here. We could just use the 
   normal sigma definition here.

   No actually, since sigma is of the type Type, 
   we cannot get any more information out ot that. 
   
   However, here typ is better because its Type2 
   I suppose.
 *)
Record typ := typ_cons {
                  typ_set : Set;
                  typ_cond : typ_set -> Prop;
                }.

Notation "{{ A | P }}" := (typ_cons A P)  (at level 110). 

Example t1 := {{ nat | (fun n => n <= 10) }}.

(*Definition get_set_typ (t : typ) : Set :=
  match t with
    typ_cons A _ => A
  end.*)

(*Definition get_types (l : list typ) : Set :=
  list_to_prod l get_set_typ ({{ unit |  (fun _ => True) }}). *)

(* This version of list_to_prod translate to Set
   instead of Type  *)
Fixpoint list_to_prod_set {X : Type}  (l : list X)
  (f : X -> Set)  (default : X)  : Set  :=
  match l with
  | nil => f default
  | cons h t =>
      prod (f h) (list_to_prod_set t f default)
  end.

Definition bool_typ := {{ bool | fun _ => True }}.
Definition unit_typ := {{ unit | fun _ => True }}.

Definition get_types (l : list typ) : Set :=
  list_to_prod_set l typ_set unit_typ.

Definition get_cond (l : list typ) : get_types l -> Prop. 
  intro.
  induction l.
  - apply True.
  - destruct H.
    apply  (typ_cond a t /\ IHl l0).
Defined.

(*Example tp1 := Eval compute in get_types (bool_typ :: bool_typ :: t1 :: nil). Example val : tp1 := (true, (true, (1, tt))). *)

(*Definition get_format_typ (t : typ) :=
  Format (typ_set t) (typ_cond t).  *)

Definition get_formats (l : list typ) :=
  list_to_prod l (fun t => T_Format (typ_set t) (typ_cond t)) unit_typ. 

Definition get_serial_prod (l : list typ) :=
  list_to_prod l (fun t => Serialize (typ_set t) (typ_cond t)) unit_typ.

Definition get_parse_prod (l : list typ) :=
  list_to_prod l (fun t => Parse (typ_set t) (typ_cond t)) unit_typ.

Definition get_to_len_prod (l : list typ) :=
  list_to_prod l (fun t => (typ_set t) -> option nat) unit_typ.

Definition get_nth_prod {X : Type} (l : list X) (f : X -> Type)
  (default : X) (prod_list : list_to_prod l f default) (n : nat)
  : f (List.nth n l default).
  generalize dependent n. induction l.
  - intros. unfold list_to_prod in prod_list.
    destruct n; simpl; apply prod_list. 
  - intros. simpl in *. destruct prod_list. 
    destruct n. 
    + apply f0. 
    + apply (IHl l0 n).
Defined.

Require Import Coq.Logic.FunctionalExtensionality. 

Lemma cond_equiv ( a : typ) (l : list typ) :
    (fun z => get_cond (a :: l) z) = (fun z => typ_cond a (fst z) /\ (get_cond l (snd z))).
Proof. 
  apply functional_extensionality.
  intros. 
  destruct x.
  simpl.
  split; auto.
Qed.

(*Definition prod_format (l : list typ) (fmts : get_formats l)
  : Format (get_types l) (get_cond l).
  induction l.
  - simpl. unfold get_cond. simpl. apply Unit.
  - simpl. destruct fmts.  rewrite cond_equiv.
    apply Append.
    + apply g.
    + apply (IHl l0).
Defined. *)

(* Need to get 'serial prod and parse prod from get_formats.
 *)
Definition fmt_to_prod (l : list typ) (fmts : get_formats l)
  (X : forall A : Set, (A -> Prop) -> Type)
  (T_X : forall (T : Set) (T_Cond : T -> Prop),
      T_Format T T_Cond -> X T T_Cond)
  (X_unit :  X unit (fun _ : unit => True))
      : list_to_prod l (fun t => X (typ_set t) (typ_cond t)) unit_typ.
  induction l.
  - apply X_unit.
  - destruct fmts. 
    apply (T_X _ _ t, IHl l0).
Defined.

Definition fmt_to_prod_no_cond (l : list typ) (fmts : get_formats l)
  (X : forall A : Set, Type)
  (T_X : forall (T : Set) (T_Cond : T -> Prop), T_Format T T_Cond -> X T)
  (X_unit : X unit)
  : list_to_prod l (fun t => X (typ_set t)) unit_typ.
  induction l.
  - apply X_unit.
  - destruct fmts.
    apply (T_X _ _ t, IHl l0). 
Defined.
