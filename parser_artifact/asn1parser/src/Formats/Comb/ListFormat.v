Require Import   
  ASN1Parser.Formats.Comb
  ASN1Parser.Formats.Term.Unit.

Definition list_and {A : Type} (P : A -> Prop) :=
  fun l => (List.fold_right (fun a v => (P a) /\ v) True l).

Lemma list_and_nil {A : Type} {P : A -> Prop} : 
  list_and P (nil).
  unfold list_and. simpl. apply I.
Qed.

Lemma list_nil_0 {A : Type} : length (A:=A) nil = 0.
  simpl. auto. Qed.

Lemma list_and_cons {A : Type} {P : A -> Prop} :
  forall {a : A} {l : list A}, 
  P a -> list_and P l -> 
  list_and P (cons a l).
intros. simpl. auto.
Qed.

Lemma list_cons_S {A : Type} : forall (a : A) {l : list A} {m : nat},
    length l = m ->
    length (cons a l) = S m.
  intros.  simpl. auto. Qed.

Definition put_fixed_item {A : Set} {P : A -> Prop} (a0 : A) (pf_a0 : P a0) :=
  fun bf pos => match (put_unit bf pos tt) with
                | Some (bf', pos', _) => Some (bf', pos', pf_a0)
                | None => None
                end.

Definition read_fixed_item {A : Set} {P : A -> Prop} (a : {x : A | P x})
  : Parse A P :=
  fun bf pos => match (read_unit bf pos) with
                | Some (_, pos', _) => Some (a, pos', SameVer)
                | None => None
                end. 

Fixpoint list_serial {A : Set} {P : A -> Prop}
  (ser : Serialize A P) (n : nat)
  : Serialize (list A) (fun la => list_and P la /\ length la = n) :=
  match n with
  | 0 => fun bf pos la =>
           match la with
           | nil => put_fixed_item
                      (P := fun l' => list_and P l' /\ length l' = 0)
                      nil (conj list_and_nil list_nil_0)
                      bf pos
           | cons _ _  => None
           end
  | S m =>
      fun bf pos la =>
        match la with
        | nil => None
        | cons h t =>
            match (ser bf pos h) with
            | Some (bf', pos', pf_h) =>
                match (list_serial ser m bf' pos' t) with
                | Some (bf'', pos'', pf_t) => 
                    Some (bf'', pos'',
                        conj (list_and_cons pf_h (proj1 pf_t))
                          (list_cons_S h (proj2 pf_t) ))
                | None => None
                end
            | None => None 
            end
        end
  end.

Fixpoint list_parse {A : Set} {P : A -> Prop}
  (par : Parse A P) (n : nat)
  : Parse (list A) (fun la => list_and P la /\ length la = n) := 
  match n with
  | 0 => read_fixed_item
           (exist _ nil (conj list_and_nil list_nil_0))
  | S m =>
      bind_parse (par)
        (fun h pf_h flg =>
           bind_parse (list_parse par m)
             (fun t pf_t flg2 =>
                return_parse
                  (exist _ (cons h t)
                     (conj (list_and_cons pf_h (proj1 pf_t))
                        (list_cons_S h (proj2 pf_t) )))
                  (flg_add flg flg2)
             )
        )
  end.

Fixpoint list_to_len {A : Set}
  (a_to_len : A -> option nat) (n : nat)
  (la : list A) : option nat :=
  match n with
  | 0 => match la with
         | nil => Some 0
         | cons _ _ => None
         end
  | S m =>
      match la with
      | nil => None
      | cons h t =>
          add_opt (a_to_len h) (list_to_len a_to_len m t)
      end
  end.

