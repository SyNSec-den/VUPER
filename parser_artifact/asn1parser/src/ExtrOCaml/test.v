Require Import
          Coq.Init.Byte
          Fiat.AbsArray 
          Fiat.AbsComb
          Fiat.ByteBuffer 
          Fiat.ASNAbs.

From Coq Require Extraction.

Require Export
  Fiat.ExtrOCaml.Extract.

(*Extract Constant byte_buffer => "Bytes.bytes".
Extract Constant make => "Bytes.make".*)

Require Import Fiat.Formats.Term.Boolean
  Fiat.Formats.Term.NonNeg
  (* Fiat.Formats.Term.LengthDet *)
  Fiat.Formats.Term.ConsInt
  Fiat.Formats.Comb.Sequence
  Fiat.Formats.Comb.SeqImpl.

Require Import Lia.
Require Import ZArith.

(* All these operations shall be opaque.  *)
Opaque byte_make byte_get byte_set Byte.to_nat Byte.of_nat.


(* I need to make everything in FC opaque *)

Opaque FC.bind_parse FC.restrict_parse FC.proj_parse
  FC.return_parse.
Opaque FC.restrict_serialize FC.proj_serialize FC.sigma_serialize
  FC.append_serialize.

Opaque ByteParser.read_n_nat ByteParser.read_unit.
Opaque ByteParser.put_n_nat ByteParser.put_unit. 

Require Import Fiat.Formats.Comb.gcd.

Opaque bool_enc unit_enc unit_dec.
Opaque opt_bind opt_serialize opt_parse
  dft_serialize dft_parse fail_parse append_parse
  prepend_serialize put_none.

Opaque bool_list_serialize bool_list_parse.
Opaque det_enc small_enc det_dec small_dec. 


(* About the length or parse in the CT *)


(*
Definition norm_small_det_dec_PT := PT.Parse_T (normally_small_len_det_format). 

Definition uncons_det_dec_PT := PT.Parse_T (uncons_len_det_format).
 *)

(*
Definition dec_after_enc {A : Set} {P : A -> Prop}
  (enc : FC.Serialize A P)
  (dec : FC.Parse A P)
  (bf : ByteBuffer) (pos : BytePos) (a : A)  :=
  match enc bf pos a  with
  | Some (bf', pos', _) =>
      dec bf' pos
  | None => None
  end.
*)

(* Here, this part of the code could be directly be written in 
   OCaml, so that we could potentially test more cases, instead 
   of having to compile everytime for a new variable.
 *)

(* 
Definition a1 := byte_make 10 x00.

Definition a2 := byte_set a1 0 x10.

Definition a3 :=
  a' <-opt byte_set a1 0 x00 ;;
  norm_small_det_dec_PT a' (pos_con 0 I0).

Definition a4 :=
  match a3 with
  | Some (exist _ x _, _) => print_nat x
  | None => tt
  end.
 *)


Definition Proj1  {A A' : Set} {P2 : A' -> Prop}
  (s :  AbsFormat.Format A' P2)
  (f : A -> A')
  (f_inv : A' -> A)
  (P2' : A' -> Prop)
  (P2_imp : forall {a' : A'}, P2 a' -> P2' a')
  (imp : forall a : A, f_inv (f a) = a)
  (imp_inv : forall a' : A', P2' a' -> f (f_inv a') = a')
  := AbsFormat.Proj (fun x => P2 (f x)) s f f_inv
       (fun x px => conj px (imp x))
       (fun y py => conj
                      (eq_ind y (fun y0 => P2 y0)
                         py (f (f_inv y))
                         (eq_sym (imp_inv y (P2_imp py))))
                      (imp_inv y (P2_imp py)))
       (fun z => AbsFormat.decidable_serialize s (f z)).

Definition Proj3 {A A' : Set} {P2 : A' -> Prop}
  (s :  AbsFormat.Format A' P2)
  (f : A -> A')
  (f_inv : A' -> A)
  (imp : forall a : A, P2 (f a) /\ f_inv (f a) = a)
  (imp_inv : forall a' : A', P2 a' -> f (f_inv a') = a')
  := AbsFormat.Proj (fun _ => True) s f f_inv
       (fun x _ => (imp x))
       (fun y py => conj I (imp_inv y py))
       (fun z => left I).

Definition Proj2 {A A' : Set} {P2 : A' -> Prop}
  (s :  AbsFormat.Format A' P2)
  (f : A -> A')
  (f_inv : A' -> A)
  (imp : forall a : A, f_inv (f a) = a)
  (imp_inv : forall a' : A', f (f_inv a') = a')
  := AbsFormat.Proj (fun x => P2 (f x)) s f f_inv
       (fun x px => conj px (imp x))
       (fun y py => conj 
                      (eq_ind y P2
                         py (f (f_inv y))
                         (eq_sym (imp_inv y)))
                      (imp_inv y))
       (fun z => AbsFormat.decidable_serialize s (f z)).

Ltac imp_solve :=
  let x := fresh "x" in 
  intro x; destruct x; simpl; auto. 

Ltac imp_inv_solve_lp fP2 Py n :=
  first    
    [ unfold fP2 in Py; simpl in Py; Lia.lia |
      (let n' := fresh "n" in
       destruct n as [|n'];
       first [ simpl; reflexivity | 
               (imp_inv_solve_lp fP2 Py n')] ) ].

Ltac imp_inv_solve P2 :=
  let y := fresh "y" in
  let Py := fresh "Py" in 
  intros y Py;
  let n := fresh "n" in
  let ty := fresh "ty" in 
  destruct y as [n ty];
  imp_inv_solve_lp P2 Py n.


Ltac tuple_destruct :=
  repeat match goal with
    | [ x : unit |- _ ] => destruct x
    | [ y : (_ * _) |- _ ] =>
        destruct y
    end.

(* It is simply repeat destruct a number til it exceeds
   
 *)
Ltac enum_solve P n :=
    first    
    [ lia |
      (let n' := fresh "n" in
       destruct n as [|n'];
       auto; enum_solve P n' ) ].

Definition ten_in_range : to_bit_sz 10 <= AbsFormat.INT_MAX_LEN.
  unfold to_bit_sz.
  unfold AbsFormat.INT_MAX_LEN. unfold Nat.log2. simpl.  
  Lia.lia. Qed.

Definition nat0_10 : AbsFormat.Format nat (fun n => n <= 10) :=
  nat_format 10 ten_in_range.

Definition zero_le_ten : (0 <= 10)%Z.
  lia.
Qed.

Definition int0_10_helper : to_bit_sz (Z.to_nat (10 - 0)) <= AbsFormat.INT_MAX_LEN .
  unfold to_bit_sz, AbsFormat.INT_MAX_LEN. simpl. 
  lia. 
Qed.

Definition int0_10 : AbsFormat.Format Z (fun z => (0 <= z <= 10)%Z):=
  int_format 0 10 (zero_le_ten) int0_10_helper.

Definition t0 : list seq_tp :=
  (Normal (Root nat0_10)) :: (Normal (Root bool_format)) ::
    (Optional (Root bool_format)) :: nil.

Definition t1 : list tp :=
  Root bool_format ::  Root nat0_10 :: nil. 

Definition z : tp :=
  Seq_ext_tp
    t0 t1. 

Definition z_typ := Eval compute in (to_type z). 

Definition z_set  := Eval compute in SeqProd.typ_set z_typ. 
Definition z_cond := Eval compute in SeqProd.typ_cond z_typ.

Module enum_test.


  
Inductive t2 :=
 | t2__ok | t2__bad | t2__very.
Lemma t2__nat__helper : to_bit_sz 2 <= AbsFormat.INT_MAX_LEN.
  unfold to_bit_sz, AbsFormat.INT_MAX_LEN. simpl. lia.
Qed.
Definition t2__nat__format : AbsFormat.Format nat (fun z => (z <= 2)) :=
  nat_format 2 t2__nat__helper.

Definition t2__f1 t :=
  match t with
  | t2__ok => 0
  | t2__bad => 1
  | t2__very => 2
  end.
Definition t2__f2 n :=
  match n with
  | 0 => t2__ok
  | 1 => t2__bad
  | 2 => t2__very
  | _ => t2__ok
  end.
Lemma t2__f1f2 : forall x : t2, (t2__f1 x <= 2) /\ t2__f2 (t2__f1 x) = x. imp_solve. Qed.
Lemma t2__f2f1 : forall (y : nat) (H : y <= 2), t2__f1 (t2__f2 y) = y. enum_solve H y. Qed.
Definition t2__format : AbsFormat.Format t2 (fun _ => True) :=
Proj3 t2__nat__format t2__f1 t2__f2 t2__f1f2 t2__f2f1.

End enum_test.
(* Here, we need a way to partially evaluate the coq function. 
   We want the function to be evaluated in Coq instead OCaml.

   This will give a more simplified version of the code, which
   OCaml can actually understand. 
 *)

(* Systematically speaking, all the function that we 
   mapped in Extract shall not be extracted. 
 *)

(* These are Sequence specific function that we opaqued.
   We should simply group them in one file?
   Because they are used in both Seq and SeqExt
 *)


Opaque Nat.mul Nat.shiftr Nat.shiftl Nat.leb Nat.add Nat.sub
  Nat.land Nat.lor.
Opaque Compare_dec.le_dec Compare_dec.le_lt_dec.

Opaque Z.le.

Example z_seq := Eval compute in List.map seq_to_type t0.
Example fmt_type := Eval cbn in seq_parse_prod z_seq.

(* Obviously the Compare_dec.le is mapped to something wrong.
   So we should not compute it here.
 *)
Example bool_len := Eval lazy in to_length_opt (Root bool_format)
.
Example nat_len := Eval lazy in to_length_opt (Root nat0_10). 

Example nat_parse1 := Eval compute in CT.Parse_T nat0_10.
Example bool_parse := Eval compute in CT.Parse_T bool_format. 

Example fmts : fmt_type :=
  (nat_parse1, (bool_parse, (bool_parse, ByteParser.read_unit))).

(* We need to make the previous parse function opaque. *)
Opaque nat_parse1 bool_parse.

(* There is problem with length function. The problem is
   if we evaluate it, it would be very cumbersome.

   A simple solution is to make two verisons of length?
   One is transparent, which will always be evaluated.
   The other one is opaque, thus we can simply carry it
   out.

   Here, in Sequence, it seems to only concern bool
   list.
 *)
Opaque length.
Example p1 := Eval compute in seq_parse z_seq fmts.

Require Import Fiat.Formats.Comb.SeqExtImpl.

Example z_ext := Eval compute in List.map to_type t1.
Example fmt_ext_type := Eval cbn in ext_parse_prod z_ext.

Example fmt_ext : fmt_ext_type :=
  (bool_parse, (nat_parse1, ByteParser.read_unit)).

Opaque open_typ_parse lt_eq_lt_dec to_parse_skip.
Opaque List.firstn.
Example p_ext := Eval lazy in ext_parse z_ext fmt_ext.
Example pz := parse_opt_tuple p1 p_ext.

Example p2 := ext_parse z_ext fmt_ext. 

(* Extraction "FormatTest.ml" p2. *)
(* Extraction "FormatTest.ml" pz. *)

(* The best case senario, I do not need to extract 
   those functions into OCaml, because I am not using them 
   in OCaml anyway. 

   So we do know that if compute has already unfolded a 
   function, then Coq won't extract the function in OCaml.
 *)


  

Module seq_test. 

  Lemma ten_ge_1 : 10 >= 1. Lia.lia. Qed.

  (* Here is the sequence test *)
  Definition l0 : list seq_elem  :=
    (Nor nat (ge 10)) ::
      (Opt bool (fun _ => True)) ::
      (Nor bool (fun _ => True)) ::
      (Dft nat (ge 10) 1 ten_ge_1  PeanoNat.Nat.eq_dec) ::
      nil.

  Definition tp := Eval compute in  seq_type l0. 

  Record seq_new_tp :=
    make_new_seq { L1 : nat ;
                   L2 : option bool;
                   L3 : bool ;
                   L4 : nat ;
    }.
  
  Definition fmts_tp := Eval compute in seq_format_prod l0.

  Definition x1 : tp  :=
    (1, (Some false, (true, (1, tt)))). 

  Definition fmts : fmts_tp :=
    (nat0_10, (bool_format, (bool_format, (nat0_10, AbsFormat.Unit)))).
  
  Definition f1 (x : seq_new_tp) : tp := 
    (L1 x, (L2 x, (L3 x, (L4 x, tt)))).

  Definition f2 (y : tp) : seq_new_tp :=
    match y with
    | (l1, (l2, (l3, (l4, _)))) =>
        make_new_seq l1 l2 l3 l4
    end. 

  (*
    destruct y as [y1 y'].
    destruct y' as [y2 y'].
    destruct y' as [y3 y'].
    destruct y' as [y4 y'].
    unit_destruct. 
    simpl. unfold f1. simpl. reflexivity.
    Qed.
   *)

  (* I will need to rewrite these projection functions such that it would be properly
     defined.
   *)
  Definition seq_test_format :=
    Proj2 (seq_format l0 fmts) f1 f2 f1f2 f2f1. 
  
  Definition seq_parser
    := PT.Parse_T seq_test_format.
  
End seq_test.  

(* Here is the choice test *)
Require Import Fiat.Formats.Comb.Choice
  Fiat.Formats.Comb.SeqProd.

Module choice_test.
  Example l1 : list typ := (typ_cons nat (fun n => n <= 10)) :: bool_typ :: nil.

  Example fmt : get_formats l1
    := (nat0_10, (bool_format, AbsFormat.Unit)).

  Example g0 := get_nth_format l1 fmt 0.

  Example tp_c := Eval compute in choice l1. 

  Example x : tp_c :=
    existT (fun n => typ_set (get_nth_typ l1 n)) 1 true.

  Example two_le : to_bit_sz (length l1 - 1) <= AbsFormat.INT_MAX_LEN.
  unfold to_bit_sz, AbsFormat.INT_MAX_LEN. simpl. Lia.lia.
  Qed.

  Example choice_test_fmt := choice_format l1 two_le fmt.

  (* Here we encounter a new problem, that choice parser would 
   NOT compile to a dependent type in OCaml. Because OCaml does not 
   support such structures. So the only reasonable way is to use 
   the Tagged Union as a inductive type. For example, 
   *)
  Inductive choice_test_type :=
  | Point (n : nat)
  | Valid (b : bool).

  (* This has turned out to be ok-ish. However, 
   the remaining task is 
   1. Find out how to represent extensions. Here the 
      problem is we cannot have as much of the 
      flexibility of Python dict or Python tuples, 
      where the types could be arbitrary. 

   2. We will need to automate the whole process.
      Even though we have some sort of AUTOMATION,
      with the few Ltac's. It is clearly not enough.
      Currently, my idea is that we would 
      - Parse ASN.1 specification file
      - Generate the AST in OCaml
      - Generate Coq definitions from the AST using 
        OCaml
      - 'Compile' the Coq code, as long as it 
        type-checks, we would have the correct 
        definitions. 

      We would be working on the AST and generating 
      Coq file first. This can be defined in OCaml. 
      The reason is that it is very hard to write a 
      ASN.1 spec parser in Coq. While there are many 
      OCaml Parser libraries available. 

   We would do the Sequence thing first. It would be
   very similar. 
   *)

  Definition f1 (x : choice_test_type) : tp_c :=
    match x with
    | Point n => existT (fun n => typ_set (get_nth_typ l1 n)) 0 n
    | Valid b => existT (fun n => typ_set (get_nth_typ l1 n)) 1 b
    end.

  (*
Definition f2 (t : tp_c) : choice_test_type.
  destruct t.
  destruct x0 eqn:E0.
  - apply (Point y).
  - apply (Point 0).
Defined. 
   *)

  Definition g :=  (fun n => typ_set (get_nth_typ l1 n)).
  
  Definition f2 (t : tp_c) : choice_test_type := 
    match t with
    | existT _ a b =>
        (match a as a0 return (a = a0 -> (g a0) -> choice_test_type)  with 
         | 0 => fun (_ : a = 0) (y1 : nat)  => Point y1
         | 1 => fun (_ : a = 1) (y2 : bool) => Valid y2
         | _ => (fun _ _ => Point 0)
         end) eq_refl b
    end.

  Ltac imp_solve :=
    let x := fresh "x" in 
    intros x; destruct x; simpl; auto. 

  Lemma f1f2 : forall x : choice_test_type, f2 (f1 x) = x.
    imp_solve.
  Qed.

  Definition fP2 (t : tp_c) : Prop := (projT1 t) <= 1.

  Ltac imp_inv_solve_lp fP2 Py n :=
    first    
      [ unfold fP2 in Py; simpl in Py; Lia.lia |
        (let n' := fresh "n" in
         destruct n as [|n'];
         first [ simpl; reflexivity | 
                 (imp_inv_solve_lp fP2 Py n')] ) ].

  Ltac imp_inv_solve P2 :=
    let y := fresh "y" in
    let Py := fresh "Py" in 
    intros y Py;
    let n := fresh "n" in
    let ty := fresh "ty" in 
    destruct y as [n ty];
    imp_inv_solve_lp P2 Py n.

  Lemma f2f1 : forall y : tp_c, fP2 y -> f1 (f2 y) = y.
    imp_inv_solve fP2.
  Qed.

  (*
    destruct n as [|n'].
  - simpl. auto.
  - destruct n' as [|n''].
    + simpl. auto.
    + unfold fP2 in Py. simpl in Py.  Lia.lia.
Qed.
   *)

  Definition new_fmt := 
    Proj1 choice_test_fmt f1 f2 fP2
      (fun z pz => proj1 pz) f1f2 f2f1.

  Definition choice_parser := PT.Parse_T new_fmt.
End choice_test.
  *)
