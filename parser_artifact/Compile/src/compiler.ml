open ASN1Format
open Compiler_basic

(* First, we can try to re-order the definitions. Also, see
   if it is indeed valid. For example, when we cannot find
   the definition anywhere.

   At least when we are trying to generate
   the file, we have to have the correct order.

   Idea: should we use a list or a map?
   Topological Sort?

   For now let's suppose everything is defined in-order.
   Because this problem is not a core issue. 
 *)

(* The second problem is with Terminal types like INTEGER
   or ENUM. So we need a preprocessor that will generate
   all the terminal types first. 

   And boolean would be
   "bool__Format"
   "bool__enc"
   "bool__Format"

   And enum with name s should be 
   Inductive s :=
   | s term name item0
   ...
   
   Then, there shall be a bijective map from s to a nat.
   Since enum will be encoded as a nat under the hood. 
   
 *)


(* Here, this is the first pass? We don't need to generate bool
   or things here, unless they are top-level.
 *)


let get_typ_name (ta : asn1_typ) (name : string) =
  match ta with
  | TERM tt ->
     (match tt with
      | NULL -> "unit"
      | INTEGER _ -> "Z"
      | BOOLEAN -> "bool"
      | Ref rf -> rf ^ "__Type"
      | BIT_STRING NO_CONS_LEN -> "bit_string"
      | OCTET_STRING NO_CONS_LEN -> "octet_string"
      | UnknownMultiString UTF8String -> "String.string"
      | _ -> name ^ "__Type"
     )
  | _ -> name ^ "__Type"

let get_seq_mrk_name (sa : seq_mrk) (name : string) =
  match sa with
  | NORMAL (name2, a_typ) ->
     get_typ_name a_typ (name ^ "__" ^ name2)
  | OPTIONAL (name2, a_typ) ->
     "option " ^ (get_typ_name a_typ (name ^ "__" ^ name2))
  | DEFAULT (name2, a_typ, _) ->
    get_typ_name a_typ (name ^ "__" ^ name2)
  | CONSTRAINT (name2, a_typ, _) ->
    get_typ_name a_typ (name ^ "__" ^ name2)

let get_cond_name (ta : asn1_typ) (name : string) = 
  match ta with
  | TERM tt ->
     (match tt with
      | NULL -> "(fun _ => True)"
      | INTEGER NO_CONS_INT -> "(fun z : Z => (- Z.pow 2 47 <= z <= Z.pow 2 47 - 1)%Z)" 
      | BOOLEAN -> "(fun _ => True)"
      | Ref rf -> rf ^ "__cond"
      | BIT_STRING NO_CONS_LEN -> "bit_string_nc_cond"
      | OCTET_STRING NO_CONS_LEN -> "(fun (b : octet_string) => length b < Nat.pow 2 14)"
      | UnknownMultiString UTF8String -> "utf8_string_cond"
      | _ -> name ^ "__cond"
     )
  | _ -> name ^ "__cond"


let get_dft_name t name =
  match t with
  | TERM tt ->
     (match tt with
      | ENUM _ -> name
      | Ref rf -> rf
      | BIT_STRING _ -> name
      | _ -> "")
  | _ -> ""

let gen_dft_type name t dft_v =
  let typ_name = (get_typ_name t name) in
  let dft_name = (get_dft_name t name) in 
  let cond_name = (get_cond_name t name) in
   match dft_v with
  | INTEGER_DFT n ->
    (* Then the type of t must be integer, or reference *)
    (Printf.sprintf "Transparent %s.\n" cond_name) 
    ^ (Printf.sprintf
        "Lemma %s__dft_helper : %s %d. unfold %s. lia. Qed.\n"
        name cond_name n cond_name)
    ^ (Printf.sprintf "Opaque %s.\n" cond_name) 
     
  | STR_DFT s ->
     (* We know that the actual name should be *)
     if (typ_name = "FilterCoefficient__Type") then
       ((Printf.sprintf
           "Definition %s__dft_helper : %s (inl %s__root__%s). apply I. Qed.\n"
           name cond_name dft_name s)
        ^ "Require Import Coq.Logic.ProofIrrelevance.\n"
        ^ (Printf.sprintf "Definition %s__dft_helper2 : forall (x y : %s), {x = y} + {x <> y}.\n"
             name typ_name)
        ^   "decide equality.
             - (decide equality).
             - destruct b, f. Defined.\n"
       )
     else
       (Printf.sprintf
          "Lemma %s__dft_helper : %s %s__%s. apply I. Qed.\n"
          name cond_name dft_name s )
       ^ (Printf.sprintf
            "Definition %s__dft_helper2 : forall (x y : %s), {x = y} + {x <> y}. decide equality. Defined.\n"
            name typ_name)
  | BITS_DFT _ ->
     (Printf.sprintf
        "Lemma %s__dft_helper : %s (8, ((Byte.xff :: nil), 0)). unfold %s. simpl. unfold Pos.to_nat. simpl. split; auto. Qed.\n"
        name cond_name cond_name)
     

(*  Here is the generation of default marks.
    Note that this approach is extremely RRC layer dependent, in other words,
    the way to deal with reference type is flawed.

    Or i can have a tactic to generate the needed type?
    If it is an ENUM, then
    If it is an INTEGER, then 
 *)
let gen_dft_mrk name t dft_v =
  let typ_name = (get_typ_name t name) in
  let cond_name = (get_cond_name t name) in
  let dft_name = (get_dft_name t name) in 
  match dft_v with
  | INTEGER_DFT n ->
    (* Then the type of t must be integer, or reference *)
    (* First, if  *)

    (Printf.sprintf
        "Dft %s %s %d%%Z %s__dft_helper Z.eq_dec"
        typ_name cond_name n name)

  | STR_DFT s ->
     (* Here, the type must be an ENUM, or ref *)
     (* We will probably have to hard-code the type here. *)
     if (typ_name = "FilterCoefficient__Type")
     then
        (Printf.sprintf
          "Dft %s %s (inl %s__root__%s) %s__dft_helper %s__dft_helper2"
          typ_name cond_name dft_name s name name)
     else
       (Printf.sprintf
          "Dft %s %s %s__%s %s__dft_helper %s__dft_helper2"
          typ_name cond_name dft_name s name name)

  | BITS_DFT _ ->
    (* There should be a better representation, but now use an ad-hoc solution
       we also need to prove bit string eq dec 
    *)
    (Printf.sprintf
       "Dft %s %s (8, ((Byte.xff :: nil), 0)) %s__dft_helper bit_string_eq_dec"
       typ_name cond_name name
    )
     
let get_constraint_cond a_typ ab =
  (match a_typ with
   | TERM (Ref ref_name) ->
     (match ab with
      | ABSENT field_name ->
        Printf.sprintf "(fun z => %s__cond z /\\ %s__%s z = None)" ref_name ref_name field_name
     )
   | _ -> raise (Failure "We only support reference of SEQUENCE here")
  )

let get_seq_mrk_list (sa : seq_mrk) (name : string) =
  match sa with
  | NORMAL (name2, a_typ) ->
    let name3 =  (name ^ "__" ^ name2) in 
    "Nor " ^ ((get_typ_name a_typ name3) ^ " " ^ (get_cond_name a_typ name3))
  | OPTIONAL (name2, a_typ) ->
    let name3 = (name ^ "__" ^ name2) in 
    "Opt " ^ ((get_typ_name a_typ name3) ^ " " ^ (get_cond_name a_typ name3))
  | DEFAULT (name2, a_typ, v) ->
    gen_dft_mrk (name ^ "__" ^ name2) a_typ v
  | CONSTRAINT (name2, a_typ, _) ->
    let name3 = (name ^ "__" ^ name2) in 
    "Nor " ^ ((get_typ_name a_typ name3)) ^ " " ^ (get_cond_name a_typ name3)
(* ^ (get_constraint_cond a_typ ab) *)


let get_seq_mrk_cond (sa : seq_mrk) (name : string) =
  match sa with
  | NORMAL (name2, a_typ) ->
     let name3 = name ^  "__" ^ name2 in 
     get_cond_name a_typ name3
  | OPTIONAL (name2, a_typ) ->
     let name3 = name ^ "__" ^ name2 in 
     "opt_cond " ^ (get_cond_name a_typ name3)
  | DEFAULT (name2, a_typ, _) ->
    get_cond_name a_typ (name ^ "__" ^ name2)
  | CONSTRAINT (name2, a_typ, _) ->
    get_cond_name a_typ (name ^ "__" ^ name2)
    (*get_constraint_cond a_typ ab *)
      

let get_seq_mrk_fst (sa : seq_mrk) =
  match sa with
  | NORMAL (name, _) -> name
  | OPTIONAL (name, _) -> name
  | DEFAULT (name, _, _) -> name
  | CONSTRAINT (name, _, _) -> name

(* Here we also need to add field names, which also might need to be
   reused. We have to use that naming convention. 
 *)
let gen_seq_typ (l : seq_mrk list) (name : string) = 
  (Printf.sprintf "Record %s__Type : Set :=\n  make__%s__Type {\n" name name)
  ^ (String.concat ""
       (List.map
          (fun a ->
            Printf.sprintf "    %s__%s : %s ;\n"
              name (get_seq_mrk_fst a) (get_seq_mrk_name a name))
          l)) 
  ^ "}.\n" 
  ^ (Printf.sprintf "Definition %s__list := (\n" name)
  ^ (String.concat "" (List.map (fun a -> Printf.sprintf " %s ::\n"
                                            (get_seq_mrk_list a name)) l))
  ^ " nil).\n"
  ^ (Printf.sprintf "Definition %s__cond z := \n" name)
  ^ (String.concat ""
       (List.map
          (fun a ->
            Printf.sprintf "  %s (%s__%s z) /\\\n"
              (get_seq_mrk_cond a name) name (get_seq_mrk_fst a))
          l))
  ^ "  True.\n\n"

let gen_seq_typ_empty name =
  (Printf.sprintf "Record %s__Type : Set := make__%s__Type {}.\n" name name)
  ^ (Printf.sprintf "Definition %s__cond (z : %s__Type) := True.\n" name name)

(* This is used in both List Extension and Choice *)
let get_seq_prod_list  (l : (string * asn1_typ) list) (name : string) =
  (Printf.sprintf "Definition %s__list : list typ := (\n" name)
  ^ (String.concat ""
       (List.map
          (fun (name2, a) ->
            let name3 = (name ^ "__" ^ name2) in
            Printf.sprintf "typ_cons %s %s ::\n"
              (get_typ_name a name3) (get_cond_name a name3))
          l))
  ^ " nil).\n" 


(* A similar function as before, but this will take a extension
   list as an input.
 *)
let gen_ext_typ (lseq : seq_mrk list) (l : (ext_mrk list)) (name : string) =
  (Printf.sprintf "Record %s__Type : Set :=\n  make__%s__Type {\n" name name)
  ^ (String.concat ""
       (List.map
          (fun a ->
            Printf.sprintf "    %s__%s : %s ;\n"
              name (get_seq_mrk_fst a) (get_seq_mrk_name a name))
          lseq)) 
  ^ (String.concat ""
       (List.mapi
          (fun i a ->
            match a with
            | EXT_ELEM (name2, a_typ) ->
               let name3 = (name ^ "__" ^ name2) in 
               Printf.sprintf "    %s : option %s ;\n"
                 name3 (get_typ_name a_typ name3)
            | EXT_GRP _ ->
               let name3 = (name ^ "__ext" ^ (string_of_int i)) in
               Printf.sprintf "    %s : option %s__Type ;\n"
                 name3 name3)
          l))
  ^ "}.\n"

  (* There are two lists, a root list and extension list *)
  (* This is the root list *)
  ^ (Printf.sprintf "Definition %s__root_list : list seq_elem := (\n" name)
  ^ (String.concat "" (List.map (fun a -> Printf.sprintf " %s ::\n"
                                            (get_seq_mrk_list a name)) lseq))
  ^ " nil).\n"

  (* this is the ext list *)
  ^ (Printf.sprintf "Definition %s__ext_list : list typ := (\n" name)
  ^ (String.concat ""
       (List.mapi
          (fun i a ->
            match a with
            | EXT_ELEM (name2, a_typ) ->
               let name3 = (name ^ "__" ^ name2) in 
               Printf.sprintf "  typ_cons %s %s ::\n"
                 (get_typ_name a_typ name3)  (get_cond_name a_typ name3)
            | EXT_GRP _ ->
               let name3 = (name ^ "__ext" ^ (string_of_int i)) in
               Printf.sprintf "  typ_cons %s__Type %s__cond ::\n"
                 name3 name3)
          l))
  ^ "  nil).\n"

  (* For conditions, there are two parts as well *)
  ^ (Printf.sprintf "Definition %s__cond (z : %s__Type) := \n" name name)

  ^ "("
  ^ (String.concat ""
       (List.map
          (fun a ->
            Printf.sprintf "  %s (%s__%s z) /\\\n"
              (get_seq_mrk_cond a name) name (get_seq_mrk_fst a))
          lseq))
  ^ "  True) /\\ \n"

  ^ "("
  ^ (String.concat ""
       (List.mapi
          (fun i a ->
            match a with
            | EXT_ELEM (name2, a_typ) ->
               let name3 = (name ^ "__" ^ name2) in 
               Printf.sprintf "  opt_cond %s (%s z) /\\\n"
                 (get_cond_name a_typ name3)
                 name3
            | EXT_GRP _ ->
               let name3 = (name ^ "__ext" ^ (string_of_int i)) in
               Printf.sprintf "  opt_cond %s__cond (%s z) /\\\n"
                 name3 name3)
          l))
  ^ "  True).\n\n"

let gen_choice_typ (l : (string * asn1_typ) list) (name : string) =
  if (List.length l = 1) then 
    match l with
    | [] -> ""
    | (term_name, t) :: _ ->
       (let name3 = (name ^ "__" ^ term_name) in 
       (Printf.sprintf
           "\nInductive %s__Type : Set := | %s : %s -> %s__Type.\n"
           name name3 (get_typ_name t name3) name)
       ^ (Printf.sprintf
            "Definition %s__cond (c : %s__Type) := \n  match c with\n"
            name name)
       ^ (Printf.sprintf "  | %s t => %s t \n"
                 name3
                 (get_cond_name t name3))
       ^ "  end.\n\n"
       )
  else 
    
    ((Printf.sprintf "\nInductive %s__Type : Set :=\n" name)
     ^ (String.concat ""
          (List.map
             (fun (name2, a) ->
               let name3 = (name ^ "__" ^ name2) in 
               Printf.sprintf "  | %s : %s -> %s__Type\n"
                 name3 (get_typ_name a name3) name)
             l))
     ^ ".\n"
     ^ (get_seq_prod_list l name)

     ^ (Printf.sprintf
          "Definition %s__cond (c : %s__Type) := \n  match c with\n"
          name name)
     ^ (String.concat ""
          (List.map
             (fun (name2, a) ->
               let name3 = (name ^ "__" ^ name2) in
               Printf.sprintf "  | %s t => %s t \n"
                 name3
                 (get_cond_name a name3)
             )
             l))
     ^ "  end.\n\n"

     (* There are two helpers, if length l >= 2 *)
     ^ (Printf.sprintf
          "Lemma %s__len_helper1 : to_bit_sz (length %s__list - 1) <= INT_MAX_LEN.\n  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.\n"
          name name)

     ^ (Printf.sprintf
          "Lemma %s__len_helper2 : 2 <= length2 %s__list.\n simpl. lia. Qed.\n"
          name name))


let gen_choice_empty_typ (name : string) =
  (Printf.sprintf "Definition %s__Type := unit.\n" name)
  ^ (Printf.sprintf "Definition %s__cond (c : unit) := True.\n\n" name)

let gen_choice_ext_typ (l : (string * asn1_typ) list) (name : string) =
(Printf.sprintf "\nInductive %s__Type : Set :=\n" name)
^ (String.concat ""
     (List.map
        (fun (name2, a) ->
          let name3 = (name ^ "__" ^ name2) in 
          Printf.sprintf "  | %s : %s -> %s__Type\n"
            name3 (get_typ_name a name3) name)
        l))
^ (Printf.sprintf "  | %s__unknown_ext : nat -> list Byte.byte -> %s__Type\n" name name)
^ ".\n"
^ (get_seq_prod_list l name)

^ (Printf.sprintf
     "Definition %s__cond (c : %s__Type) := \n  match c with\n"
     name name)
^ (String.concat ""
     (List.map
        (fun (name2, a) ->
          let name3 = (name ^ "__" ^ name2) in
          Printf.sprintf "  | %s t => %s t \n"
            name3
            (get_cond_name a name3)
        )
        l))
^ (Printf.sprintf
     "  | %s__unknown_ext n ct => (length %s__list <= n) /\\ (length ct < Nat.pow 2 14)\n"
     name name)
^ "  end.\n\n"

(* There are two helpers, if length l >= 2 *)
^ (Printf.sprintf
     "Lemma %s__len_helper1 : to_bit_sz (length %s__list - 1) <= INT_MAX_LEN.\n  unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.\n"
     name name)

let gen_choice_ext_tail_typ name =
  (Printf.sprintf
     "Definition %s__Type : Set := %s__root__Type + %s__ext__Type.\n"
     name name name )
  ^ (Printf.sprintf
       "Definition %s__cond :=\n  sum_cond %s__root__cond %s__ext__cond.\n"
       name name name)

let gen_length_cons_helper_nat name lb ub : string =
  let lb1 = read_a_int lb in
  let ub1 = read_a_int ub in
  (Printf.sprintf
     "Lemma %s__helper1 : (%s <= %s). %s%s lia. Qed.\n"
     name lb1 ub1
     (print_unfold_int lb) (print_unfold_int ub))
  ^ (Printf.sprintf
     "Lemma %s__helper2 : to_bit_sz (%s - %s) <= INT_MAX_LEN.\n"
     name ub1 lb1)
  ^ "unfold to_bit_sz, INT_MAX_LEN. simpl. lia. Qed.\n"
    

let gen_seq_of_typ c name type_name cond_name =
  (Printf.sprintf "Definition %s__Type := list %s.\n\n"
       name type_name) 
  ^ (match c with
      | FIXED_LEN n ->
        let n1 = read_a_int n in 
        (Printf.sprintf
           "Definition %s__cond (z : %s__Type) := (list_and %s z) /\\ (length z = Z.to_nat %s).\n\n"
           name name cond_name n1)
      | RANGED_LEN (lb, ub) ->
        let lb1 = read_a_int lb in
        let ub1 = read_a_int ub in
        (gen_length_cons_helper name lb ub)
        ^ (Printf.sprintf
             "Definition %s__cond (z : %s__Type) :=  (%s <= Z.of_nat (length z) <= %s)%%Z /\\ (list_and %s z) .\n\n"
             name name lb1 ub1 cond_name )
      | RANGED_LEN_Ext (lb, ub) ->
        let lb1 = read_a_int lb in
        let ub1 = read_a_int ub in
        (gen_length_cons_helper_nat name lb ub)
        ^ (Printf.sprintf
             "Definition %s__cond (z : %s__Type) := (fun z0 => (%s <= z0 <= %s) \\/ (~(%s <= z0 <= %s) /\\ (z0 < Nat.pow 2 14))) (length z) /\\ (list_and %s z) .\n\n"
             name name lb1 ub1 lb1 ub1 cond_name )
      | NO_CONS_LEN ->
        (Printf.sprintf
           "Definition %s__cond (z : %s__Type) := (list_and %s z) /\\ (length z <= Nat.pow 2 14).\n\n"
           name name cond_name)
    )

(* Here, we need to insert the name, here we only consider
   cases without extensions, i.e., Choice, Sequence-Of, and
   Sequence. We'll consider extensions later. 
 *)

let rec all_optional l =
  match l with
  | [] -> true
  | h :: t ->
      match h with
      | OPTIONAL _ -> all_optional t
      | _ -> false

(* if it is a known multi-string, then we actually utilize
   gen_seq 
*)
let rec gen_type (ta : asn1_typ) (name : string) =
  match ta with
  | TERM t ->
    (match t with
     | KnownMultiString (st, lc) ->
       let (type_name, cond_name) =
         (match st with
          | NumericString -> ("Ascii.ascii", "numeric_constraint")
          | IA5String -> ("Ascii.ascii", "ia5_constraint")) in 
       gen_seq_of_typ lc name type_name cond_name
     | _ -> (gen_term_type t name))
  | SEQUENCE lseq ->
     if (List.length lseq = 0)
     then
       (* The case when extension root is empty *)
       gen_seq_typ_empty name
     else
       (String.concat "" (List.map (fun a -> gen_seq_mrk_typ a name) lseq))
       ^ gen_seq_typ lseq name

  | SEQUENCE_Ext (lseq, ext) ->
     let root_name = name ^ "__root" in
     (* let ext_name = name ^ "__ext" in  *)
     (* First we generate the extension root *)
     (if (List.length lseq = 0)
      then
        (* The case when extension root is empty *)
        gen_seq_typ_empty root_name
        (*gen_seq_typ_empty root_name *)
      else 
        (String.concat ""
           (List.map (fun a -> gen_seq_mrk_typ a name) lseq)))

     (* Now we generate the extension, note it could be nothing.
        we also need to sanity test the case of extension being empty.

        However, note that this is a lot different. Because we need to
        support that even though there is no extensions, there might
        be unsupported extensions. We simply resolve the naming issues.
      *)
     ^ (String.concat ""
          (List.mapi (fun i a ->
               gen_ext_mrk_typ a name i) ext))

     ^ (gen_ext_typ lseq ext name)


  | CHOICE lc ->
     (* Similar for choice *)
     (* Again, we need to consider the case where lc is empty or 1.
        when lc is 0, then Obviously nothing is encoded nor decoded.
     
     When lc is 1, we don't need a length determinant. So this is another
     special case
      *)
    if (List.length lc = 0)
    then
      (* We simply use a unit type *)
      gen_choice_empty_typ name
    else 
      (String.concat "" (List.map (fun (name2, a) ->
                             gen_type a (name ^ "__" ^ name2)) lc))
      ^ (gen_choice_typ lc name)


  | CHOICE_Ext (lc, ext) ->
     let root_name = name ^ "__root" in
     let ext_name = name ^ "__ext" in 
     (if (List.length lc = 0)
      then
        gen_choice_empty_typ root_name
      else
        (String.concat "" (List.map (fun (name2, a) ->
                               gen_type a (root_name ^ "__" ^ name2)) lc))
        ^ (gen_choice_typ lc root_name))
     ^ (String.concat "" (List.map (fun (name2, a) ->
                              gen_type a (ext_name ^ "__" ^ name2)) ext))
     (* We also need to generate the extension type *)
     ^ (gen_choice_ext_typ ext ext_name)
     ^ (gen_choice_ext_tail_typ name)

  | SEQUENCE_OF (c, t) ->
     (* For sequence t is simply a term *)
    (gen_type t (name ^ "__seq_of"))
    ^ (let type_name = (get_typ_name t (name ^ "__seq_of")) in 
       let cond_name = get_cond_name t (name ^ "__seq_of") in
       (gen_seq_of_typ c name type_name cond_name))


and gen_seq_mrk_typ (sa : seq_mrk) (name : string) =
  match sa with
  | NORMAL (name2, a_typ) -> gen_type a_typ (name ^ "__" ^ name2)  
  | OPTIONAL (name2, a_typ) -> gen_type a_typ (name ^ "__" ^ name2)  
  | DEFAULT (name2, a_typ, v) ->
    (gen_type a_typ (name ^ "__" ^ name2))
    ^ (gen_dft_type (name ^ "__" ^ name2) a_typ v)
  | CONSTRAINT (name2, a_typ, _) ->
    gen_type a_typ (name ^ "__" ^ name2)

and gen_ext_mrk_typ (ea : ext_mrk) (name : string) (i : int) =
  match ea with
  | EXT_ELEM (name2, a_typ) ->
     gen_type a_typ (name ^ "__" ^ name2)
     
  | EXT_GRP lseq ->

     if all_optional lseq
     then
       (* If the extension group is all optional, then, it is more
          complicated, because we need to add one more layer of condition,
          aka, if
        *)
       let new_name = name ^ "__ext"  ^ (string_of_int i) in
       (String.concat "" (List.map (fun a ->
                              gen_seq_mrk_typ a (new_name ^ "O")) lseq))
       ^ (gen_seq_typ lseq (new_name ^ "O"))
       ^ (Printf.sprintf "Definition %s__Type := %sO__Type.\n" new_name new_name)
       ^ (Printf.sprintf "Definition %s__cond := %sO__cond.\n\n" new_name new_name)

     else
       (* If the extension group is not all optional, we consider it as
          a normal sequence
        *)
       let new_name = name ^ "__ext" ^ (string_of_int i) in
       (String.concat "" (List.map (fun a ->
                              gen_seq_mrk_typ a new_name) lseq))
       ^ (gen_seq_typ lseq new_name)


let gen_type_top_level (ta : asn1_typ) (name : string) =
  match ta with
  | TERM tt ->
    (match tt with
     | KnownMultiString _ -> gen_type ta name
     | _ -> gen_term_type_top_level tt name)
  | _ -> gen_type ta name

let get_x_param_name a param_name get_x_name prev_name x_name =
  (match a with
   | TERM (Ref rf_name) ->
      (if (rf_name = param_name)
       then (param_name ^ x_name)
       else rf_name)
   | _ -> get_x_name a prev_name)  

(* We only support Choice *)
let gen_type_param t name param_name =
  (Printf.sprintf "Section %s__sec.\n" name)
  ^ (Printf.sprintf "Variable %s__Type : Set.\n"
       param_name )
  ^ (Printf.sprintf "Variable %s__cond : %s__Type -> Prop.\n"
       param_name param_name)
  ^ (Printf.sprintf "Variable %s__Format : T_Format %s__Type %s__cond.\n"
       param_name param_name param_name)

  ^ (match t with
     | CHOICE l ->
        gen_choice_typ l name
     | _ -> "")
  

(* Here, since this term might be from extension, we should
   generate the length determinate as well.

   We can define some functions in Coq. That will translate
   the length more easily. 
 *)

let get_op_name (a : asn1_typ) (name : string) =
  match a with
  | TERM tt ->
     get_op_term_name tt name
  | _ -> name
          
let get_seq_mrk_op_name (sa : seq_mrk) (name : string) =
  match sa with
  | NORMAL (name2, ta) ->
     get_op_name ta (name ^ "__" ^ name2)
  | OPTIONAL (name2, ta) ->
     get_op_name ta (name ^ "__" ^ name2)
  | DEFAULT (name2, ta, _) ->
    get_op_name ta (name ^ "__" ^ name2)
  | _ -> ""
           (*CONSTRAINT (name2, ta, ab) ->
    match ab with
    | ABSENT field_name ->
             get_op_name ta (name ^ "__" ^ name2) *)


let gen_seq_op (lseq : seq_mrk list) (name : string) =
  let len_lseq = List.length lseq in

  (* Format list *)
  (Printf.sprintf "\nDefinition %s__Format_Type := Eval cbn in seq_format_prod %s__list.\n"
     name name)
  ^ (Printf.sprintf "Definition %s__Format_list : %s__Format_Type :=\n  " name name)
  ^ (String.concat ""
       (List.map (fun a ->
            match a with
            | CONSTRAINT (_, a_typ, ab) ->
              (match ab with
               | ABSENT field_name ->
                 match a_typ with
                 | TERM (Ref ref_name) ->
                   Printf.sprintf
                     "(restrict_add_format (fun z => match %s__%s z with | Some _ => false | None => true end) %s__Format, " ref_name field_name ref_name
                 | _ -> "")
            | _ -> 
              Printf.sprintf "(%s__Format, " (get_seq_mrk_op_name a name))
          lseq)) 
  ^ "unit_format" 
  ^ (print_n len_lseq ')') 
  ^ ".\n"
  ^ (Printf.sprintf
       "Definition %s__list__Format := (*Eval compute in *) seq_format %s__list %s__Format_list.\n"
       name name name)

  (* Here is F1 which maps Record into Prod  *)
  ^ (Printf.sprintf "Definition %s__F1 z :=\n  " name) 
  ^ (String.concat "" (List.map (fun a ->
                           Printf.sprintf "(%s__%s z, " name (get_seq_mrk_fst a))
                         lseq)) 
  ^ "tt" 
  ^ (print_n len_lseq ')') 
  ^ ".\n" 

  (* Then, F2 maps Prod into Record. *)
  ^ (Printf.sprintf "Definition %s__F2 (y : seq_type %s__list) :=\n  match y with\n  | "
       name name) 
  ^ (String.concat "" (List.mapi (fun i _ -> Printf.sprintf "(i%d, " i) lseq))
  ^ "_" 
  ^ (print_n len_lseq ')')
  ^ (Printf.sprintf "=>\n    make__%s__Type" name)
  ^ (String.concat "" (List.mapi (fun i _ -> Printf.sprintf " i%d" i) lseq))
  ^ (Printf.sprintf "\n  end.\n")

  (* This part is for the two lemmas that shows the condictions are the same *)
  ^ (Printf.sprintf "Lemma %s__F1F2_cond (z : %s__Type)\n  : %s__cond z ->\n  (seq_cond %s__list (%s__F1 z)).\n"
       name name name name name)
  ^ (Printf.sprintf "intro H. unfold %s__cond in H. simpl. auto. Qed.\n" name)

  ^ (Printf.sprintf "Lemma %s__F1F2_cond2 (z : %s__Type)\n : %s__F2 (%s__F1 z) = z.\n"
       name name name name )
  ^ (Printf.sprintf "destruct z. simpl. auto. Qed.\n")

  ^ (Printf.sprintf "Lemma %s__F2F1_cond (y : seq_type %s__list)\n  : seq_cond %s__list y ->\n (%s__cond (%s__F2 y)) /\\  %s__F1 (%s__F2 y) = y.\n"
       name name name name name name name)
  ^ (Printf.sprintf
       "  intro H. split; unfold seq_type in y; simpl in y; repeat destruct_prod.\n - unfold %s__cond. simpl in *. auto.\n - simpl. unfold %s__F1. simpl. destruct_all_unit. auto.   Qed.\n"
       name name)

  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond :=
        proj2_format  %s__cond %s__list__Format
    %s__F1 %s__F2 %s__F1F2_cond  %s__F1F2_cond2 %s__F2F1_cond.\n"
       name name name name name name name name name name)

  ^ (make_op_opaque name)


let gen_seq_empty_op name =
  (Printf.sprintf
     "Definition %s__helper : forall a : %s__Type, True -> True /\\ make__%s__Type = a.\n  eq_unit_helper_tact. Qed.\n"
     name name name)
  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond :=\n (* Eval compute in *) proj_format (fun _ => True) unit_format (fun _ => tt) (fun _ => make__%s__Type)\n    %s__helper unit_unique (fun _ => left I).\n\n"
       name name name name name)
  ^ (make_op_opaque name)
    

let gen_x_list (x : string) default_x (l : (string * asn1_typ) list) (name : string) =
    (Printf.sprintf "Definition %s__%s_list : %s__%s_Type :=\n  " name x name x)
  ^ (String.concat ""
       (List.map (fun (name2, a) ->
            Printf.sprintf "(%s__%s, " (get_op_name a (name ^ "__" ^ name2)) x)
          l))
  ^ default_x
  ^ (print_n (List.length l) ')')
  ^ ".\n"

let gen_format_list  (l : (string * asn1_typ) list) (name : string) =
  gen_x_list "Format" "unit__Format" l name

(*let gen_dec_list  (l : (string * asn1_typ) list) (name : string) =
  gen_x_list "dec" "read_unit" l name

let gen_to_len_list l name =
  gen_x_list "to_len" "unit_to_len" l name *)

(* Generation of list for extensions *)

(* This is for sequence extension *)
let gen_ext_op (lseq : seq_mrk list) (ext : ext_mrk list) (name : string) =
  let len_lseq = List.length lseq in 
  let len_ext = List.length ext in
  
  (* This is root format list *)
  (Printf.sprintf "\nDefinition %s__root_Format_Type := Eval cbn in seq_format_prod %s__root_list.\n"
     name name)
  ^ (Printf.sprintf "Definition %s__root_Format_list : %s__root_Format_Type :=\n  " name name)
  ^ (String.concat ""
       (List.map (fun a ->
            Printf.sprintf "(%s__Format, " (get_seq_mrk_op_name a name))
          lseq)) 
  ^ "unit_format" 
  ^ (print_n len_lseq ')') 
  ^ ".\n"

      (* This is ext format list *)
  (* Need to add the function to check if it is all none *)

  ^ (Printf.sprintf
       "\nDefinition %s__ext_Format_Type := Eval cbn in get_formats %s__ext_list.\n"
       name name)

  ^ (Printf.sprintf "Definition %s__ext_Format_list : %s__ext_Format_Type :=\n  "
         name name)
  ^ (String.concat ""
       (List.mapi (fun i a ->
            match a with
            | EXT_ELEM (name2, a') ->
               Printf.sprintf "(%s__Format, "
                 (get_op_name a' (name ^ "__" ^ name2))
            | EXT_GRP _ ->
               Printf.sprintf "(%s__ext%d__Format, " name i)
          ext))
  ^ "unit__Format"
  ^ (print_n len_ext ')')
  ^ ".\n\n"

  ^ (Printf.sprintf
       "Definition %s__list_type : Set := (seq_type %s__root_list) * (seq_ext_type %s__ext_list).\n"
       name name name)

  ^ (Printf.sprintf
       "Definition %s__list_cond (z : %s__list_type) : Prop :=
        (seq_cond %s__root_list (fst z)) /\\ (seq_ext_cond %s__ext_list (snd z)).\n"
       name name name name)

  ^ (Printf.sprintf
       "Lemma %s__ext_len_lt : length2 %s__ext_list < Nat.pow 2 14.\nProof. simpl. Transparent Nat.pow. unfold Nat.pow. lia. Opaque Nat.pow. Qed.\n\n"
       name name)

  ^ (Printf.sprintf
       "Definition %s__list_format : T_Format %s__list_type %s__list_cond :=\n (* Eval compute in *) seq_ext_format %s__root_list %s__root_Format_list %s__ext_list %s__ext_Format_list %s__ext_len_lt.\n\n"
       name name name name name name name name)
  ^ (Printf.sprintf "Opaque %s__list_format.\n" name)

  (* Here is F1 which maps Record into Prod  *)
  ^ (Printf.sprintf "Definition %s__F1 (z : %s__Type) : %s__list_type :=\n  "
       name name name)
  ^ "(("
  ^ (String.concat "" (List.map (fun a ->
                           Printf.sprintf "(%s__%s z, " name (get_seq_mrk_fst a))
                         lseq)) 
  ^ "tt" 
  ^ (print_n len_lseq ')') 
  ^ "), (\n" 
  ^ (String.concat "" (List.mapi (fun i a ->
                           match a with
                           | EXT_ELEM (name2, _) ->
                              Printf.sprintf "(%s__%s z, " name name2
                           | EXT_GRP _ ->
                              Printf.sprintf "(%s__ext%d z, " name i)
                         ext))
  ^ "tt"
  ^ (print_n len_ext ')')
  ^ ")).\n"

  (* Then, F2 maps Prod into Record. *)
  ^ (Printf.sprintf
       "Definition %s__F2 (y : %s__list_type) : %s__Type :=\n  match y with\n  | "
       name name name)

  ^ "("
  ^ (String.concat "" (List.mapi (fun i _ -> Printf.sprintf "(j%d, " i) lseq))
  ^ "_" 
  ^ (print_n len_lseq ')')
  ^ ", "
  ^ (String.concat "" (List.mapi (fun i _ -> Printf.sprintf "(i%d, " i) ext))
  ^ "_"
  ^ (print_n len_ext ')')
  ^ ")"

  ^ (Printf.sprintf "=>\n    make__%s__Type" name)
  ^ (String.concat "" (List.mapi (fun i _ -> Printf.sprintf " j%d" i) lseq))
  ^ (String.concat "" (List.mapi (fun i _ -> Printf.sprintf " i%d" i) ext))
  ^ "\n  end.\n"

  ^ (Printf.sprintf "Definition %s__helper1 : (forall a : %s__Type, %s__cond a -> %s__list_cond (%s__F1 a)).
                     intros. destruct a. auto. Qed.\n"
       name name name name name)
  ^ (Printf.sprintf "Definition %s__helper2 : (forall a : %s__Type, %s__F2 (%s__F1 a) = a).
                     intros. destruct a. auto. Qed.\n"
       name name name name)
  ^ (Printf.sprintf "Definition %s__helper3 : (forall b : %s__list_type, %s__list_cond b -> %s__cond (%s__F2 b) /\\ %s__F1 (%s__F2 b) = b).
                     intros. destruct b as [y y1]. unfold %s__cond, %s__list_cond in *. simpl.
                     split; unfold seq_type, seq_ext_type in *; simpl in y, y1; repeat destruct_prod; split_and; simpl in *; destruct_all_unit; auto; repeat (split; auto). \n
                     Qed.\n"
       name name name name name name name name name)

  (* Here is the actual encoding/decoding function *)
  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond :=\n proj2_format %s__cond %s__list_format  %s__F1 %s__F2 %s__helper1 %s__helper2 %s__helper3.\n\n"
       name name name name name name name name name name)

  ^ (make_op_opaque name)
       
(* Now the problem is is_ext is not only needed for terms in
   ext, but also those ref terms in ext. We have to backtrace
   those.

   We would have to keep a map that counts if one ref already has
   this get_length function. we will use a hashtable.

   Note that for decoding, we do not need the length function.
   So we ignore this problem for now. We will try to generate
   the parsers first.

   We call it gen_op, it means operations or enc/dec operations
 *)


let gen_le_S_pf n x =
  (print_n_str n "(le_n_S _ _ ")
  ^ "(le_0_n " ^ x ^ ")"
  ^ (print_n n ')')

let gen_choice_op lc name =
  (* enc list *)
  if (List.length lc = 1)
  then
    (* Case where there is only one term in lc *)
    (match lc with
    | [] -> ""
    | (t_name, t) :: _ ->
       let term_name = name ^ "__" ^ t_name in 
       let typ_name = get_typ_name t term_name in
       let cond_name = get_cond_name t term_name in 
       let op_name = get_op_name t term_name in 
       
       (Printf.sprintf
          "Definition %s__F1 (z : %s__Type) : %s := \n  match z with\n  | %s t => t\n  end.\n"
          name name typ_name term_name)

       ^ (Printf.sprintf
            "Definition %s__F2 (y : %s) : %s__Type := %s y.\n\n"
            name typ_name name term_name)

       ^ (Printf.sprintf
            "Definition %s__helper2 : (forall z : %s__Type, %s__cond z -> %s (%s__F1 z)).\nProof. intros. destruct z; auto. Qed.\n"
            name name name cond_name name)
       ^ (Printf.sprintf
            "Definition %s__helper3 : (forall z : %s__Type, %s__F2 (%s__F1 z) = z).\nProof. intros. destruct z; auto. Qed.\n"
            name name name name)
     
       ^ (Printf.sprintf
            "Definition %s__helper4 : (forall y : %s, %s y -> %s__cond (%s__F2 y) /\\  %s__F1 (%s__F2 y) = y).\nProof. intros. destruct y; auto. Qed.\n"
            name typ_name cond_name name name name name)
     
       ^ (Printf.sprintf
            "Definition %s__Format : T_Format %s__Type %s__cond :=\n  proj2_format %s__cond %s__Format %s__F1 %s__F2 %s__helper2 %s__helper3 %s__helper4.\n"
            name name name name op_name name name name name name)
     
       ^ (make_op_opaque name)
     
    )
  else
    (* Normal caes *)
    let len_lc = List.length lc in
    let s_x' = (gen_n_S len_lc "x'") in
    ((Printf.sprintf
        "\nDefinition %s__Format_Type := Eval cbn in get_formats %s__list.\n"
        name name)
     ^ (gen_format_list lc name)
     ^ (Printf.sprintf
          "Definition %s__list__Format := Eval compute in choice_format %s__list %s__len_helper1 %s__len_helper2  %s__Format_list.\n"
          name name name name name)

     (* Mapping *)
     ^ (Printf.sprintf
          "Definition %s__F1 (z : %s__Type) : (choice %s__list) :=\n  match z with\n "
          name name name)
     ^ (String.concat ""
          (List.mapi (fun i (name2, _) ->
               Printf.sprintf "  | %s__%s t => existT _ %d t\n" name name2 i) lc))
     ^ "  end.\n"
     ^ (Printf.sprintf
          "Definition %s__g := (fun n => typ_set (get_nth_typ %s__list n)).\n"
          name name)
     ^ (Printf.sprintf
          "Definition %s__F2 (y : choice %s__list) : %s__Type :=\n  let (x0, t0) := y in\n"
          name name name)
     ^ (Printf.sprintf
          "    (match x0 as n return  (%s__g n -> %s__Type) with\n"
          name name)
     ^ (String.concat ""
          (List.mapi
             (fun i (name2, a) ->
               let name3 = name ^ "__" ^ name2 in 
               Printf.sprintf
                 "    | %d => fun (t : %s) => %s t \n"
                 i (get_typ_name a name3)  name3)
             lc))
     ^ (Printf.sprintf
          " | %s => " (gen_n_S len_lc "n0"))

     ^ (Printf.sprintf
           "(fun (x' : nat) (t'' : %s__g %s) =>" name s_x')
     ^ (Printf.sprintf "let t' :=
           eq_rect (get_nth_typ %s__list %s)
           (fun t' : typ => typ_set t') t'' empty_typ
           (get_nth_typ_ge_len %s__list %s
           %s) in match t' return %s__Type with end) n0
           end t0).\n\n"
          name s_x' name s_x' (gen_le_S_pf len_lc "x'") name)

     ^ (Printf.sprintf
          "Lemma %s__helper2 :  forall (y : %s__Type), %s__cond y -> choice_cond %s__list (%s__F1 y).\n  choice_helper_tact_dec y. Qed.\n\n"
          name name name name name)

     ^ (Printf.sprintf
          "Lemma %s__helper3 :  forall (y : %s__Type), %s__F2 (%s__F1 y) = y.\n  choice_helper_tact_dec y. Qed.\n\n"
          name name name name)
     ^ "Transparent length.\n"
     ^ (Printf.sprintf
          "Lemma %s__helper4 : (forall b : choice %s__list, choice_cond %s__list b -> %s__cond (%s__F2 b) /\\ %s__F1 (%s__F2 b) = b).\n"
          name name name name name name name)
    ^ "Proof. intros. destruct b as [x t]; split; choice_helper_tact0 H x t. Qed.\n"

     (* enc/dec function for Choice *)
     ^ (Printf.sprintf "Opaque length %s__F1 %s__F2.\n" name name)
     ^ (Printf.sprintf
          "Definition %s__Format : T_Format %s__Type %s__cond :=\n  (* Eval compute in *) proj2_format %s__cond %s__list__Format %s__F1 %s__F2 %s__helper2 %s__helper3 %s__helper4.\n"
          name name name name name name name name name name)

     ^ (make_op_opaque name))

let gen_choice_ext_op ext name =
  (* to_len list *)
  let ext_len = List.length ext in
  let s_x' = (gen_n_S ext_len "x'") in

  (Printf.sprintf
     "\nDefinition %s__Format_Type := Eval cbn in get_formats %s__list.\n"
     name name)
  ^ (gen_format_list ext name)
  ^ (Printf.sprintf
       "Definition %s__list__Format := Eval compute in choice_ext_format %s__list %s__Format_list.\n"
       name name name)

  (* Mapping *)
  ^ (Printf.sprintf
       "Definition %s__F1 (z : %s__Type) : choice_ext_typ (choice %s__list) :=\n  match z with\n "
       name name name)
  ^ (String.concat ""
       (List.mapi (fun i (name2, _) ->
            Printf.sprintf "  | %s__%s t => known_ext (existT _ %d t)\n" name name2 i) ext))
  ^ (Printf.sprintf "  | %s__unknown_ext n ct => unknown_ext n ct\n" name)
  ^ "  end.\n"
  ^ (Printf.sprintf
       "Definition %s__g := (fun n => typ_set (get_nth_typ %s__list n)).\n"
       name name)
  ^ (Printf.sprintf
       "Definition %s__F2 (y : choice_ext_typ (choice %s__list)) : %s__Type :=\n  match y with\n"
       name name name)
  ^ "  | known_ext y' =>\n"
  ^ (Printf.sprintf
       "      let (x0, t0) := y' in\n      (match x0 as n return  (%s__g n -> %s__Type) with\n"
       name name)
  ^ (String.concat ""
       (List.mapi
          (fun i (name2, a) ->
            let name3 = name ^ "__" ^ name2 in 
            Printf.sprintf
              "      | %d => fun (t : %s) => %s t \n"
              i (get_typ_name a name3)  name3)
          ext))
  ^ (Printf.sprintf
       "      | %s => " (gen_n_S ext_len "n0"))

  ^ (Printf.sprintf
       "(fun (x' : nat) (t'' : %s__g %s) =>" name s_x')
  ^ (Printf.sprintf "let t' :=
                     eq_rect (get_nth_typ %s__list %s)
                     (fun t' : typ => typ_set t') t'' empty_typ
                     (get_nth_typ_ge_len %s__list %s
                     %s) in match t' return %s__Type with end) n0
                     end t0)\n"
       name s_x' name s_x' (gen_le_S_pf ext_len "x'") name)
  ^ (Printf.sprintf "  | unknown_ext n ct => %s__unknown_ext n ct\n" name)
  ^ "  end.\n\n"

  ^ (Printf.sprintf
       "Lemma %s__helper2 :  forall (y : %s__Type), %s__cond y -> choice_ext_cond (length %s__list) (choice_cond %s__list) (%s__F1 y).\n  choice_helper_tact_dec y. Qed.\n\n"
       name name name name name name)

  ^ (Printf.sprintf
       "Lemma %s__helper3 :  forall (y : %s__Type), %s__F2 (%s__F1 y) = y.\n  choice_helper_tact_dec y. Qed.\n\n"
       name name name name)
  ^ "Transparent length.\n"
  ^ (Printf.sprintf
       "Lemma %s__helper4 : (forall b : choice_ext_typ (choice %s__list), choice_ext_cond (length %s__list) (choice_cond %s__list) b -> %s__cond (%s__F2 b) /\\ %s__F1 (%s__F2 b) = b).\n"
       name name name name name name name name)
  ^ "Proof. intros. destruct b as [b | n ct].\n"
  ^ "  - destruct b as [x t]; split; choice_helper_tact0 H x t.\n"
  ^ "  - simpl in *. split; auto.\n"
  ^ "Qed.\n"

  (* enc/dec function for Choice *)
  ^ (Printf.sprintf "Opaque length %s__F1 %s__F2.\n" name name)

  (* format for Choice *)
  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond :=
        proj2_format %s__cond %s__list__Format %s__F1 %s__F2 %s__helper2 %s__helper3 %s__helper4.\n"
       name name name name name name name name name name)

  ^ (make_op_opaque name)

let gen_choice_ext_tail_op name =
  (Printf.sprintf
     "Definition %s__Format : T_Format %s__Type %s__cond := sum_format %s__root__Format %s__ext__Format.\n"
     name name name name name)
 
  ^ (make_op_opaque name)


let gen_choice_empty_op name =
  (Printf.sprintf
     "\nDefinition %s__Format : T_Format %s__Type %s__cond := unit_format.\n"
     name name name)

  ^ (make_op_opaque name)

let gen_seq_of_op c name op_name =
  (match c with
   | FIXED_LEN n ->
      let n1 = read_a_int n in
      (Printf.sprintf
         "Definition %s__Format : T_Format %s__Type %s__cond := seq_of_fixed_format %s__Format %s.\n\n"
         name name name 
         op_name
         n1)
   
   | RANGED_LEN (lb, ub) ->
      let lb1 = read_a_int lb in
      let ub1 = read_a_int ub in 
      (Printf.sprintf
         "Definition %s__Format : T_Format %s__Type %s__cond := seq_of_format %s__Format %s %s %s__helper1 %s__helper2.\n\n"
         name name name 
         op_name
         lb1 ub1
         name name)
   | RANGED_LEN_Ext (lb, ub) ->
     let lb1 = read_a_int lb in
     let ub1 = read_a_int ub in 
     (Printf.sprintf
        "Definition %s__Format : T_Format %s__Type %s__cond := seq_of_ext_format %s__Format %s %s %s__helper1 %s__helper2.\n\n"
        name name name 
        op_name
        lb1 ub1
        name name)
     
   | NO_CONS_LEN -> ""
  )
  ^ (make_op_opaque name)


let gen_seq_ext_grp l name =

  (* Here, i need to generate the proof that matches in Coq *)
  (* It will generate the seq-op here, with another name *)
  (gen_seq_op l (name ^ "O"))

  ^ (Printf.sprintf "Definition %s__check_all_none (b : %sO__Type) : bool :=\n"
       name name )
  ^ (Printf.sprintf "match b with \n  | make__%sO__Type %s => false \n  | _ => true \n end.\n"
       name (print_n_str (List.length l) "None "))

  ^ (Printf.sprintf
       "Definition %s__Format : T_Format %s__Type %s__cond :=\n  restrict_add_format %s__check_all_none %sO__Format.\n\n"
       name name name name name )

  ^ (make_op_opaque name)

let rec gen_op (ta : asn1_typ) (name : string) =
  match ta with
  | TERM tt ->
    (* Here I don't need to do it for bool, or even ref? *)
    (match tt with
     | KnownMultiString (st, lc) ->
       let op_name =
         (match st with
          | NumericString -> "numeric_string"
          | IA5String -> "ia5_string")  in 
       gen_seq_of_op lc name op_name
     | _ -> (gen_term_op tt name))


  | SEQUENCE lseq ->
     if (List.length lseq = 0)
     then
       gen_seq_empty_op name
     else
       (String.concat "" (List.map (fun a -> gen_seq_mrk_op a name) lseq))
       ^ (gen_seq_op lseq name)
  (* ^ (gen_proj_op name) *)

  | SEQUENCE_Ext (lseq, ext) ->
     let root_name = name ^ "__root" in

     (if (List.length lseq = 0)
      then
        gen_seq_empty_op root_name
      else
        (String.concat "" (List.map (fun a -> gen_seq_mrk_op a name) lseq)))

     (* For the extension part *)
     ^ (String.concat ""
          (List.mapi (fun i a ->
               gen_ext_mrk_op a name i) ext))
     ^ (gen_ext_op lseq ext name)

  | CHOICE lc ->
     if (List.length lc = 0)
     then 
       gen_choice_empty_op name
     else 
       (String.concat ""
          (List.map (fun (name2, a) ->
               gen_op a (name ^ "__" ^ name2)) lc))
       ^ (gen_choice_op lc name)

  | CHOICE_Ext (lc, ext) ->

     let root_name = name ^ "__root" in
     let ext_name = name ^ "__ext" in
     (* extension-root, same as before *)
     (if (List.length lc = 0)
      then 
        gen_choice_empty_op root_name
      else 
        (String.concat ""
           (List.map (fun (name2, a) ->
                gen_op a (root_name ^ "__" ^ name2)) lc))
        ^ (gen_choice_op lc root_name))

     (* Extension part, first, need to generate the
        ops
      *)
     ^ (String.concat ""
           (List.map (fun (name2, a) ->
                gen_op a (ext_name ^ "__" ^ name2)) ext))
     ^ (gen_choice_ext_op ext ext_name)

     ^ (gen_choice_ext_tail_op name)

  | SEQUENCE_OF (c, t) ->
     (gen_op t (name ^ "__seq_of"))
     ^ (let op_name = (get_op_name t (name ^ "__seq_of")) in
        gen_seq_of_op c name op_name)
       
and gen_seq_mrk_op (sa : seq_mrk) (name : string)  =
  match sa with
  | NORMAL (name2, a_typ) ->
     gen_op a_typ (name ^ "__" ^ name2)
  | OPTIONAL (name2, a_typ) ->
     gen_op a_typ (name ^ "__" ^ name2)
  | DEFAULT (name2, a_typ, _) ->
    gen_op a_typ (name ^ "__" ^ name2)
  | CONSTRAINT (name2, a_typ, _) -> 
    gen_op a_typ (name ^ "__" ^ name2)
     

and gen_ext_mrk_op ea name i =
  match ea with
  | EXT_ELEM (name2, a_typ) ->
     gen_op a_typ (name ^ "__" ^ name2)
  | EXT_GRP l ->
     (* Here we need to check if l is an all-optional type *)
     if all_optional l
     then
       let new_name = name ^ "__ext" ^ (string_of_int i) in
       (* Add an "O" to indicate it's all optional *)
       (String.concat "" (List.map (fun a -> gen_seq_mrk_op a (new_name ^ "O")) l))
       ^ (gen_seq_ext_grp l new_name)
     else
       let new_name = name ^ "__ext" ^ (string_of_int i) in 
       (String.concat "" (List.map (fun a -> gen_seq_mrk_op a new_name) l))
       ^ (gen_seq_op l new_name)

(* Similarly, if it is top-level, then we actually need to
   generate all the definitions, because they could be used 
   as a reference in the future.
 *)
let gen_op_top_level (ta : asn1_typ) (name : string) =
  match ta with
  | TERM tt ->
    (match tt with
     | KnownMultiString _ -> gen_op ta name
     | _ -> gen_term_op_top_level tt name)
  | _ -> gen_op ta name

let gen_op_param t name param_name = 
  (match t with
   | CHOICE lc ->
      gen_choice_op lc name
   | _ -> param_name
  )
  ^ (Printf.sprintf "End %s__sec.\n" name)

(* There should be seveal passes on this list.
   First, we generate the terminal types of AbsFormat
   definitions.

   Second, we should generate the sequence-element/
   ext-element. We need to add a layer of combinator before
   the Seq/Choice. Such that it becomes a Record. 
   
   Second, we generate the parser/encoder of these base
   formats.
   Here, we should make something opaque here. 

 *)


let separator =
  {|
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
|}
 
 
(*
let gen_asn1_list_def (l : asn1_list) =
  headers
  ^ (String.concat "" (List.map (gen_asn1_base_def) l))

    (* We need to make some notations opaque Such that some
       computation would actually work. 
     *)
  ^ separator 
  ^ (String.concat "" (List.map (gen_asn1_enc_dec) l))
  ^ {|Extraction "../src/FormatTest.ml" |}
  ^ (String.concat " " (List.map (extract_asn1) l))
  ^ ".\n"
 *)

let header =
{|Require Import ASN1Parser.ExtrOCaml.ExtractHelper.

|}

(* For ASN_Val type, we simply first define all the value definition
   in one file. We could later add all the imported value to it
   as well. Then, we can simply import them in other cases. 
 *)
let gen_asn1_def (a : asn1_def) (module_name : string) =
  match a with
  | ASN_Val _ -> ()
  | ASN_Type (name, t) ->
     (let oc = open_out (proj_name ^ "/" ^ name ^ ".v") in
      Printf.fprintf oc "%s" header;
      Printf.fprintf oc "Require Import %s.%s.\n" proj_name module_name; 
      Printf.fprintf oc "%s" (gen_type_top_level t name);
      Printf.fprintf oc "%s" separator;
      Printf.fprintf oc "%s" (gen_op_top_level t name); 
      close_out oc)
  | ASN_PARAM_Type (name, param_name, t) ->
     (* Here, note that the only param type is the
        setup-release, we can sort of only do part of
        the problem.

        Second thing is the only difference in dealing
        with the type generation, and the op
        generation, is the SetupRelease, which is a choice
        with 
      *)
     
     let oc = open_out (proj_name ^ "/" ^ name ^ ".v") in
     Printf.fprintf oc "%s" header;
     Printf.fprintf oc "%s" (gen_type_param t name param_name);
     Printf.fprintf oc "%s" separator;
     Printf.fprintf oc "%s" (gen_op_param t name param_name); 
     close_out oc

let gen_asn1_type_def (l : asn1_list) module_name =
  List.iter (fun a -> gen_asn1_def a module_name) l

let rec gen_asn1_val_def (l : asn1_def list) : string list =
  match l with
  | [] -> []
  | (ASN_Val (INT_value (name, v))) :: t ->
     (Printf.sprintf "Definition %s := %d%%Z.\n" name v) :: (gen_asn1_val_def t)
  (* (Printf.sprintf "Opaque %s.\n" name)*)
  | _ :: t -> (gen_asn1_val_def t)

let gen_import_list (import_l : asn1_import_list list) =
  (String.concat ""
     (List.map
        (fun (list_name, import_def_list) ->
          (Printf.sprintf "Require Import %s.%s.\n" proj_name list_name)
          ^ (String.concat ""
               (List.map
                  (fun a ->
                    match a with
                    | Val_Import val_name ->
                       Printf.sprintf "Definition %s := (* Eval compute in *) %s.\n"
                         val_name val_name
                    | Type_Import _ -> "" )
                  import_def_list))
        ) import_l))


let gen_asn1_val_def_file (l : asn1_list) (name : string) (import_l : asn1_import_list list) =
  let oc = open_out (proj_name ^ "/" ^ name ^ ".v") in
  Printf.fprintf oc "Require Import BinInt.\n";
  Printf.fprintf oc "%s" (String.concat "" (gen_asn1_val_def l));
  Printf.fprintf oc "%s" (gen_import_list import_l);
  close_out oc

let gen_asn1_module (m : asn1_module) = 
  let (module_name, import_lst, asn_lst) = m in
  (* For the import list, we only care about the value
     imported, which would be added through asn1_val_def
     
   *)
  gen_asn1_val_def_file asn_lst module_name import_lst;
  gen_asn1_type_def asn_lst module_name

(* These functions will generate the necessary _CoqProject file
   for the compliation of the files. We need this to bring
   together out definitions.

   Question, should we group modules by directories? Probably unnecessary.
 *)

let gen_asn1_type_filenames (a : asn1_def) =
  match a with
  | ASN_Val _ -> ""
  | ASN_Type (name, _) -> Printf.sprintf "%s.v" name
  | ASN_PARAM_Type (name, _, _) -> Printf.sprintf "%s.v" name

let gen_asn1_module_filenames (m : asn1_module) = 
  let (module_name, _, asn_lst) = m in
  (Printf.sprintf "%s.v\n" module_name)
  ^ (String.concat "\n" (List.map (gen_asn1_type_filenames) asn_lst))
  ^ "\n"
  
let gen_asn1_coq_proj (a : asn1_obj)  =
  let oc = open_out (proj_name ^ "/_CoqProject") in
  Printf.fprintf oc "-R ../../asn1parser/src ASN1Parser\n";

  (* We just give it a random name *)
  Printf.fprintf oc "-Q . %s\n\n" proj_name;
  List.iter (fun m -> Printf.fprintf oc "%s" (gen_asn1_module_filenames m)) a;
  close_out oc

let gen_extract_file extr_obj_name extr_file_name =
  let oc = open_out (proj_name ^ "/extract_" ^ extr_obj_name ^ ".v") in 
  Printf.fprintf oc "Require Export ASN1Parser.ExtrOCaml.Extract.\n";
  Printf.fprintf oc "Require Import %s.%s.\n" proj_name extr_obj_name;
  Printf.fprintf oc "Extraction \"%s\" %s__enc %s__dec.\n"
    extr_file_name extr_obj_name extr_obj_name

let gen_asn1_obj (a : asn1_obj) =
  gen_asn1_coq_proj a;
  List.iter (gen_asn1_module) a;
