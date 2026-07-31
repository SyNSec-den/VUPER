open Ppxlib
open Ast_helper
open Ppx_deriving.Ast_convenience

let safe_map f l = List.rev (List.rev_map f l)

let rec expr_of_type typ =
  let loc = typ.ptyp_loc in
  match typ with
  | [%type: unit]  -> [%expr fun (_:unit) -> `Null]
  | [%type: int]   -> [%expr fun (x:int) -> `Int x]
  | [%type: bool]  -> [%expr fun (x:bool) -> `Bool x]
  | [%type: string]  -> [%expr fun (x:string) -> `String x]
  | [%type: [%t? typ] list]  -> [%expr fun x -> `List (List.map [%e expr_of_type typ] x)]

  (* Case of type identifier *)
  | { ptyp_desc = Ptyp_constr ({ txt = lid; _ }, args); _ } ->
    let ser_fn = Exp.ident (mknoloc (Ppx_deriving.mangle_lid (`Suffix "to_jer") lid)) in
    let args_pp = List.map (fun typ -> [%expr [%e expr_of_type typ]]) args in
    
    (* eta-expansion is necessary for recursive groups *)
    app ser_fn args_pp

  | _ ->
    Location.raise_errorf ~loc "No support for this expression: %s"
      (string_of_core_type typ)

let remove_before_double_underscore s =
  let rec find_last_double_underscore idx last_idx =
    match String.index_from_opt s idx '_' with
    | Some i when i < String.length s - 1 && String.get s (i + 1) = '_' ->
        find_last_double_underscore (i + 2) (Some i)
    | Some i -> find_last_double_underscore (i + 1) last_idx
    | None -> last_idx
  in
  match find_last_double_underscore 0 None with
  | Some idx -> String.sub s (idx + 2) (String.length s - idx - 2)
  | None -> s


let replace_underscores_with_hyphens s =
  String.map (fun c -> if c = '_' then '-' else c) s

let rename name =
  name |> remove_before_double_underscore |> replace_underscores_with_hyphens

let increment_suffix s =
  let open Re in
  let re = compile (seq [str "ext"; group (rep1 digit)]) in
  match exec_opt re s with
  | Some g ->
    let num_part = Group.get_opt g 1 in
    (match num_part with
     | Some num -> 
       "ext" ^ string_of_int (int_of_string num + 1)
     | None -> s ^ "nomatch")
  | None -> s  (* If the input does not match "ext<number>", return unchanged *)

(* Label is string. Here I need to change the name of txt *)
let ser_str_of_record loc (labels : label_declaration list) varname =
  let exprs =
    labels |>
    (List.map
      (fun { pld_loc = loc; pld_name = { txt = name; _ }; pld_type; _ } ->
        let field  = Exp.field (evar varname) (mknoloc (Lident name)) in
        (* Here, we need to consider the option type *)
        let new_name = name |> rename |> increment_suffix in 
        match pld_type with
        | [%type: [%t? typ] option] ->
          [%expr
            match [%e field] with
            | Some v ->
              [ [%e str new_name], [%e expr_of_type typ] v ]
            | None ->
              []]
        | _ ->         
          [%expr [[%e str new_name], [%e expr_of_type pld_type] [%e field]]]))
  in
  let list_of_exprs exprs =
    List.fold_right
      (fun e acc -> [%expr [%e e] @ [%e acc]]) (* Concatenating lists *)
      exprs
      [%expr []]
  in 
  [%expr `Assoc [%e list_of_exprs exprs]]


let jer_of_type loc typ_decl =
  let func_name =
    { loc; txt = typ_decl.ptype_name.txt ^ "_to_jer" } in
  let jer_expr =
    (match typ_decl.ptype_kind with
     | Ptype_abstract ->
       (match typ_decl.ptype_manifest with
        | Some t -> expr_of_type t
        | None ->
          Location.raise_errorf ~loc "Cannot derive anything for this abstract type")
     | Ptype_record labels ->
       [%expr fun x -> [%e ser_str_of_record loc labels "x"]]

     | Ptype_variant constrs ->
       constrs |>
       (List.map
          (fun { pcd_name = { txt = name; _ }; pcd_args; _ } ->
             let new_name = rename name in 
             match pcd_args with
             | Pcstr_tuple([]) ->
               if (new_name = "Type")
               then
                 Exp.case
                   (pconstr name [])
                   [%expr `Assoc []]
               else 
                 Exp.case
                   (pconstr name [])
                   [%expr `String [%e str new_name]]
             | Pcstr_tuple(arg::[]) ->
               let arg_expr = app (expr_of_type arg) [(evar "x")] in 
               Exp.case
                 (pconstr name [pvar "x"])
                 [%expr `Assoc [([%e str new_name], [%e arg_expr])]]
             | Pcstr_tuple _ ->
               Location.raise_errorf ~loc "Cannot derive anything for such variant"
             | Pcstr_record _ ->
               Location.raise_errorf ~loc "Cannot derive anything for such variant"))
       |> Exp.function_
     | _ -> Location.raise_errorf ~loc "Cannot derive anything for this type") in
  [%stri let [%p Pat.var func_name] = [%e jer_expr]]

let generate_impl ~ctxt (_rec_flag, type_decls) =
  let loc = Expansion_context.Deriver.derived_item_loc ctxt in
  List.map (fun typ_decl -> jer_of_type loc typ_decl) type_decls

let impl_generator = Deriving.Generator.V2.make_noarg generate_impl

let my_deriver =
  Deriving.add "jer"
    ~str_type_decl:impl_generator

