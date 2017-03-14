DECLARE PLUGIN "ast_plugin"

open Declarations
open Format
open Univ
open Term
open Names

(* util *)

let print (s : string) =
  Pp.pp (Pp.str s)

let print_to_string (pp : formatter -> 'a -> unit) (trm : 'a) =
  Format.asprintf "%a" pp trm

let wrap (s : string) =
  String.concat "" ["(" ; s ; ")"]

let build (node : string) (leaves : string list) =
  wrap (String.concat " " (node :: leaves))

let rec range (min : int) (max : int) =
  if min < max then
    min :: range (min + 1) max
  else
    []

let build_name (n : name) =
  match n with
    Name id -> build "Name" [string_of_id id]
  | Anonymous -> "(Anonymous)"

let build_var (v : identifier) =
  build "Var" [string_of_id v]

let build_meta (n : metavariable) =
  build "Meta" [string_of_int n]

let build_evar (k : existential_key) (c_asts : string list) =
  build "Evar" ((string_of_int (Evar.repr k)) :: c_asts)

let build_rel_named (env : Environ.env) (i : int) =
  let (name, body, typ) = Environ.lookup_rel i env in
  match name with
    Name id -> build_var id
  | Anonymous -> build "Rel" [string_of_int i]

let build_rel (env : Environ.env) (i : int) =
    build_rel_named env i

let build_sort (s : sorts) =
  let s_ast =
    match s with
      Prop _ -> if s = prop_sort then "Prop" else "Set"
    | Type u -> build "Type" [] (* skip universe *)
  in build "Sort" [s_ast]

let build_cast_kind (k : cast_kind) =
  match k with
    VMcast -> "VMcast"
  | DEFAULTcast -> "DEFAULTcast"
  | REVERTcast -> "REVERTcast"
  | NATIVEcast -> "NATIVEcast"

let build_cast (trm_ast : string) (kind : cast_kind) (typ_ast : string) =
  build "Cast" [trm_ast; build_cast_kind kind; typ_ast]

let build_product (n : name) (typ_ast : string) (body_ast : string) =
  build "Prod" [build_name n; typ_ast; body_ast]

let build_lambda (n : name) (typ_ast : string) (body_ast : string) =
  build "Lambda" [build_name n; typ_ast; body_ast]

let build_let_in (n : name) (typ_ast : string) (expr_ast : string) (body_ast : string) =
  build "LetIn" [build_name n; typ_ast; expr_ast; body_ast]

let build_app (f_ast : string) (arg_asts : string list) =
  build "App" (f_ast :: arg_asts)

let build_kername (kn : kernel_name) =
  string_of_kn kn

let get_definition (cd : Declarations.constant_body) =
 match cd.const_body with
   Undef _ ->
     None
 | Def cs ->
     Some (Mod_subst.force_constr cs)
 | OpaqueDef o ->
     Some (Opaqueproof.force_proof (Global.opaque_tables ()) o)

let build_axiom (kn : kernel_name) (typ_ast : string) (u : Instance.t) =
  let kn' = build_kername kn in
  build "Axiom" [kn'; typ_ast]

let build_definition (kn : kernel_name) (typ_ast : string) (u : Instance.t) =
   let kn' = build_kername kn in
   build "Definition" [kn'; typ_ast]

let bindings_for_fix (names : name array) (typs : constr array) =
  Array.to_list
    (CArray.map2_i
      (fun i name typ -> (name, None, Vars.lift i typ))
      names typs)

let build_fix_fun (index : int) (n : name) (typ_ast : string) (body_ast : string) =
  build (build_name n) [string_of_int index; typ_ast; body_ast]

let build_fix (funs : string list) (index : int) =
  build "Fix" [build "Functions" funs; string_of_int index]

let build_cofix (funs : string list) (index : int) =
  build "CoFix" [build "Functions" funs; string_of_int index]

let lookup_mutind_body (i : mutual_inductive) (env : Environ.env) =
  Environ.lookup_mind i env

let build_inductive_name (ind_body : one_inductive_body) =
  let name_id = ind_body.mind_typename in
  build_var name_id

let bindings_for_inductive (env : Environ.env) (mutind_body : mutual_inductive_body) (ind_bodies : one_inductive_body list) =
  List.map
    (fun ind_body ->
      let univ_context = mutind_body.mind_universes in
      let univ_instance = UContext.instance univ_context in
      let name_id = ind_body.mind_typename in
      let mutind_spec = (mutind_body, ind_body) in
      let typ = Inductive.type_of_inductive env (mutind_spec, univ_instance) in
      (Names.Name name_id, None, typ))
    ind_bodies

let build_inductive (body_asts : string list) (u : Instance.t) =
  build "Ind" body_asts

let build_inductive_body (constr_asts : string list) =
  build "inductive_body" constr_asts

let named_constructors (ind_body : one_inductive_body) =
  let constr_names = Array.to_list ind_body.mind_consnames in
  let indexes = List.map string_of_int (range 1 ((List.length constr_names) + 1)) in
  let constrs = Array.to_list ind_body.mind_user_lc in
  List.combine indexes (List.combine constr_names constrs)

let build_constructor (t_ast : string) (index : int) (u : Instance.t) =
  let index' = string_of_int index in
  build "Construct" [t_ast; index']

let build_case (info : case_info) (case_typ_ast : string) (match_ast : string) (branch_asts : string list) =
  let num_args = string_of_int info.ci_npar in
  let match_typ = build "CaseMatch" [match_ast] in
  let branches = build "CaseBranches" branch_asts in
  build "Case" [num_args; case_typ_ast; match_typ; branches]

let build_proj (p_const_ast : string) (c_ast : string) =
  build "Proj" [p_const_ast; c_ast]

let rec build_ast (env : Environ.env) (depth : int) (trm : types) =
  match kind_of_term trm with
    Rel i ->
      build_rel env i
  | Var v ->
      build_var v
  | Meta mv ->
      build_meta mv
  | Evar (k, cs) ->
      let cs' = List.map (build_ast env depth) (Array.to_list cs) in
      build_evar k cs'
  | Sort s ->
      build_sort s
  | Cast (c, k, t) ->
      let c' = build_ast env depth c in
      let t' = build_ast env depth t in
      build_cast c' k t'
  | Prod (n, t, b) ->
      let t' = build_ast env depth t in
      let b' = build_ast (Environ.push_rel (n, None, t) env) depth b in
      build_product n t' b'
  | Lambda (n, t, b) ->
      let t' = build_ast env depth t in
      let b' = build_ast (Environ.push_rel (n, None, t) env) depth b in
      build_lambda n t' b'
  | LetIn (n, t, e, b) ->
      let t' = build_ast env depth t in
      let e' = build_ast env depth e in
      let b' = build_ast (Environ.push_rel (n, Some e, t) env) depth b in
      build_let_in n t' e' b'
  | App (f, xs) ->
      let f' = build_ast env depth f in
      let xs' = List.map (build_ast env depth) (Array.to_list xs) in
      build_app f' xs'
  | Const (c, u) ->
      build_const env depth (c, u)
  | Construct ((i, c_index), u) ->
      let i' = build_ast env depth (Term.mkInd i) in
      build_constructor i' c_index u
  | Ind ((i, i_index), u) ->
      build_minductive env depth ((i, i_index), u)
  | Case (ci, ct, m, bs) ->
      let typ = build_ast env depth ct in
      let match_typ = build_ast env depth m in
      let branches = List.map (build_ast env depth) (Array.to_list bs) in
      build_case ci typ match_typ branches
  | Fix ((is, i), (ns, ts, ds)) ->
      build_fix (build_fixpoint_functions env depth ns ts ds) i
  | CoFix (i, (ns, ts, ds)) ->
      build_cofix (build_fixpoint_functions env depth ns ts ds) i
  | Proj (p, c) ->
      let p' = build_ast env depth (Term.mkConst (Projection.constant p)) in
      let c' = build_ast env depth c in
      build_proj p' c'

and build_const (env : Environ.env) (depth : int) ((c, u) : pconstant) =
  let kn = Constant.canonical c in
  let cd = Environ.lookup_constant c env in
  let global_env = Global.env () in
  match get_definition cd with
    None ->
      begin
        match cd.const_type with
          RegularArity ty -> build_axiom kn (build_ast global_env (depth - 1) ty) u
        | TemplateArity _ -> assert false (* pre-8.5 universe polymorphism *)
      end
  | Some c ->
      build_definition kn (build_ast global_env (depth - 1) c) u

and build_fixpoint_functions (env : Environ.env) (depth : int) (names : name array) (typs : constr array) (defs : constr array)  =
  let env_fix = Environ.push_rel_context (bindings_for_fix names typs) env in
  List.map
    (fun i ->
      let typ = build_ast env depth (Array.get typs i) in
      let def = build_ast env_fix depth (Array.get defs i) in
      build_fix_fun i (Array.get names i) typ def)
    (range 0 (Array.length names))

and build_oinductive (env : Environ.env) (depth : int) (ind_body : one_inductive_body) =
  let constrs =
    List.map
      (fun (i, (n, typ)) -> build (Names.string_of_id n) [i; build_ast env (depth - 1) typ])
    (named_constructors ind_body)
  in build (build "Name" [Names.string_of_id ind_body.mind_typename]) [build_inductive_body constrs]

and build_minductive (env : Environ.env) (depth : int) (((i, i_index), u) : pinductive) =
  let mutind_body = lookup_mutind_body i env in
  let ind_bodies = mutind_body.mind_packets in
  if depth <= 0 then (* don't expand *)
    build_inductive_name (Array.get ind_bodies i_index)
  else (* expand *)
    let ind_bodies_list = Array.to_list ind_bodies in
    let env_ind = Environ.push_rel_context (bindings_for_inductive env mutind_body ind_bodies_list) env in
    let cs = List.map (build_oinductive env_ind depth) ind_bodies_list in
    build_inductive cs u

let apply_to_definition (f : Environ.env -> int -> types -> 'a) (env : Environ.env) (depth : int) (body : types) =
  match (kind_of_term body) with
  | Const _ ->
      f env (depth + 1) body
  | Ind _ ->
      f env (depth + 1) body
  | _ ->
      f env depth body

let print_ast (depth : int) (def : Constrexpr.constr_expr) =
  let (evm, env) = Lemmas.get_current_context() in
  let (body, _) = Constrintern.interp_constr env evm def in
  let ast = apply_to_definition build_ast env depth body in
  print ast

VERNAC COMMAND EXTEND Print_AST
| [ "PrintAST" constr(def) ] ->
  [ print_ast 0 def ]
| [ "PrintAST" constr(def) "with" "depth" integer(depth)] ->
  [ print_ast depth def ]
END

