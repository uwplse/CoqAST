DECLARE PLUGIN "ast_plugin"

open Declarations
open Format
open Univ
open Term
open Names
open Pp

let adler32_digest s =
  let d = Adler32.digest s Int32.one 0 (String.length s) in
  Printf.sprintf "%lX" d

let md5_digest s = Digest.to_hex (Digest.string s)

let rec range (min : int) (max : int) =
  if min < max then min :: range (min + 1) max else []

type ast =
| Leaf of string
| Node of string * ast list

let build_name (n : name) =
  match n with
  | Name id -> Node ("Name", [Leaf (string_of_id id)])
  | Anonymous -> Leaf "Anonymous"

let build_var (v : identifier) =
  Node ("Var", [Leaf (string_of_id v)])

let build_rel (env : Environ.env) (i : int) =
  let (name, body, typ) = Environ.lookup_rel i env in
  match name with
    Name id -> build_var id
  | Anonymous -> Node ("Rel", [Leaf (string_of_int i)])

let build_meta (n : metavariable) =
  Node ("Meta", [Leaf (string_of_int n)])

let build_evar (k : existential_key) (c_asts : ast list) =
  Node ("Evar", Leaf string_of_int (Evar.repr k) :: c_asts)

let build_sort (s : sorts) =
  let s_ast =
    match s with
      Prop _ -> if s = prop_sort then "Prop" else "Set"
    | Type _ -> "Type" (* skip universe *)
  in Node ("Sort", [Leaf s_ast])

let string_of_cast_kind (k : cast_kind) =
  match k with
    VMcast -> "VMcast"
  | DEFAULTcast -> "DEFAULTcast"
  | REVERTcast -> "REVERTcast"
  | NATIVEcast -> "NATIVEcast"

let build_cast (trm_ast : ast) (kind : cast_kind) (typ_ast : ast) =
  Node ("Cast", [trm_ast; Leaf (string_of_cast_kind kind); typ_ast])

let build_product (n : name) (typ_ast : ast) (body_ast : ast) =
  Node ("Prod", [build_name n; typ_ast; body_ast])

let build_lambda (n : name) (typ_ast : ast) (body_ast : ast) =
  Node ("Lambda", [build_name n; typ_ast; body_ast])

let build_let_in (n : name) (typ_ast : ast) (expr_ast : ast) (body_ast : ast) =
  Node ("LetIn", [build_name n; typ_ast; expr_ast; body_ast])

let build_app (f_ast : ast) (arg_asts : ast list) =
  Node ("App", f_ast :: arg_asts)

let build_case (info : case_info) (case_typ_ast : ast) (match_ast : ast) (branch_asts : ast list) =
  let num_args = Leaf (string_of_int info.ci_npar) in
  let match_typ = Node ("CaseMatch", [match_ast]) in
  let branches = Node ("CaseBranches", branch_asts) in
  Node ("Case", [num_args; case_typ_ast; match_typ; branches])

let build_proj (p_const_ast : ast) (c_ast : ast) =
  Node ("Proj", [p_const_ast; c_ast])

let build_construct ((k,i):Names.inductive) (index : int) =
  let kn = Names.canonical_mind k in
  Node ("Construct", [Leaf (Names.string_of_kn kn); Leaf (string_of_int index)])

(* use cb.body_of_constant_body? *)
let get_definition (cb : Declarations.constant_body) =
  match cb.const_body with
  | Undef _ ->
    None
  | Def cs ->
    Some (Mod_subst.force_constr cs)
  | OpaqueDef o ->
    Some (Opaqueproof.force_proof (Global.opaque_tables ()) o)

let bindings_for_fix (names : name array) (typs : constr array) =
  Array.to_list
    (CArray.map2_i
       (fun i name typ -> (name, None, Vars.lift i typ))
       names typs)

let build_fix_fun (index : int) (body_ast : ast) =
  Node ("Fun", [Leaf (string_of_int index); body_ast])

let build_fix (index : int) (funs : ast list) =
  Node ("Fix", Leaf (string_of_int index) :: funs)

let build_cofix (index : int) (funs : ast list) =
  Node ("CoFix", Leaf (string_of_int index) :: funs)

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

let named_constructors (ind_body : one_inductive_body) =
  let constr_names = Array.to_list ind_body.mind_consnames in
  let indexes = List.map string_of_int (range 1 ((List.length constr_names) + 1)) in
  let constrs = Array.to_list ind_body.mind_user_lc in
  List.combine indexes (List.combine constr_names constrs)

let rec build_ast (env : Environ.env) (depth : int) (trm : constr) =
  match kind_of_term trm with
  | Rel i ->
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
  | Case (ci, ct, m, bs) ->
    let typ = build_ast env depth ct in
    let match_typ = build_ast env depth m in
    let branches = List.map (build_ast env depth) (Array.to_list bs) in
    build_case ci typ match_typ branches
  | Proj (p, c) ->
    let p' = build_ast env depth (Term.mkConst (Projection.constant p)) in
    let c' = build_ast env depth c in
    build_proj p' c'
  | Construct ((i, c_index), _) ->
    build_construct i c_index
  | Const c ->
    build_const env depth c
  | Fix ((is, i), (ns, ts, ds)) ->
    build_fix i (build_fixpoint_functions env depth ns ts ds)
  | CoFix (i, (ns, ts, ds)) ->
    build_cofix i (build_fixpoint_functions env depth ns ts ds)
  | Ind i ->
    build_minductive env depth i
and build_const (env : Environ.env) (depth : int) ((c, _) : pconstant) =
  let kn = Constant.canonical c in
  if depth <= 0 then (* don't expand *)
    Node ("Const", [Leaf (string_of_kn kn)])
  else (* expand *)
    let cb = Environ.lookup_constant c env in
    match get_definition cb with
    | None ->
      begin
	match cb.const_type with
	| RegularArity _ -> (* axiom *)
	  Node ("Const", [Leaf (string_of_kn kn)])
	| TemplateArity _ -> assert false
      end
    | Some t ->
      Node ("Const", [build_ast env (depth - 1) t])
and build_fixpoint_functions (env : Environ.env) (depth : int) (names : name array) (typs : constr array) (defs : constr array)  =
  let env_fix = Environ.push_rel_context (bindings_for_fix names typs) env in
  List.map
    (fun i ->
      let def = build_ast env_fix depth (Array.get defs i) in
      build_fix_fun i def)
    (range 0 (Array.length names))
and build_minductive (env : Environ.env) (depth : int) (((i, i_index), _) : pinductive) =
  if depth <= 0 then (* don't expand *)
    let kn = Names.canonical_mind i in
    Node ("MInd", [Leaf (string_of_kn kn); Leaf (string_of_int i_index)])
  else (* expand *)
    let mutind_body = Environ.lookup_mind i env in
    let ind_bodies = mutind_body.mind_packets in
    let ind_bodies_list = Array.to_list ind_bodies in
    let env_ind = Environ.push_rel_context (bindings_for_inductive env mutind_body ind_bodies_list) env in
    let cs = List.map (build_oinductive env_ind depth) ind_bodies_list in
    Node ("MInd", cs)
and build_oinductive (env : Environ.env) (depth : int) (ind_body : one_inductive_body) =
  let constrs =
    List.map (fun (i, (n, typ)) -> Node ("Cons", [Leaf i; Leaf (Names.string_of_id n); build_ast env (depth - 1) typ])) (named_constructors ind_body)
  in
  Node ("Ind", Leaf (Names.string_of_id ind_body.mind_typename) :: constrs)

let rec string_of_ast a =
match a with
| Leaf s -> s
| Node (h, l) ->
  let sl = List.map string_of_ast l in 
  let s = String.concat " " sl in
  Printf.sprintf "(%s %s)" h s

let rec digest_of_ast hash a =
match a with
| Leaf v -> hash v
| Node (v, l) ->
  let ls = v :: List.map (digest_of_ast hash) l in
  hash (String.concat "" ls)

let string_of_gref gref =
  match gref with
  | Globnames.VarRef _ -> ""
  | Globnames.ConstRef cst ->
    Names.string_of_kn (Names.canonical_con cst)
  | Globnames.IndRef (kn,_) ->
    Names.string_of_kn (Names.canonical_mind kn)
  | Globnames.ConstructRef _ -> ""

let locate_mp_dirpath ref =
  let (loc,qid) = Libnames.qualid_of_reference ref in
  try Nametab.dirpath_of_module (Nametab.locate_module qid)
  with Not_found ->
    Errors.user_err_loc (loc, "", str "Unknown module " ++ Libnames.pr_qualid qid)

let get_dirlist_grefs dirlist =
  let selected_gref = ref [] in
  let select gref env constr =
    if Search.module_filter (dirlist, false) gref env constr
    then selected_gref := gref :: !selected_gref
  in
    Search.generic_search None select;
    !selected_gref

let is_prop gref =
  try
    let glob = Glob_term.GRef(Loc.ghost, gref, None) in
    let env = Global.env() in
    let sigma = Evd.from_env env in
    let sigma', c = Pretyping.understand_tcc env sigma glob in
    let sigma2 = Evarconv.consider_remaining_unif_problems env sigma' in
    let sigma3, nf = Evarutil.nf_evars_and_universes sigma2 in
    let pl, uctx = Evd.universe_context sigma3 in
    let env2 = Environ.push_context uctx (Evarutil.nf_env_evar sigma3 env) in
    let c2 = nf c in
    let t = Environ.j_type (Typeops.infer env2 c2) in
    let t2 = Environ.j_type (Typeops.infer env2 t) in
    Term.is_Prop t2
  with _ ->
    begin
      Pp.msg_error (str "unable to determine the type of the type for ref");
      false
    end

let is_opaque gref =
  match gref with
  | Globnames.VarRef _ -> false
  | Globnames.ConstRef cst ->
    let cb = Environ.lookup_constant cst (Global.env ()) in
    (match cb.Declarations.const_body with
    | Declarations.OpaqueDef _ -> true
    | _ -> false)
  | Globnames.IndRef _ | Globnames.ConstructRef _ -> false

let buf = Buffer.create 1000

let formatter out =
  let fmt =
    match out with
    | Some oc -> Pp_control.with_output_to oc
    | None -> Buffer.clear buf; Format.formatter_of_buffer buf
  in
  Format.pp_set_max_boxes fmt max_int;
  fmt

let print_ast fmt gref t =
  let ast = build_ast (Global.env ()) 1 t in
  let s = Printf.sprintf "%s: %s\n" (string_of_gref gref) (string_of_ast ast) in
  pp_with fmt (str s)

let print_ast_type_digest hash fmt gref t_type delim =
  let type_ast = build_ast (Global.env ()) 0 t_type in
  let type_digest = digest_of_ast hash type_ast in
  let s = Printf.sprintf
    "%s { \"name\": \"%s\", \"isProp\": %B, \"isOpaque\": %B, \"typeDigest\": \"%s\" }"
    !delim (string_of_gref gref)  (is_prop gref) (is_opaque gref) type_digest
  in
  pp_with fmt (str s);
  delim := ",\n"

let print_ast_body_digest hash fmt gref t_body delim =
  let body_ast = build_ast (Global.env ()) 1 t_body in
  let body_digest = digest_of_ast hash body_ast in
  let s = Printf.sprintf
    "%s { \"name\": \"%s\", \"isProp\": %B, \"isOpaque\": %B, \"bodyDigest\": \"%s\" }"
    !delim (string_of_gref gref) (is_prop gref) (is_opaque gref) body_digest
  in
  pp_with fmt (str s);
  delim := ",\n"

let print_ast_all_digest hash fmt gref t_type t_body delim =
  let type_ast = build_ast (Global.env ()) 0 t_type in
  let body_ast = build_ast (Global.env ()) 1 t_body in
  let type_digest = digest_of_ast hash type_ast in
  let body_digest = digest_of_ast hash body_ast in
  let s = Printf.sprintf
    "%s { \"name\": \"%s\", \"isProp\": %B, \"isOpaque\": %B, \"typeDigest\": \"%s\", \"bodyDigest\": \"%s\" }"
    !delim (string_of_gref gref) (is_prop gref) (is_opaque gref) type_digest body_digest
  in
  pp_with fmt (str s);
  delim := ",\n"

let print_ast_of_gref fmt gref =
  match gref with
  | Globnames.VarRef _ -> ()
  | Globnames.ConstRef cst ->
    let t = mkConst cst in
    print_ast fmt gref t
  | Globnames.IndRef i ->
    let t = mkInd i in
    print_ast fmt gref t
  | Globnames.ConstructRef _ -> ()

let print_ast_of_gref_type fmt gref =
  match gref with
  | Globnames.ConstRef cst ->
    let cb = Environ.lookup_constant cst (Global.env()) in
    begin match cb.Declarations.const_type with
    | Declarations.RegularArity t ->
      let ast = build_ast (Global.env ()) 0 t in
      let s = Printf.sprintf "%s: %s\n" (string_of_gref gref) (string_of_ast ast) in
      pp_with fmt (str s)
    | Declarations.TemplateArity _ -> ()
    end
  | _ -> ()

let print_digest_of_gref hash fmt gref delim =
  match gref with
  | Globnames.VarRef _ -> ()
  | Globnames.ConstRef cst ->
    let t_body = mkConst cst in
    let cb = Environ.lookup_constant cst (Global.env()) in
    begin match cb.Declarations.const_type with
    | Declarations.RegularArity t_type ->
      print_ast_all_digest hash fmt gref t_type t_body delim
    | Declarations.TemplateArity _ ->
      print_ast_body_digest hash fmt gref t_body delim
    end
  | Globnames.IndRef i ->
    let t_body = mkInd i in
    print_ast_body_digest hash fmt gref t_body delim
  | Globnames.ConstructRef _ -> ()

let print_vio_digest_of_gref hash fmt gref delim =
  match gref with
  | Globnames.VarRef _ -> ()
  | Globnames.ConstRef cst ->
    let t_body = mkConst cst in
    let cb = Environ.lookup_constant cst (Global.env()) in
    begin match cb.Declarations.const_type with
    | Declarations.RegularArity t_type ->
      if is_opaque gref then
	print_ast_type_digest hash fmt gref t_type delim
      else
	print_ast_all_digest hash fmt gref t_type t_body delim
    | Declarations.TemplateArity _ ->
      print_ast_body_digest hash fmt gref t_body delim
    end
  | Globnames.IndRef i ->
    let t_body = mkInd i in
    print_ast_body_digest hash fmt gref t_body delim
  | Globnames.ConstructRef _ -> ()

VERNAC COMMAND EXTEND Ast
| [ "AST" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    List.iter (fun ref -> print_ast_of_gref fmt (Nametab.global ref)) rl;
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "TypeAST" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    List.iter (fun ref -> print_ast_of_gref_type fmt (Nametab.global ref)) rl;
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "AST" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    List.iter (fun ref -> print_ast_of_gref fmt (Nametab.global ref)) rl;
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote AST(s) to file: " ++ str f)
  ]
| [ "TypeAST" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    List.iter (fun ref -> print_ast_of_gref_type fmt (Nametab.global ref)) rl;
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote AST(s) to file: " ++ str f)
  ]
| [ "Digest" "MD5" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun ref -> print_digest_of_gref md5_digest fmt (Nametab.global ref) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "Digest" "ADLER32" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun ref -> print_digest_of_gref adler32_digest fmt (Nametab.global ref) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "Digest" "MD5" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun ref -> print_digest_of_gref md5_digest fmt (Nametab.global ref) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote digest(s) to file: " ++ str f)
  ]
| [ "Digest" "ADLER32" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun ref -> print_digest_of_gref adler32_digest fmt (Nametab.global ref) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote digest(s) to file: " ++ str f)
  ]
| [ "Digest" "VIO" "MD5" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun ref -> print_vio_digest_of_gref md5_digest fmt (Nametab.global ref) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "Digest" "VIO" "ADLER32" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    pp_with fmt (str "[\n");
    List.iter (fun ref -> print_vio_digest_of_gref adler32_digest fmt (Nametab.global ref) delim) rl;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "ModuleAST" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    List.iter (fun gref -> print_ast_of_gref fmt gref) grefs;
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "ModuleAST" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    List.iter (fun gref -> print_ast_of_gref fmt gref) grefs;
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote AST(s) to file: " ++ str f)
  ]
| [ "ModuleDigest" "MD5" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_digest_of_gref md5_digest fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "ModuleDigest" "ADLER32" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_digest_of_gref adler32_digest fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "ModuleDigest" "VIO" "MD5" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_vio_digest_of_gref md5_digest fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "ModuleDigest" "VIO" "ADLER32" reference_list(rl) ] ->
  [
    let fmt = formatter None in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_vio_digest_of_gref adler32_digest fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    if not (Int.equal (Buffer.length buf) 0) then begin
      Pp.msg_notice (str (Buffer.contents buf));
      Buffer.reset buf
    end
  ]
| [ "ModuleDigest" "MD5" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_digest_of_gref md5_digest fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote digest(s) to file: " ++ str f)
  ]
| [ "ModuleDigest" "ADLER32" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_digest_of_gref adler32_digest fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote digest(s) to file: " ++ str f)
  ]
| [ "ModuleDigest" "VIO" "MD5" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_vio_digest_of_gref md5_digest fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote digest(s) to file: " ++ str f)
  ]
| [ "ModuleDigest" "VIO" "ADLER32" string(f) reference_list(rl) ] ->
  [
    let oc = open_out f in
    let fmt = formatter (Some oc) in
    let delim = ref "" in
    let dirlist = List.map locate_mp_dirpath rl in
    let grefs = get_dirlist_grefs dirlist in
    pp_with fmt (str "[\n");
    List.iter (fun gref -> print_vio_digest_of_gref adler32_digest fmt gref delim) grefs;
    pp_with fmt (str "\n]\n");
    Format.pp_print_flush fmt ();
    close_out oc;
    Pp.msg_notice (str "wrote digest(s) to file: " ++ str f)
  ]
END
