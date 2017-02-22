DECLARE PLUGIN "ast_plugin"

(* Plugin to print an AST for a definition.
   Based on TemplateCoq: https://github.com/gmalecha/template-coq/blob/master/src/reify.ml4 *)

(* --- Options --- *)

let opt_debruijn = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optsync = true;
  Goptions.optdepr = false;
  Goptions.optname = "DeBruijn indexing in PrintAST";
  Goptions.optkey = ["PrintAST"; "Indexing"];
  Goptions.optread = (fun () -> !opt_debruijn);
  Goptions.optwrite = (fun b -> opt_debruijn := b);
}

let is_debruijn () = !opt_debruijn

let opt_show_universes = ref (false)
let _ = Goptions.declare_bool_option {
  Goptions.optsync = true;
  Goptions.optdepr = false;
  Goptions.optname = "Show universe instances in PrintAST";
  Goptions.optkey = ["PrintAST"; "Show"; "Universes"];
  Goptions.optread = (fun () -> !opt_show_universes);
  Goptions.optwrite = (fun b -> opt_show_universes := b);
}

let show_universes () = !opt_show_universes

(* --- Helper functions --- *)

let print s = Pp.pp (Pp.str s)

let print_to_string pp trm = Format.asprintf "%a" pp trm

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

let pp_univ_level fmt l = Pp.pp_with fmt (Univ.Level.pr l)

let rec pair_with_number st ls =
  match ls with
    [] -> []
  | l :: ls -> (st, l) :: pair_with_number (st + 1) ls

let wrap str =
  String.concat "" ["(" ; str ; ")"]

let build typ trms =
  wrap (String.concat " " (typ :: trms))

(* --- Names --- *)

let build_name n =
  match n with
    Names.Name id -> build "Name" [Names.string_of_id id]
  | Names.Anonymous -> "(Anonymous)"

(* --- Indexes --- *)

(*
 * The body and type are arbitrary terms.
 * For now we don't recursively print them, but we can if we want to.
 *)
let build_rel_named env i =
  let (name, body, typ) = Environ.lookup_rel i env in
  build "Rel" [build_name name]

(*
 * If De Bruijn mode is on, we show the index.
 * Otherwise, we show the name the index refers to in the environment.
 *)
let build_rel env i =
  if is_debruijn () then
    build "Rel" [string_of_int i]
  else
    build_rel_named env i

(* --- Variables --- *)

let build_var v =
  build "Var" [Names.string_of_id v]

(* --- Universes --- *)

let build_universe_level l =
  build "Level" [print_to_string pp_univ_level l]

let build_universe_levels u =
  match Univ.Universe.level u with
    Some l -> build_universe_level l
  | None -> build "Max" (List.map build_universe_level (Univ.LSet.elements (Univ.Universe.levels u)))

let build_universe u =
  build "Universe" [build_universe_levels u]

(* --- Universe instances --- *)

let build_universe_instance i =
  let ls = Univ.Instance.to_array i in
  build "UnivInstance" (List.map build_universe_level (Array.to_list ls))

(* --- Sorts --- *)

let build_sort s =
  let s_ast =
    match s with
      Term.Prop _ -> if s = Term.prop_sort then "Prop" else "Set"
    | Term.Type u -> build "Type" [build_universe u]
  in build "Sort" [s_ast]

(* --- Casts --- *)

let build_cast_kind k =
  match k with
    Term.VMcast -> "VMcast"
  | Term.DEFAULTcast -> "DEFAULTcast"
  | Term.REVERTcast -> "REVERTcast"
  | Term.NATIVEcast -> "NATIVEcast"

let build_cast (constr, kind, typ) =
  build "Cast" [constr; kind; typ]

(* --- Product types and lambdas --- *)

let build_product (name, typ, body) =
  build "Prod" [name; typ; body]

let build_lambda (name, typ, body) =
  build "Lambda" [name; typ; body]

(* --- Let --- *)

let build_let_in (name, typ, expr, body) =
  build "LetIn" [name; typ; expr; body]

(* --- Application --- *)

let build_app (f, args) =
  build "App" (f :: args)

(* --- Constants --- *)

let build_kername kn =
  Names.string_of_kn kn

let build_axiom kn ty u =
  let kn' = build_kername kn in
  if show_universes () then
    build "pAxiom" [kn'; ty; build_universe_instance u]
  else
    build "pAxiom" [kn'; ty]

let build_pconstr kn ty u =
   let kn' = build_kername kn in
   if show_universes () then
     build "pConstr" [kn'; ty; build_universe_instance u]
   else
     build "pConstr" [kn'; ty]

(* --- Inductive types --- *)

let mutually_inductive_body i env =
  Environ.lookup_mind (fst i) env

let build_inductive_name i env =
  let body = mutually_inductive_body i env in
  let def = Array.get (body.mind_packets) 0 in
  let name_id = def.mind_typename in
  build "Name" [Names.string_of_id name_id]

let build_constructor ((i, c), u) =
  let c' = string_of_int c in
  if show_universes () then
    build "Construct" [i; c'; build_universe_instance u]
  else
    build "Construct" [i; c']

let build_inductive (cs, u) =
  if show_universes () then
    build "Ind" (List.append cs [build_universe_instance u])
  else
    build "Ind" cs

let build_ctor_list =
  fun ls ->
    let ctors = List.map (fun (a, b) -> build a [b]) ls in
    build "inductive_body" ctors

(* --- Pattern matching --- *)

let build_case ((info : Term.case_info), c_a, c_b, branches) =
  let npar = string_of_int info.ci_npar in (* TODO still not sure what npar is *)
  build "Case" (npar :: (c_a :: (c_b :: branches)))

(* --- Unknown type, not yet supported by plugin, but we can pretty-print --- *)

let build_unknown trm =
  build "Unknown" [print_to_string pp_constr trm]

(* --- Full AST --- *)

let rec build_ast env trm depth =
  match Term.kind_of_term trm with
    Term.Rel i ->
      build_rel env i
  | Term.Var v ->
      build_var v
  | Term.Sort s ->
      build_sort s
  | Term.Cast (c, k, t) ->
      let c' = build_ast env c depth in
      let k' = build_cast_kind k in
      let t' = build_ast env t depth in
      build_cast (c', k', t')
  | Term.Prod (n, t, b) ->
      let n' = build_name n in
      let t' = build_ast env t depth in
      let b' = build_ast (Environ.push_rel (n, None, t) env) b depth in
      build_product (n', t', b')
  | Term.Lambda (n, t, b) ->
      let n' = build_name n in
      let t' = build_ast env t depth in
      let b' = build_ast (Environ.push_rel (n, None, t) env) b depth in
      build_lambda (n', t', b')
  | Term.LetIn (n, t, e, b) ->
      let n' = build_name n in
      let t' = build_ast env t depth in
      let e' = build_ast env e depth in
      let b' = build_ast (Environ.push_rel (n, Some e, t) env) b depth in
      build_let_in (n', t', e', b')
  | Term.App (f, xs) ->
      let f' = build_ast env f depth in
      let xs' = List.map (fun x -> build_ast env x depth) (Array.to_list xs) in
      build_app (f', xs')
  | Term.Const (c, u) ->
      build_const env (c, u) depth
  | Term.Construct ((i, c), u) ->
      let i' = build_ast env (Term.mkInd i) depth in
      build_constructor ((i', c), u)
  | Term.Ind (i, u) ->
      build_minductive env (i, u) depth
  | Term.Case (ci, a, b, e) ->
      let c_a = build_ast env a depth in
      let c_b = build_ast env b depth in
      let branches = List.map (fun x -> build_ast env x depth) (Array.to_list e) in
      build_case (ci, c_a, c_b, branches)
  | Term.Fix fp ->
      build_fixpoint env fp depth
  | _ ->
      build_unknown trm

and build_undef (cb : Declarations.constant_body) kn u depth = (* TODO left off here downward *)
  match cb.const_type with
    RegularArity ty -> build_axiom kn (build_ast (Global.env ()) ty depth) u
  | TemplateArity _ -> assert false (* Pre-8.5 universe polymorphism *)

and build_const env (c, u) depth =
  let kn = Names.Constant.canonical c in
  let cb = Environ.lookup_constant c env in
  match cb.const_body with
    Undef _ -> build_undef cb kn u depth
  | Def cs -> build_pconstr kn (build_ast (Global.env ()) (Mod_subst.force_constr cs) depth) u
  | OpaqueDef lc -> build_pconstr kn (build_ast (Global.env ()) (Opaqueproof.force_proof (Global.opaque_tables ()) lc) depth) u

and build_fixpoint env t depth =
  let ((a, b), (ns, ts, ds)) = t in
    let rec seq f t =
      if f < t then
        f :: seq (f + 1) t
      else
        []
      in
      let ctxt = CArray.map2_i (fun i na t -> (na, None, Vars.lift i t)) ns ts in
      let envfix = Environ.push_rel_context (Array.to_list ctxt) env in
      let mk_fun xs i =
	let n = string_of_int i in
	let nm = build_name (Array.get ns i) in
	let ty = build_ast env (Array.get ts i) depth in
	let ds = build_ast envfix (Array.get ds i) depth in
	(build "mkdef" ["term"; nm; ty; ds; n]) :: xs
      in
      let defs = List.fold_left mk_fun [] (seq 0 (Array.length a)) in
      build "Fix" [build "def" ("term" :: (List.rev defs)); string_of_int b]

and build_minductive env (i, u) depth =
  if depth = 0 then (* don't expand *)
    build_inductive_name i env
  else (* expand *)
    let mib = mutually_inductive_body i env in
    let inst = Univ.UContext.instance mib.Declarations.mind_universes in
    let indtys =
      Array.to_list Declarations.(Array.map (fun oib ->
        let ty = Inductive.type_of_inductive env ((mib, oib), inst) in
        (Names.Name oib.mind_typename, None, ty)) mib.mind_packets)
    in
    let envind = Environ.push_rel_context indtys env in
    let ls =
      List.fold_left (fun ls oib -> (* One inductive body *)
        let named_ctors =
	  List.combine
	    Declarations.(Array.to_list oib.mind_consnames)
	    Declarations.(Array.to_list oib.mind_user_lc)
	in
	let ctor_asts =
	  List.fold_left (fun ls (nm, ty) ->
	    let ty = build_ast envind ty (depth - 1) in
	    (Names.string_of_id nm, ty) :: ls)
	  [] named_ctors
	in
	  Declarations.((build "Name" [Names.string_of_id oib.mind_typename]),
	    build_ctor_list (List.rev ctor_asts)) :: ls)
	  [] (Array.to_list mib.mind_packets) (* Array of one inductive bodies *)
    in
    let cs = List.map (fun (a, b) -> build a [b]) (List.rev ls) in
    build_inductive (cs, u)

let print_ast def depth =
  let (evm, env) = Lemmas.get_current_context() in
  let (body, _) = Constrintern.interp_constr env evm def in
  print (build_ast env body depth)

(* PrintAST command
   The depth specifies the depth at which to unroll nested inductive types *)
VERNAC COMMAND EXTEND Print_AST
| [ "PrintAST" constr(def) ] ->
  [ print_ast def 1 ]
| [ "PrintAST" constr(def) "with" "depth" string(depth)] ->
  [ print_ast def (int_of_string depth) ]
END

