open TypeChecker

(* ------------------------------------------------------------------ *)
(* FIR type definitions                                                  *)
(* ------------------------------------------------------------------ *)

type fir_value =
  | FVUnit
  | FVLit of literal
  | FVVar of ident
  | FVClosure of ident * fir_tval list
  | FVStruct of string * (string * fir_tval) list
and fir_tval = { fv : fir_value; ft : ty }

type fir_place =
  | FIPVar of ident
  | FIPDeref of fir_place
  | FIPField of fir_place * string

type fir_instr =
  | FILet     of ident * ty * fir_tval
  | FIReturn  of fir_tval
  | FICall    of ident * ty * ident * fir_tval list
  | FICallValue of ident * ty * fir_tval * fir_tval list
  | FIProject of ident * ty * fir_place * ty
  | FIDrop    of ident * fir_place * ty
  | FIReplace of ident * ty * fir_place * ty * fir_tval
  | FIBorrow  of ident * ref_kind * fir_place * ty
  | FIDeref   of ident * ty * ident * ty
  | FILabel   of string
  | FIGoto    of string
  | FIIf      of fir_tval * string * string

type fir_fn = {
  ff_name   : ident;
  ff_params : param list;
  ff_ret    : ty;
  ff_body   : fir_instr list;
}

(* ------------------------------------------------------------------ *)
(* Conversion engine                                                     *)
(* ------------------------------------------------------------------ *)

type conv_env = {
  env             : global_env;
  fenv            : fn_def list;
  lifetimes       : Big_int_Z.big_int;
  mutable ctx     : ctx;
  mutable counter : int;
  mutable instrs  : fir_instr list;
  mutable moved   : (ident * string list) list;
}

let unit_ty = MkTy (UUnrestricted, TUnits)

let lit_ty = function
  | LInt _   -> MkTy (UUnrestricted, TIntegers)
  | LFloat _ -> MkTy (UUnrestricted, TFloats)
  | LBool _  -> MkTy (UUnrestricted, TBooleans)

let fresh_id env =
  let n = env.counter in
  env.counter <- n + 1;
  ("%t" ^ string_of_int n, Big_int_Z.big_int_of_int 0)

let fresh_label env prefix =
  let n = env.counter in
  env.counter <- n + 1;
  prefix ^ string_of_int n

let emit env i = env.instrs <- i :: env.instrs

let get_var_ty env x =
  match ctx_lookup_b x env.ctx with
  | Some (ty, _) -> ty
  | None -> failwith ("FIR: unbound variable: " ^ fst x)

let rec lower_place = function
  | PVar id -> FIPVar id
  | PDeref place -> FIPDeref (lower_place place)
  | PField (place, field) -> FIPField (lower_place place, field)

let rec infer_place_ty env = function
  | PVar id -> get_var_ty env id
  | PDeref place ->
    begin match ty_core (infer_place_ty env place) with
    | TRef (_, _, inner_ty) -> inner_ty
    | _ -> failwith "FIR: dereference target is not a reference"
    end
  | PField _ as place ->
    begin match infer_place_env env.env env.ctx place with
    | Infer_ok ty -> ty
    | Infer_err _ -> failwith "FIR: field place type inference failed"
    end

let infer_expr_ty env e =
  let result = infer_core_env env.env [] env.lifetimes env.ctx e in
  match result with
  | Infer_ok (ty, _) -> ty
  | Infer_err _ -> unit_ty

let rec place_root_path = function
  | PVar id -> Some (id, [])
  | PField (place, field) ->
    begin match place_root_path place with
    | Some (root, path) -> Some (root, path @ [field])
    | None -> None
    end
  | PDeref _ -> None

let rec path_prefix prefix path =
  match prefix, path with
  | [], _ -> true
  | x :: xs, y :: ys when x = y -> path_prefix xs ys
  | _ -> false

let add_moved_path env place ty =
  if ty_usage ty <> UUnrestricted then
    match place_root_path place with
    | Some (root, (_ :: _ as path)) ->
      env.moved <- (root, path) :: env.moved
    | _ -> ()

let restore_path env place =
  match place_root_path place with
  | Some (root, path) ->
    env.moved <-
      List.filter
        (fun (mroot, moved_path) ->
          mroot <> root || not (path_prefix path moved_path))
        env.moved
  | None -> ()

let path_moved env root path =
  List.exists
    (fun (mroot, moved_path) ->
      mroot = root && path_prefix moved_path path)
    env.moved

let consume_if_needed env x ty =
  if ty_usage ty <> UUnrestricted then
    match ctx_update_state x (state_consume_path []) env.ctx with
    | Some ctx' -> env.ctx <- ctx'
    | None -> ()

let get_fn_ret env f =
  match lookup_fn_b f env.fenv with
  | Some fd -> fd.fn_ret
  | None -> failwith ("FIR: function not found: " ^ fst f)

let get_fn_value_ty env f =
  match lookup_fn_b f env.fenv with
  | Some fd -> fn_value_ty fd
  | None -> failwith ("FIR: function not found: " ^ fst f)

let ident_of_tval env tv =
  match tv.fv with
  | FVVar x -> x
  | FVClosure _ | FVStruct _ ->
    let tmp = fresh_id env in
    emit env (FILet (tmp, tv.ft, tv));
    tmp
  | _ ->
    let tmp = fresh_id env in
    emit env (FILet (tmp, tv.ft, tv));
    tmp

let rec to_value env = function
  | EUnit  -> { fv = FVUnit; ft = unit_ty }
  | ELit l -> { fv = FVLit l; ft = lit_ty l }
  | EVar x ->
    let ty = get_var_ty env x in
    consume_if_needed env x ty;
    { fv = FVVar x; ft = ty }
  | EPlace place ->
    let p_ty = infer_place_ty env place in
    begin match place with
    | PVar id ->
      consume_if_needed env id p_ty;
      { fv = FVVar id; ft = p_ty }
    | _ ->
      let tmp = fresh_id env in
      emit env (FIProject (tmp, p_ty, lower_place place, p_ty));
      add_moved_path env place p_ty;
      { fv = FVVar tmp; ft = p_ty }
    end
  | EFn f ->
    { fv = FVClosure (f, []); ft = get_fn_value_ty env f }
  | ELet (m, x, t, e1, e2) ->
    emit_into env x t e1;
    env.ctx <- ctx_add_b x t m env.ctx;
    to_value env e2
  | ELetInfer (m, x, e1, e2) ->
    let ty1 = infer_expr_ty env e1 in
    emit_into env x ty1 e1;
    env.ctx <- ctx_add_b x ty1 m env.ctx;
    to_value env e2
  | ECall (f, args) ->
    let ret = get_fn_ret env f in
    let flat = List.map (to_value env) args in
    let tmp = fresh_id env in
    emit env (FICall (tmp, ret, f, flat));
    { fv = FVVar tmp; ft = ret }
  | ECallExpr (callee, args) ->
    let callee_val = to_value env callee in
    let result_ty = infer_expr_ty env (ECallExpr (callee, args)) in
    let flat = List.map (to_value env) args in
    let tmp = fresh_id env in
    emit env (FICallValue (tmp, result_ty, callee_val, flat));
    { fv = FVVar tmp; ft = result_ty }
  | EStruct (sname, lts, args, fields) ->
    let struct_def =
      match lookup_struct sname env.env with
      | Some s -> s
      | None -> failwith ("FIR: struct not found: " ^ sname)
    in
    let field_values =
      List.map
        (fun field_def ->
          let field_expr =
            match List.assoc_opt field_def.field_name fields with
            | Some e -> e
            | None -> failwith ("FIR: missing struct field: " ^ field_def.field_name)
          in
          (field_def.field_name, to_value env field_expr))
        struct_def.struct_fields
    in
    { fv = FVStruct (sname, field_values);
      ft = instantiate_struct_instance_ty struct_def lts args }
  | EDrop (EVar x) ->
    let tmp = fresh_id env in
    drop_place env tmp (PVar x);
    { fv = FVVar tmp; ft = unit_ty }
  | EDrop (EPlace place) ->
    let tmp = fresh_id env in
    drop_place env tmp place;
    { fv = FVVar tmp; ft = unit_ty }
  | EDrop inner ->
    let v = to_value env inner in
    let tmp = fresh_id env in
    emit env (FIDrop (tmp, FIPVar (ident_of_tval env v), v.ft));
    { fv = FVVar tmp; ft = unit_ty }
  | EReplace (place, e_new) ->
    let fir_place = lower_place place in
    let p_ty = infer_place_ty env place in
    let v_new = to_value env e_new in
    let tmp = fresh_id env in
    emit env (FIReplace (tmp, p_ty, fir_place, p_ty, v_new));
    restore_path env place;
    { fv = FVVar tmp; ft = p_ty }
  | EAssign (place, e_new) ->
    let fir_place = lower_place place in
    let p_ty = infer_place_ty env place in
    let v_new = to_value env e_new in
    let old_tmp = fresh_id env in
    emit env (FIReplace (old_tmp, p_ty, fir_place, p_ty, v_new));
    let drop_tmp = fresh_id env in
    emit env (FIDrop (drop_tmp, FIPVar old_tmp, p_ty));
    restore_path env place;
    { fv = FVVar drop_tmp; ft = unit_ty }
  | EBorrow (rk, place) ->
    let fir_place = lower_place place in
    let p_ty = infer_place_ty env place in
    let ref_ty = MkTy (UUnrestricted, TRef (LStatic, rk, p_ty)) in
    let tmp = fresh_id env in
    emit env (FIBorrow (tmp, rk, fir_place, p_ty));
    { fv = FVVar tmp; ft = ref_ty }
  | EDeref inner ->
    let v = to_value env inner in
    let inner_ty = match ty_core v.ft with
      | TRef (_, _, t) -> t
      | _ -> failwith "FIR: EDeref requires a reference type"
    in
    let tmp = fresh_id env in
    emit env (FIDeref (tmp, inner_ty, ident_of_tval env v, v.ft));
    { fv = FVVar tmp; ft = inner_ty }
  | EIf (e1, e2, e3) ->
    let result_ty = infer_expr_ty env (EIf (e1, e2, e3)) in
    let cond_val = to_value env e1 in
    let then_lbl = fresh_label env "if_then_" in
    let else_lbl = fresh_label env "if_else_" in
    let end_lbl  = fresh_label env "if_end_"  in
    let result_tmp = fresh_id env in
    let saved_ctx = env.ctx in
    emit env (FIIf (cond_val, then_lbl, else_lbl));
    emit env (FILabel then_lbl);
    let then_val = to_value env e2 in
    emit env (FILet (result_tmp, result_ty, then_val));
    emit env (FIGoto end_lbl);
    env.ctx <- saved_ctx;
    emit env (FILabel else_lbl);
    let else_val = to_value env e3 in
    emit env (FILet (result_tmp, result_ty, else_val));
    emit env (FILabel end_lbl);
    { fv = FVVar result_tmp; ft = result_ty }

and drop_place env result_id place =
  let place_ty = infer_place_ty env place in
  let fir_place = lower_place place in
  let emitted = structural_drop env result_id place fir_place place_ty in
  if not emitted then
    emit env (FILet (result_id, unit_ty, { fv = FVUnit; ft = unit_ty }))

and structural_drop env result_id place fir_place place_ty =
  match place_root_path place with
  | Some (root, path) when path <> [] && path_moved env root path ->
    false
  | _ ->
    begin match ty_core place_ty with
    | TStruct (sname, lts, args) ->
      begin match lookup_struct sname env.env with
      | None ->
        emit env (FIDrop (result_id, fir_place, place_ty));
        add_moved_path env place place_ty;
        true
      | Some struct_def ->
        let emitted_any = ref false in
        let fields = struct_def.struct_fields in
        List.iteri
          (fun idx field_def ->
            let field_place = PField (place, field_def.field_name) in
            let field_fir_place = FIPField (fir_place, field_def.field_name) in
            let field_ty = instantiate_struct_field_ty lts args field_def in
            let drop_id =
              if idx = List.length fields - 1 then result_id else fresh_id env
            in
            if structural_drop env drop_id field_place field_fir_place field_ty then
              emitted_any := true)
          fields;
        !emitted_any
      end
    | _ ->
      emit env (FIDrop (result_id, fir_place, place_ty));
      add_moved_path env place place_ty;
      true
    end

and emit_into env x t = function
  | EUnit | ELit _ | EVar _ as e ->
    emit env (FILet (x, t, to_value env e))
  | EPlace place ->
    emit env (FILet (x, t, to_value env (EPlace place)))
  | ECall (f, args) ->
    let flat = List.map (to_value env) args in
    emit env (FICall (x, t, f, flat))
  | EStruct _ as e ->
    emit env (FILet (x, t, to_value env e))
  | EDrop inner ->
    begin match inner with
    | EVar id -> drop_place env x (PVar id)
    | EPlace place -> drop_place env x place
    | _ ->
      let v = to_value env inner in
      emit env (FIDrop (x, FIPVar (ident_of_tval env v), v.ft))
    end
  | EReplace (place, e_new) ->
    let fir_place = lower_place place in
    let p_ty = infer_place_ty env place in
    let v_new = to_value env e_new in
    emit env (FIReplace (x, p_ty, fir_place, p_ty, v_new));
    restore_path env place
  | EAssign (place, e_new) ->
    let fir_place = lower_place place in
    let p_ty = infer_place_ty env place in
    let v_new = to_value env e_new in
    let old_tmp = fresh_id env in
    emit env (FIReplace (old_tmp, p_ty, fir_place, p_ty, v_new));
    emit env (FIDrop (x, FIPVar old_tmp, p_ty));
    restore_path env place
  | e ->
    let v = to_value env e in
    emit env (FILet (x, t, v))

let params_to_ctx params =
  List.map
    (fun p -> (((p.param_name, p.param_ty), binding_state_of_bool false), p.param_mutability))
    params

let convert_fn global_env fn_def =
  let env = { env = global_env; fenv = global_env.env_fns; lifetimes = fn_def.fn_lifetimes;
              ctx = params_to_ctx fn_def.fn_params;
              counter = 0; instrs = []; moved = [] } in
  let final_val = to_value env fn_def.fn_body in
  emit env (FIReturn final_val);
  { ff_name   = fn_def.fn_name;
    ff_params = fn_def.fn_params;
    ff_ret    = fn_def.fn_ret;
    ff_body   = List.rev env.instrs }

(* ------------------------------------------------------------------ *)
(* Printer                                                               *)
(* ------------------------------------------------------------------ *)

let pp_usage = function
  | ULinear       -> "linear"
  | UAffine       -> "affine"
  | UUnrestricted -> "unrestricted"

let rec pp_ty (MkTy (u, c)) = pp_usage u ^ " " ^ pp_ty_core c
and pp_ty_core = function
  | TUnits    -> "unit"
  | TIntegers -> "isize"
  | TFloats   -> "f64"
  | TBooleans -> "bool"
  | TNamed s  -> s
  | TParam i  -> Printf.sprintf "T%s" (Big_int_Z.string_of_big_int i)
  | TStruct (name, lts, args) ->
    let lt_s = List.map (fun _ -> "'_") lts in
    let arg_s = List.map pp_ty args in
    let all = lt_s @ arg_s in
    if all = [] then name else Printf.sprintf "%s<%s>" name (String.concat ", " all)
  | TFn (ts, r) ->
    "fn(" ^ String.concat ", " (List.map pp_ty ts) ^ ") -> " ^ pp_ty r
  | TForall (n, _, body) ->
    "for<" ^
    String.concat ", "
      (List.init (Big_int_Z.int_of_big_int n)
         (fun i -> "'_" ^ string_of_int i)) ^
    "> " ^ pp_ty body
  | TRef (_, RShared, t) -> "& " ^ pp_ty t
  | TRef (_, RUnique, t) -> "&mut " ^ pp_ty t

let pp_ident (name, idx) =
  if name = "_" then "_"
  else name ^ "#" ^ Big_int_Z.string_of_big_int idx

let rec pp_place = function
  | FIPVar id -> pp_ident id
  | FIPDeref place -> "*" ^ pp_place place
  | FIPField (place, field) -> pp_place place ^ "." ^ field

let rec pp_tval tv =
  let vs = match tv.fv with
    | FVUnit      -> "()"
    | FVLit (LInt n)   -> Big_int_Z.string_of_big_int n
    | FVLit (LFloat f) -> f
    | FVLit (LBool b)  -> string_of_bool b
    | FVVar x     -> pp_ident x
    | FVClosure (f, captured) ->
      let captures =
        match captured with
        | [] -> ""
        | _ ->
          "[" ^ String.concat ", " (List.map pp_tval captured) ^ "]"
      in
      "closure " ^ pp_ident f ^ captures
    | FVStruct (name, fields) ->
      let field_s =
        fields
        |> List.map (fun (field, value) -> field ^ " = " ^ pp_tval value)
        |> String.concat ", "
      in
      name ^ " { " ^ field_s ^ " }"
  in
  vs ^ " as " ^ pp_ty tv.ft

let pp_instr = function
  | FILet (x, t, v) ->
    Printf.sprintf "  let %s as %s = %s" (pp_ident x) (pp_ty t) (pp_tval v)
  | FIReturn v ->
    Printf.sprintf "  return %s" (pp_tval v)
  | FICall (x, t, f, args) ->
    let lhs = if fst x = "_" then "_ as " ^ pp_ty t
              else pp_ident x ^ " as " ^ pp_ty t in
    Printf.sprintf "  call %s = %s (%s)" lhs (pp_ident f)
      (String.concat ", " (List.map pp_tval args))
  | FICallValue (x, t, f, args) ->
    let lhs = if fst x = "_" then "_ as " ^ pp_ty t
              else pp_ident x ^ " as " ^ pp_ty t in
    Printf.sprintf "  call %s = %s (%s)" lhs (pp_tval f)
      (String.concat ", " (List.map pp_tval args))
  | FIProject (r, r_ty, src, src_ty) ->
    Printf.sprintf "  project %s as %s = %s as %s"
      (pp_ident r) (pp_ty r_ty) (pp_place src) (pp_ty src_ty)
  | FIDrop (r, src, src_ty) ->
    Printf.sprintf "  drop %s as unrestricted unit = %s as %s"
      (pp_ident r) (pp_place src) (pp_ty src_ty)
  | FIReplace (r, r_ty, tgt, tgt_ty, v_new) ->
    Printf.sprintf "  replace %s as %s = %s as %s with %s"
      (pp_ident r) (pp_ty r_ty) (pp_place tgt) (pp_ty tgt_ty) (pp_tval v_new)
  | FIBorrow (r, RShared, src, src_ty) ->
    Printf.sprintf "  borrow %s = &%s as %s"
      (pp_ident r) (pp_place src) (pp_ty src_ty)
  | FIBorrow (r, RUnique, src, src_ty) ->
    Printf.sprintf "  borrow %s = &mut %s as %s"
      (pp_ident r) (pp_place src) (pp_ty src_ty)
  | FIDeref (r, r_ty, src, src_ty) ->
    Printf.sprintf "  deref %s as %s = *%s as %s"
      (pp_ident r) (pp_ty r_ty) (pp_ident src) (pp_ty src_ty)
  | FILabel lbl -> Printf.sprintf "%s:" lbl
  | FIGoto  lbl -> Printf.sprintf "  goto %s" lbl
  | FIIf (cond, then_lbl, else_lbl) ->
    Printf.sprintf "  if %s goto %s else %s" (pp_tval cond) then_lbl else_lbl

let pp_param p =
  let mut = if p.param_mutability = MMutable then "mut " else "" in
  Printf.sprintf "%s%s: %s" mut (pp_ident p.param_name) (pp_ty p.param_ty)

let pp_fn ff =
  let params_str = String.concat ", " (List.map pp_param ff.ff_params) in
  let body_str = String.concat "\n" (List.map pp_instr ff.ff_body) in
  Printf.sprintf "fn %s (%s) -> %s {\n%s\n}"
    (pp_ident ff.ff_name) params_str (pp_ty ff.ff_ret) body_str

(* ------------------------------------------------------------------ *)
(* Entry point                                                           *)
(* ------------------------------------------------------------------ *)

let emit_fir filename env =
  let fir_fns = List.map (convert_fn env) env.env_fns in
  let oc = open_out filename in
  List.iter (fun ff ->
    output_string oc (pp_fn ff);
    output_char oc '\n'
  ) fir_fns;
  close_out oc
