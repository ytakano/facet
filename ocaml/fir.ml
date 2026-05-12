open TypeChecker

(* ------------------------------------------------------------------ *)
(* FIR type definitions                                                  *)
(* ------------------------------------------------------------------ *)

type fir_value =
  | FVUnit
  | FVLit of literal
  | FVVar of ident

type fir_tval = { fv : fir_value; ft : ty }

type fir_instr =
  | FILet     of ident * ty * fir_tval
  | FIReturn  of fir_tval
  | FICall    of ident * ty * ident * fir_tval list
  | FIDrop    of ident * ident * ty
  | FIReplace of ident * ty * ident * ty * fir_tval
  | FIBorrow  of ident * ref_kind * ident * ty
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
  fenv            : fn_def list;
  lifetimes       : Big_int_Z.big_int;
  mutable ctx     : ctx;
  mutable counter : int;
  mutable instrs  : fir_instr list;
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

let consume_if_needed env x ty =
  if ty_usage ty <> UUnrestricted then
    match ctx_consume_b x env.ctx with
    | Some ctx' -> env.ctx <- ctx'
    | None -> ()

let get_fn_ret env f =
  match lookup_fn_b f env.fenv with
  | Some fd -> fd.fn_ret
  | None -> failwith ("FIR: function not found: " ^ fst f)

let ident_of_tval env tv =
  match tv.fv with
  | FVVar x -> x
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
  | ELet (m, x, t, e1, e2) ->
    emit_into env x t e1;
    env.ctx <- ctx_add_b x t m env.ctx;
    to_value env e2
  | ELetInfer (m, x, e1, e2) ->
    let ty1 = match infer_core env.fenv env.lifetimes env.ctx e1 with
      | Infer_ok (t, _) -> t
      | Infer_err _ -> unit_ty
    in
    emit_into env x ty1 e1;
    env.ctx <- ctx_add_b x ty1 m env.ctx;
    to_value env e2
  | ECall (f, args) ->
    let ret = get_fn_ret env f in
    let flat = List.map (to_value env) args in
    let tmp = fresh_id env in
    emit env (FICall (tmp, ret, f, flat));
    { fv = FVVar tmp; ft = ret }
  | EDrop inner ->
    let v = to_value env inner in
    let tmp = fresh_id env in
    emit env (FIDrop (tmp, ident_of_tval env v, v.ft));
    { fv = FVVar tmp; ft = unit_ty }
  | EReplace (place, e_new) ->
    let id = place_name place in
    let p_ty = get_var_ty env id in
    let v_new = to_value env e_new in
    let tmp = fresh_id env in
    emit env (FIReplace (tmp, p_ty, id, p_ty, v_new));
    { fv = FVVar tmp; ft = p_ty }
  | EAssign (place, e_new) ->
    let id = place_name place in
    let p_ty = get_var_ty env id in
    let v_new = to_value env e_new in
    let old_tmp = fresh_id env in
    emit env (FIReplace (old_tmp, p_ty, id, p_ty, v_new));
    let drop_tmp = fresh_id env in
    emit env (FIDrop (drop_tmp, old_tmp, p_ty));
    { fv = FVVar drop_tmp; ft = unit_ty }
  | EBorrow (rk, place) ->
    let id = place_name place in
    let p_ty = get_var_ty env id in
    let ref_ty = MkTy (UUnrestricted, TRef (LStatic, rk, p_ty)) in
    let tmp = fresh_id env in
    emit env (FIBorrow (tmp, rk, id, p_ty));
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
    let result_ty = match infer_core env.fenv env.lifetimes env.ctx (EIf (e1, e2, e3)) with
      | Infer_ok (t, _) -> t
      | Infer_err _ -> unit_ty
    in
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

and emit_into env x t = function
  | EUnit | ELit _ | EVar _ as e ->
    emit env (FILet (x, t, to_value env e))
  | ECall (f, args) ->
    let flat = List.map (to_value env) args in
    emit env (FICall (x, t, f, flat))
  | EDrop inner ->
    let v = to_value env inner in
    emit env (FIDrop (x, ident_of_tval env v, v.ft))
  | EReplace (place, e_new) ->
    let id = place_name place in
    let p_ty = get_var_ty env id in
    let v_new = to_value env e_new in
    emit env (FIReplace (x, p_ty, id, p_ty, v_new))
  | EAssign (place, e_new) ->
    let id = place_name place in
    let p_ty = get_var_ty env id in
    let v_new = to_value env e_new in
    let old_tmp = fresh_id env in
    emit env (FIReplace (old_tmp, p_ty, id, p_ty, v_new));
    emit env (FIDrop (x, old_tmp, p_ty))
  | e ->
    let v = to_value env e in
    emit env (FILet (x, t, v))

let params_to_ctx params =
  List.map (fun p -> (((p.param_name, p.param_ty), false), p.param_mutability)) params

let convert_fn fenv fn_def =
  let env = { fenv; lifetimes = fn_def.fn_lifetimes;
              ctx = params_to_ctx fn_def.fn_params;
              counter = 0; instrs = [] } in
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
  | TFn (ts, r) ->
    "fn(" ^ String.concat ", " (List.map pp_ty ts) ^ ") -> " ^ pp_ty r
  | TRef (_, RShared, t) -> "& " ^ pp_ty t
  | TRef (_, RUnique, t) -> "&mut " ^ pp_ty t

let pp_ident (name, idx) =
  if name = "_" then "_"
  else name ^ "#" ^ Big_int_Z.string_of_big_int idx

let pp_tval tv =
  let vs = match tv.fv with
    | FVUnit      -> "()"
    | FVLit (LInt n)   -> Big_int_Z.string_of_big_int n
    | FVLit (LFloat f) -> f
    | FVLit (LBool b)  -> string_of_bool b
    | FVVar x     -> pp_ident x
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
  | FIDrop (r, src, src_ty) ->
    Printf.sprintf "  drop %s as unrestricted unit = %s as %s"
      (pp_ident r) (pp_ident src) (pp_ty src_ty)
  | FIReplace (r, r_ty, tgt, tgt_ty, v_new) ->
    Printf.sprintf "  replace %s as %s = %s as %s with %s"
      (pp_ident r) (pp_ty r_ty) (pp_ident tgt) (pp_ty tgt_ty) (pp_tval v_new)
  | FIBorrow (r, RShared, src, src_ty) ->
    Printf.sprintf "  borrow %s = &%s as %s"
      (pp_ident r) (pp_ident src) (pp_ty src_ty)
  | FIBorrow (r, RUnique, src, src_ty) ->
    Printf.sprintf "  borrow %s = &mut %s as %s"
      (pp_ident r) (pp_ident src) (pp_ty src_ty)
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

let emit_fir filename fn_defs =
  let fir_fns = List.map (convert_fn fn_defs) fn_defs in
  let oc = open_out filename in
  List.iter (fun ff ->
    output_string oc (pp_fn ff);
    output_char oc '\n'
  ) fir_fns;
  close_out oc
