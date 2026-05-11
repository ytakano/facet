
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

type mutability =
| MImmutable
| MMutable

type usage =
| ULinear
| UAffine
| UUnrestricted

type ref_kind =
| RShared
| RUnique

type 'a typeCore =
| TUnits
| TIntegers
| TFloats
| TNamed of string
| TFn of 'a list * 'a
| TRef of ref_kind * 'a

type ty =
| MkTy of usage * ty typeCore

(** val ty_usage : ty -> usage **)

let ty_usage = function
| MkTy (u, _) -> u

(** val ty_core : ty -> ty typeCore **)

let ty_core = function
| MkTy (_, c) -> c

type ident = (string, nat) prod

(** val ident_eqb : ident -> ident -> bool **)

let ident_eqb x y =
  match eqb1 (fst x) (fst y) with
  | True -> Nat.eqb (snd x) (snd y)
  | False -> False

type literal =
| LInt of z
| LFloat of string

type place = ident
  (* singleton inductive, whose constructor was PVar *)

type expr =
| EUnit
| ELit of literal
| EVar of ident
| ELet of mutability * ident * ty * expr * expr
| ELetInfer of mutability * ident * expr * expr
| ECall of ident * expr list
| EReplace of place * expr
| EDrop of expr

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type fn_def = { fn_name : ident; fn_params : param list; fn_ret : ty;
                fn_body : expr }

type syntax = fn_def list

type ctx_entry = ((ident, ty) prod, bool) prod

type ctx = ctx_entry list

(** val usage_eqb : usage -> usage -> bool **)

let usage_eqb u1 u2 =
  match u1 with
  | ULinear -> (match u2 with
                | ULinear -> True
                | _ -> False)
  | UAffine -> (match u2 with
                | UAffine -> True
                | _ -> False)
  | UUnrestricted -> (match u2 with
                      | UUnrestricted -> True
                      | _ -> False)

(** val usage_sub_bool : usage -> usage -> bool **)

let usage_sub_bool u1 u2 =
  match u1 with
  | ULinear -> (match u2 with
                | ULinear -> True
                | _ -> False)
  | UAffine -> (match u2 with
                | UUnrestricted -> False
                | _ -> True)
  | UUnrestricted -> True

(** val ty_core_eqb : ty typeCore -> ty typeCore -> bool **)

let ty_core_eqb c1 c2 =
  match c1 with
  | TUnits -> (match c2 with
               | TUnits -> True
               | _ -> False)
  | TIntegers -> (match c2 with
                  | TIntegers -> True
                  | _ -> False)
  | TFloats -> (match c2 with
                | TFloats -> True
                | _ -> False)
  | TNamed s1 -> (match c2 with
                  | TNamed s2 -> eqb1 s1 s2
                  | _ -> False)
  | _ -> False

(** val ctx_lookup_b : ident -> ctx -> (ty, bool) prod option **)

let rec ctx_lookup_b x = function
| Nil -> None
| Cons (c, t) ->
  let Pair (p, b) = c in
  let Pair (n, t0) = p in
  (match ident_eqb x n with
   | True -> Some (Pair (t0, b))
   | False -> ctx_lookup_b x t)

(** val ctx_consume_b : ident -> ctx -> ctx option **)

let rec ctx_consume_b x = function
| Nil -> None
| Cons (c, t) ->
  let Pair (p, b) = c in
  let Pair (n, t0) = p in
  (match ident_eqb x n with
   | True -> Some (Cons ((Pair ((Pair (n, t0)), True)), t))
   | False ->
     (match ctx_consume_b x t with
      | Some t' -> Some (Cons ((Pair ((Pair (n, t0)), b)), t'))
      | None -> None))

(** val ctx_add_b : ident -> ty -> ctx -> ctx **)

let ctx_add_b x t _UU0393_ =
  Cons ((Pair ((Pair (x, t)), False)), _UU0393_)

(** val ctx_remove_b : ident -> ctx -> ctx **)

let rec ctx_remove_b x = function
| Nil -> Nil
| Cons (c, t) ->
  let Pair (p, b) = c in
  let Pair (n, t0) = p in
  (match ident_eqb x n with
   | True -> t
   | False -> Cons ((Pair ((Pair (n, t0)), b)), (ctx_remove_b x t)))

(** val ctx_check_ok : ident -> ty -> ctx -> bool **)

let ctx_check_ok x t _UU0393_ =
  match ty_usage t with
  | ULinear ->
    (match ctx_lookup_b x _UU0393_ with
     | Some p -> let Pair (_, b) = p in b
     | None -> False)
  | _ -> True

(** val lookup_fn_b : ident -> fn_def list -> fn_def option **)

let rec lookup_fn_b name = function
| Nil -> None
| Cons (f, t) ->
  (match ident_eqb name f.fn_name with
   | True -> Some f
   | False -> lookup_fn_b name t)

type rename_env = (ident, ident) prod list

(** val lookup_rename : ident -> rename_env -> ident **)

let rec lookup_rename x = function
| Nil -> x
| Cons (p, _UU03c1_') ->
  let Pair (old, fresh) = p in
  (match ident_eqb x old with
   | True -> fresh
   | False -> lookup_rename x _UU03c1_')

(** val max_ident_index : string -> ident list -> nat **)

let rec max_ident_index base = function
| Nil -> O
| Cons (i, used') ->
  let Pair (base0, n) = i in
  (match eqb1 base base0 with
   | True -> Nat.max n (max_ident_index base used')
   | False -> max_ident_index base used')

(** val fresh_ident : ident -> ident list -> ident **)

let fresh_ident x used =
  Pair ((fst x), (S (max_ident_index (fst x) used)))

(** val ctx_names : ctx -> ident list **)

let rec ctx_names = function
| Nil -> Nil
| Cons (c, _UU0393_') ->
  let Pair (p, _) = c in
  let Pair (x, _) = p in Cons (x, (ctx_names _UU0393_'))

(** val place_name : place -> ident **)

let place_name p =
  p

type infer_error =
| ErrUnknownVar of ident
| ErrAlreadyConsumed of ident
| ErrTypeMismatch of ty typeCore * ty typeCore
| ErrUsageMismatch of usage * usage
| ErrFunctionNotFound of ident
| ErrArityMismatch
| ErrContextCheckFailed
| ErrNotImplemented

type 'a infer_result =
| Infer_ok of 'a
| Infer_err of infer_error

(** val free_vars_expr : expr -> ident list **)

let rec free_vars_expr = function
| EVar x -> Cons (x, Nil)
| ELet (_, x, _, e1, e2) ->
  Cons (x, (app (free_vars_expr e1) (free_vars_expr e2)))
| ELetInfer (_, x, e1, e2) ->
  Cons (x, (app (free_vars_expr e1) (free_vars_expr e2)))
| ECall (_, args) ->
  let rec go = function
  | Nil -> Nil
  | Cons (arg, rest) -> app (free_vars_expr arg) (go rest)
  in go args
| EReplace (p, e_new) -> Cons ((place_name p), (free_vars_expr e_new))
| EDrop e1 -> free_vars_expr e1
| _ -> Nil

(** val param_names : param list -> ident list **)

let rec param_names = function
| Nil -> Nil
| Cons (p, ps') -> Cons (p.param_name, (param_names ps'))

(** val rename_place : rename_env -> place -> place **)

let rename_place _UU03c1_ p =
  lookup_rename p _UU03c1_

(** val alpha_rename_expr :
    rename_env -> ident list -> expr -> (expr, ident list) prod **)

let rec alpha_rename_expr _UU03c1_ used = function
| EVar x -> Pair ((EVar (lookup_rename x _UU03c1_)), used)
| ELet (m, x, t, e1, e2) ->
  let Pair (e1', used1) = alpha_rename_expr _UU03c1_ used e1 in
  let used1' = Cons (x, (app (free_vars_expr e2) used1)) in
  let x' = fresh_ident x used1' in
  let used2 = Cons (x', used1') in
  let Pair (e2', used3) =
    alpha_rename_expr (Cons ((Pair (x, x')), _UU03c1_)) used2 e2
  in
  Pair ((ELet (m, x', t, e1', e2')), used3)
| ELetInfer (m, x, e1, e2) ->
  let Pair (e1', used1) = alpha_rename_expr _UU03c1_ used e1 in
  let used1' = Cons (x, (app (free_vars_expr e2) used1)) in
  let x' = fresh_ident x used1' in
  let used2 = Cons (x', used1') in
  let Pair (e2', used3) =
    alpha_rename_expr (Cons ((Pair (x, x')), _UU03c1_)) used2 e2
  in
  Pair ((ELetInfer (m, x', e1', e2')), used3)
| ECall (fname, args) ->
  let go =
    let rec go used0 = function
    | Nil -> Pair (Nil, used0)
    | Cons (arg, rest) ->
      let Pair (arg', used1) = alpha_rename_expr _UU03c1_ used0 arg in
      let Pair (rest', used2) = go used1 rest in
      Pair ((Cons (arg', rest')), used2)
    in go
  in
  let Pair (args', used') = go used args in
  Pair ((ECall (fname, args')), used')
| EReplace (p, e_new) ->
  let Pair (e_new', used') = alpha_rename_expr _UU03c1_ used e_new in
  Pair ((EReplace ((rename_place _UU03c1_ p), e_new')), used')
| EDrop e1 ->
  let Pair (e1', used') = alpha_rename_expr _UU03c1_ used e1 in
  Pair ((EDrop e1'), used')
| x -> Pair (x, used)

(** val alpha_rename_params :
    rename_env -> ident list -> param list -> ((param list, rename_env) prod,
    ident list) prod **)

let rec alpha_rename_params _UU03c1_ used = function
| Nil -> Pair ((Pair (Nil, _UU03c1_)), used)
| Cons (p, ps') ->
  let x = p.param_name in
  let x' = fresh_ident x used in
  let p' = { param_mutability = p.param_mutability; param_name = x';
    param_ty = p.param_ty }
  in
  let Pair (p0, used') =
    alpha_rename_params (Cons ((Pair (x, x')), _UU03c1_)) (Cons (x', used))
      ps'
  in
  let Pair (ps'', _UU03c1_') = p0 in
  Pair ((Pair ((Cons (p', ps'')), _UU03c1_')), used')

(** val alpha_rename_fn_def :
    ident list -> fn_def -> (fn_def, ident list) prod **)

let alpha_rename_fn_def used f =
  let used0 =
    app (param_names f.fn_params) (app (free_vars_expr f.fn_body) used)
  in
  let Pair (p, used1) = alpha_rename_params Nil used0 f.fn_params in
  let Pair (params', _UU03c1_) = p in
  let Pair (body', used2) = alpha_rename_expr _UU03c1_ used1 f.fn_body in
  Pair ({ fn_name = f.fn_name; fn_params = params'; fn_ret = f.fn_ret;
  fn_body = body' }, used2)

(** val alpha_rename_syntax_go :
    ident list -> syntax -> (syntax, ident list) prod **)

let rec alpha_rename_syntax_go used = function
| Nil -> Pair (Nil, used)
| Cons (f, fs) ->
  let Pair (f', used1) = alpha_rename_fn_def used f in
  let Pair (fs', used2) = alpha_rename_syntax_go used1 fs in
  Pair ((Cons (f', fs')), used2)

(** val alpha_rename_for_infer :
    ctx -> fn_def list -> expr -> (fn_def list, expr) prod **)

let alpha_rename_for_infer _UU0393_ fenv e =
  let Pair (fenv', used) =
    alpha_rename_syntax_go (app (free_vars_expr e) (ctx_names _UU0393_)) fenv
  in
  let Pair (e', _) = alpha_rename_expr Nil used e in Pair (fenv', e')

(** val infer_core :
    fn_def list -> ctx -> expr -> (ty, ctx) prod infer_result **)

let rec infer_core fenv _UU0393_ = function
| EUnit -> Infer_ok (Pair ((MkTy (UUnrestricted, TUnits)), _UU0393_))
| ELit l ->
  (match l with
   | LInt _ -> Infer_ok (Pair ((MkTy (UUnrestricted, TIntegers)), _UU0393_))
   | LFloat _ -> Infer_ok (Pair ((MkTy (UUnrestricted, TFloats)), _UU0393_)))
| EVar x ->
  (match ctx_lookup_b x _UU0393_ with
   | Some p ->
     let Pair (t, b) = p in
     (match usage_eqb (ty_usage t) UUnrestricted with
      | True -> Infer_ok (Pair (t, _UU0393_))
      | False ->
        (match b with
         | True -> Infer_err (ErrAlreadyConsumed x)
         | False ->
           (match ctx_consume_b x _UU0393_ with
            | Some _UU0393_' -> Infer_ok (Pair (t, _UU0393_'))
            | None -> Infer_err (ErrUnknownVar x))))
   | None -> Infer_err (ErrUnknownVar x))
| ELet (_, x, t, e1, e2) ->
  (match infer_core fenv _UU0393_ e1 with
   | Infer_ok p ->
     let Pair (t1, _UU0393_1) = p in
     (match ty_core_eqb (ty_core t1) (ty_core t) with
      | True ->
        (match usage_sub_bool (ty_usage t1) (ty_usage t) with
         | True ->
           (match infer_core fenv (ctx_add_b x t _UU0393_1) e2 with
            | Infer_ok p0 ->
              let Pair (t2, _UU0393_2) = p0 in
              (match ctx_check_ok x t _UU0393_2 with
               | True -> Infer_ok (Pair (t2, (ctx_remove_b x _UU0393_2)))
               | False -> Infer_err ErrContextCheckFailed)
            | Infer_err err -> Infer_err err)
         | False -> Infer_err (ErrUsageMismatch ((ty_usage t1), (ty_usage t))))
      | False -> Infer_err (ErrTypeMismatch ((ty_core t1), (ty_core t))))
   | Infer_err err -> Infer_err err)
| ELetInfer (_, _, _, _) -> Infer_err ErrNotImplemented
| ECall (fname, args) ->
  (match lookup_fn_b fname fenv with
   | Some fdef ->
     let go =
       let rec go _UU0393_0 as_ ps =
         match as_ with
         | Nil ->
           (match ps with
            | Nil -> Infer_ok _UU0393_0
            | Cons (_, _) -> Infer_err ErrArityMismatch)
         | Cons (e', es) ->
           (match ps with
            | Nil -> Infer_err ErrArityMismatch
            | Cons (p, ps') ->
              (match infer_core fenv _UU0393_0 e' with
               | Infer_ok p0 ->
                 let Pair (t_e, _UU0393_1) = p0 in
                 (match ty_core_eqb (ty_core t_e) (ty_core p.param_ty) with
                  | True ->
                    (match usage_sub_bool (ty_usage t_e) (ty_usage p.param_ty) with
                     | True -> go _UU0393_1 es ps'
                     | False ->
                       Infer_err (ErrUsageMismatch ((ty_usage t_e),
                         (ty_usage p.param_ty))))
                  | False ->
                    Infer_err (ErrTypeMismatch ((ty_core t_e),
                      (ty_core p.param_ty))))
               | Infer_err err -> Infer_err err))
       in go
     in
     (match go _UU0393_ args fdef.fn_params with
      | Infer_ok _UU0393_' -> Infer_ok (Pair (fdef.fn_ret, _UU0393_'))
      | Infer_err err -> Infer_err err)
   | None -> Infer_err (ErrFunctionNotFound fname))
| EReplace (p, e_new) ->
  (match ctx_lookup_b p _UU0393_ with
   | Some p0 ->
     let Pair (t_x, b) = p0 in
     (match b with
      | True -> Infer_err (ErrAlreadyConsumed p)
      | False ->
        (match infer_core fenv _UU0393_ e_new with
         | Infer_ok p1 ->
           let Pair (t_new, _UU0393_') = p1 in
           (match ty_core_eqb (ty_core t_new) (ty_core t_x) with
            | True ->
              (match usage_sub_bool (ty_usage t_new) (ty_usage t_x) with
               | True -> Infer_ok (Pair (t_x, _UU0393_'))
               | False ->
                 Infer_err (ErrUsageMismatch ((ty_usage t_new),
                   (ty_usage t_x))))
            | False ->
              Infer_err (ErrTypeMismatch ((ty_core t_new), (ty_core t_x))))
         | Infer_err err -> Infer_err err))
   | None -> Infer_err (ErrUnknownVar p))
| EDrop e1 ->
  (match infer_core fenv _UU0393_ e1 with
   | Infer_ok p ->
     let Pair (_, _UU0393_') = p in
     Infer_ok (Pair ((MkTy (UUnrestricted, TUnits)), _UU0393_'))
   | Infer_err err -> Infer_err err)

(** val infer : fn_def list -> ctx -> expr -> (ty, ctx) prod infer_result **)

let infer fenv _UU0393_ e =
  let Pair (fenv', e') = alpha_rename_for_infer _UU0393_ fenv e in
  infer_core fenv' _UU0393_ e'
