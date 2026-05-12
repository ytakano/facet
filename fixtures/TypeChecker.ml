
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eqb = Big_int_Z.eq_big_int

  (** val max :
      Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

  let rec max n m =
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
        (fun _ -> n)
        (fun m' -> Big_int_Z.succ_big_int (max n' m'))
        m)
      n
 end

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

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
| TBooleans
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

type ident = string * Big_int_Z.big_int

(** val ident_eqb : ident -> ident -> bool **)

let ident_eqb x y =
  (&&) ((=) (fst x) (fst y)) (Nat.eqb (snd x) (snd y))

type literal =
| LInt of Big_int_Z.big_int
| LFloat of string
| LBool of bool

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
| EIf of expr * expr * expr

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type fn_def = { fn_name : ident; fn_params : param list; fn_ret : ty;
                fn_body : expr }

type syntax = fn_def list

type ctx_entry = (ident * ty) * bool

type ctx = ctx_entry list

(** val param_ctx_entry : param -> ctx_entry **)

let param_ctx_entry p =
  ((p.param_name, p.param_ty), false)

(** val params_ctx : param list -> ctx **)

let rec params_ctx = function
| [] -> []
| p :: ps' -> (param_ctx_entry p) :: (params_ctx ps')

(** val usage_max : usage -> usage -> usage **)

let usage_max u1 u2 =
  match u1 with
  | ULinear -> ULinear
  | UAffine -> (match u2 with
                | ULinear -> ULinear
                | _ -> UAffine)
  | UUnrestricted -> u2

(** val ctx_merge : ctx -> ctx -> ctx option **)

let rec ctx_merge _UU0393_2 _UU0393_3 =
  match _UU0393_2 with
  | [] -> (match _UU0393_3 with
           | [] -> Some []
           | _ :: _ -> None)
  | c :: t2 ->
    let (p, b2) = c in
    let (n, t) = p in
    (match _UU0393_3 with
     | [] -> None
     | c0 :: t3 ->
       let (p0, b3) = c0 in
       let (n', _) = p0 in
       if negb (ident_eqb n n')
       then None
       else (match ctx_merge t2 t3 with
             | Some rest ->
               (match ty_usage t with
                | ULinear ->
                  if eqb b2 b3 then Some (((n, t), b2) :: rest) else None
                | _ -> Some (((n, t), ((||) b2 b3)) :: rest))
             | None -> None))

(** val usage_eqb : usage -> usage -> bool **)

let usage_eqb u1 u2 =
  match u1 with
  | ULinear -> (match u2 with
                | ULinear -> true
                | _ -> false)
  | UAffine -> (match u2 with
                | UAffine -> true
                | _ -> false)
  | UUnrestricted -> (match u2 with
                      | UUnrestricted -> true
                      | _ -> false)

(** val usage_sub_bool : usage -> usage -> bool **)

let usage_sub_bool u1 u2 =
  match u1 with
  | ULinear -> (match u2 with
                | ULinear -> true
                | _ -> false)
  | UAffine -> (match u2 with
                | UUnrestricted -> false
                | _ -> true)
  | UUnrestricted -> true

(** val ty_core_eqb : ty typeCore -> ty typeCore -> bool **)

let ty_core_eqb c1 c2 =
  match c1 with
  | TUnits -> (match c2 with
               | TUnits -> true
               | _ -> false)
  | TIntegers -> (match c2 with
                  | TIntegers -> true
                  | _ -> false)
  | TFloats -> (match c2 with
                | TFloats -> true
                | _ -> false)
  | TBooleans -> (match c2 with
                  | TBooleans -> true
                  | _ -> false)
  | TNamed s1 -> (match c2 with
                  | TNamed s2 -> (=) s1 s2
                  | _ -> false)
  | _ -> false

(** val ctx_lookup_b : ident -> ctx -> (ty * bool) option **)

let rec ctx_lookup_b x = function
| [] -> None
| c :: t ->
  let (p, b) = c in
  let (n, t0) = p in if ident_eqb x n then Some (t0, b) else ctx_lookup_b x t

(** val ctx_consume_b : ident -> ctx -> ctx option **)

let rec ctx_consume_b x = function
| [] -> None
| c :: t ->
  let (p, b) = c in
  let (n, t0) = p in
  if ident_eqb x n
  then Some (((n, t0), true) :: t)
  else (match ctx_consume_b x t with
        | Some t' -> Some (((n, t0), b) :: t')
        | None -> None)

(** val ctx_add_b : ident -> ty -> ctx -> ctx **)

let ctx_add_b x t _UU0393_ =
  ((x, t), false) :: _UU0393_

(** val ctx_remove_b : ident -> ctx -> ctx **)

let rec ctx_remove_b x = function
| [] -> []
| c :: t ->
  let (p, b) = c in
  let (n, t0) = p in
  if ident_eqb x n then t else ((n, t0), b) :: (ctx_remove_b x t)

(** val ctx_check_ok : ident -> ty -> ctx -> bool **)

let ctx_check_ok x t _UU0393_ =
  match ty_usage t with
  | ULinear ->
    (match ctx_lookup_b x _UU0393_ with
     | Some p -> let (_, b) = p in b
     | None -> false)
  | _ -> true

(** val lookup_fn_b : ident -> fn_def list -> fn_def option **)

let rec lookup_fn_b name = function
| [] -> None
| f :: t -> if ident_eqb name f.fn_name then Some f else lookup_fn_b name t

type rename_env = (ident * ident) list

(** val lookup_rename : ident -> rename_env -> ident **)

let rec lookup_rename x = function
| [] -> x
| p :: _UU03c1_' ->
  let (old, fresh) = p in
  if ident_eqb x old then fresh else lookup_rename x _UU03c1_'

(** val max_ident_index : string -> ident list -> Big_int_Z.big_int **)

let rec max_ident_index base = function
| [] -> Big_int_Z.zero_big_int
| i :: used' ->
  let (base0, n) = i in
  if (=) base base0
  then Nat.max n (max_ident_index base used')
  else max_ident_index base used'

(** val fresh_ident : ident -> ident list -> ident **)

let fresh_ident x used =
  ((fst x), (Big_int_Z.succ_big_int (max_ident_index (fst x) used)))

(** val ctx_names : ctx -> ident list **)

let rec ctx_names = function
| [] -> []
| c :: _UU0393_' ->
  let (p, _) = c in let (x, _) = p in x :: (ctx_names _UU0393_')

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
| EVar x -> x :: []
| ELet (_, x, _, e1, e2) -> x :: (app (free_vars_expr e1) (free_vars_expr e2))
| ELetInfer (_, x, e1, e2) ->
  x :: (app (free_vars_expr e1) (free_vars_expr e2))
| ECall (_, args) ->
  let rec go = function
  | [] -> []
  | arg :: rest -> app (free_vars_expr arg) (go rest)
  in go args
| EReplace (p, e_new) -> (place_name p) :: (free_vars_expr e_new)
| EDrop e1 -> free_vars_expr e1
| EIf (e1, e2, e3) ->
  app (free_vars_expr e1) (app (free_vars_expr e2) (free_vars_expr e3))
| _ -> []

(** val param_names : param list -> ident list **)

let rec param_names = function
| [] -> []
| p :: ps' -> p.param_name :: (param_names ps')

(** val rename_place : rename_env -> place -> place **)

let rename_place _UU03c1_ p =
  lookup_rename p _UU03c1_

(** val alpha_rename_expr :
    rename_env -> ident list -> expr -> expr * ident list **)

let rec alpha_rename_expr _UU03c1_ used = function
| EVar x -> ((EVar (lookup_rename x _UU03c1_)), used)
| ELet (m, x, t, e1, e2) ->
  let (e1', used1) = alpha_rename_expr _UU03c1_ used e1 in
  let used1' = x :: (app (free_vars_expr e2) used1) in
  let x' = fresh_ident x used1' in
  let used2 = x' :: used1' in
  let (e2', used3) = alpha_rename_expr ((x, x') :: _UU03c1_) used2 e2 in
  ((ELet (m, x', t, e1', e2')), used3)
| ELetInfer (m, x, e1, e2) ->
  let (e1', used1) = alpha_rename_expr _UU03c1_ used e1 in
  let used1' = x :: (app (free_vars_expr e2) used1) in
  let x' = fresh_ident x used1' in
  let used2 = x' :: used1' in
  let (e2', used3) = alpha_rename_expr ((x, x') :: _UU03c1_) used2 e2 in
  ((ELetInfer (m, x', e1', e2')), used3)
| ECall (fname, args) ->
  let go =
    let rec go used0 = function
    | [] -> ([], used0)
    | arg :: rest ->
      let (arg', used1) = alpha_rename_expr _UU03c1_ used0 arg in
      let (rest', used2) = go used1 rest in ((arg' :: rest'), used2)
    in go
  in
  let (args', used') = go used args in ((ECall (fname, args')), used')
| EReplace (p, e_new) ->
  let (e_new', used') = alpha_rename_expr _UU03c1_ used e_new in
  ((EReplace ((rename_place _UU03c1_ p), e_new')), used')
| EDrop e1 ->
  let (e1', used') = alpha_rename_expr _UU03c1_ used e1 in
  ((EDrop e1'), used')
| EIf (e1, e2, e3) ->
  let (e1', used1) = alpha_rename_expr _UU03c1_ used e1 in
  let (e2', used2) = alpha_rename_expr _UU03c1_ used1 e2 in
  let (e3', used3) = alpha_rename_expr _UU03c1_ used2 e3 in
  ((EIf (e1', e2', e3')), used3)
| x -> (x, used)

(** val alpha_rename_params :
    rename_env -> ident list -> param list -> (param
    list * rename_env) * ident list **)

let rec alpha_rename_params _UU03c1_ used = function
| [] -> (([], _UU03c1_), used)
| p :: ps' ->
  let x = p.param_name in
  let x' = fresh_ident x used in
  let p' = { param_mutability = p.param_mutability; param_name = x';
    param_ty = p.param_ty }
  in
  let (p0, used') = alpha_rename_params ((x, x') :: _UU03c1_) (x' :: used) ps'
  in
  let (ps'', _UU03c1_') = p0 in (((p' :: ps''), _UU03c1_'), used')

(** val alpha_rename_fn_def : ident list -> fn_def -> fn_def * ident list **)

let alpha_rename_fn_def used f =
  let used0 =
    app (param_names f.fn_params) (app (free_vars_expr f.fn_body) used)
  in
  let (p, used1) = alpha_rename_params [] used0 f.fn_params in
  let (params', _UU03c1_) = p in
  let (body', used2) = alpha_rename_expr _UU03c1_ used1 f.fn_body in
  ({ fn_name = f.fn_name; fn_params = params'; fn_ret = f.fn_ret; fn_body =
  body' }, used2)

(** val alpha_rename_syntax_go :
    ident list -> syntax -> syntax * ident list **)

let rec alpha_rename_syntax_go used = function
| [] -> ([], used)
| f :: fs ->
  let (f', used1) = alpha_rename_fn_def used f in
  let (fs', used2) = alpha_rename_syntax_go used1 fs in ((f' :: fs'), used2)

(** val alpha_rename_for_infer :
    ctx -> fn_def list -> expr -> fn_def list * expr **)

let alpha_rename_for_infer _UU0393_ fenv e =
  let (fenv', used) =
    alpha_rename_syntax_go (app (free_vars_expr e) (ctx_names _UU0393_)) fenv
  in
  let (e', _) = alpha_rename_expr [] used e in (fenv', e')

(** val infer_core : fn_def list -> ctx -> expr -> (ty * ctx) infer_result **)

let rec infer_core fenv _UU0393_ = function
| EUnit -> Infer_ok ((MkTy (UUnrestricted, TUnits)), _UU0393_)
| ELit l ->
  (match l with
   | LInt _ -> Infer_ok ((MkTy (UUnrestricted, TIntegers)), _UU0393_)
   | LFloat _ -> Infer_ok ((MkTy (UUnrestricted, TFloats)), _UU0393_)
   | LBool _ -> Infer_ok ((MkTy (UUnrestricted, TBooleans)), _UU0393_))
| EVar x ->
  (match ctx_lookup_b x _UU0393_ with
   | Some p ->
     let (t, b) = p in
     if usage_eqb (ty_usage t) UUnrestricted
     then Infer_ok (t, _UU0393_)
     else if b
          then Infer_err (ErrAlreadyConsumed x)
          else (match ctx_consume_b x _UU0393_ with
                | Some _UU0393_' -> Infer_ok (t, _UU0393_')
                | None -> Infer_err (ErrUnknownVar x))
   | None -> Infer_err (ErrUnknownVar x))
| ELet (_, x, t, e1, e2) ->
  (match infer_core fenv _UU0393_ e1 with
   | Infer_ok p ->
     let (t1, _UU0393_1) = p in
     if ty_core_eqb (ty_core t1) (ty_core t)
     then if usage_sub_bool (ty_usage t1) (ty_usage t)
          then (match infer_core fenv (ctx_add_b x t _UU0393_1) e2 with
                | Infer_ok p0 ->
                  let (t2, _UU0393_2) = p0 in
                  if ctx_check_ok x t _UU0393_2
                  then Infer_ok (t2, (ctx_remove_b x _UU0393_2))
                  else Infer_err ErrContextCheckFailed
                | Infer_err err -> Infer_err err)
          else Infer_err (ErrUsageMismatch ((ty_usage t1), (ty_usage t)))
     else Infer_err (ErrTypeMismatch ((ty_core t1), (ty_core t)))
   | Infer_err err -> Infer_err err)
| ELetInfer (_, x, e1, e2) ->
  (match infer_core fenv _UU0393_ e1 with
   | Infer_ok p ->
     let (t1, _UU0393_1) = p in
     (match infer_core fenv (ctx_add_b x t1 _UU0393_1) e2 with
      | Infer_ok p0 ->
        let (t2, _UU0393_2) = p0 in
        if ctx_check_ok x t1 _UU0393_2
        then Infer_ok (t2, (ctx_remove_b x _UU0393_2))
        else Infer_err ErrContextCheckFailed
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| ECall (fname, args) ->
  (match lookup_fn_b fname fenv with
   | Some fdef ->
     let go =
       let rec go _UU0393_0 as_ ps =
         match as_ with
         | [] ->
           (match ps with
            | [] -> Infer_ok _UU0393_0
            | _ :: _ -> Infer_err ErrArityMismatch)
         | e' :: es ->
           (match ps with
            | [] -> Infer_err ErrArityMismatch
            | p :: ps' ->
              (match infer_core fenv _UU0393_0 e' with
               | Infer_ok p0 ->
                 let (t_e, _UU0393_1) = p0 in
                 if ty_core_eqb (ty_core t_e) (ty_core p.param_ty)
                 then if usage_sub_bool (ty_usage t_e) (ty_usage p.param_ty)
                      then go _UU0393_1 es ps'
                      else Infer_err (ErrUsageMismatch ((ty_usage t_e),
                             (ty_usage p.param_ty)))
                 else Infer_err (ErrTypeMismatch ((ty_core t_e),
                        (ty_core p.param_ty)))
               | Infer_err err -> Infer_err err))
       in go
     in
     (match go _UU0393_ args fdef.fn_params with
      | Infer_ok _UU0393_' -> Infer_ok (fdef.fn_ret, _UU0393_')
      | Infer_err err -> Infer_err err)
   | None -> Infer_err (ErrFunctionNotFound fname))
| EReplace (p, e_new) ->
  (match ctx_lookup_b p _UU0393_ with
   | Some p0 ->
     let (t_x, b) = p0 in
     if b
     then Infer_err (ErrAlreadyConsumed p)
     else (match infer_core fenv _UU0393_ e_new with
           | Infer_ok p1 ->
             let (t_new, _UU0393_') = p1 in
             if ty_core_eqb (ty_core t_new) (ty_core t_x)
             then if usage_sub_bool (ty_usage t_new) (ty_usage t_x)
                  then Infer_ok (t_x, _UU0393_')
                  else Infer_err (ErrUsageMismatch ((ty_usage t_new),
                         (ty_usage t_x)))
             else Infer_err (ErrTypeMismatch ((ty_core t_new), (ty_core t_x)))
           | Infer_err err -> Infer_err err)
   | None -> Infer_err (ErrUnknownVar p))
| EDrop e1 ->
  (match infer_core fenv _UU0393_ e1 with
   | Infer_ok p ->
     let (_, _UU0393_') = p in
     Infer_ok ((MkTy (UUnrestricted, TUnits)), _UU0393_')
   | Infer_err err -> Infer_err err)
| EIf (e1, e2, e3) ->
  (match infer_core fenv _UU0393_ e1 with
   | Infer_ok p ->
     let (t_cond, _UU0393_1) = p in
     if ty_core_eqb (ty_core t_cond) TBooleans
     then (match infer_core fenv _UU0393_1 e2 with
           | Infer_ok p0 ->
             let (t2, _UU0393_2) = p0 in
             (match infer_core fenv _UU0393_1 e3 with
              | Infer_ok p1 ->
                let (t3, _UU0393_3) = p1 in
                if ty_core_eqb (ty_core t2) (ty_core t3)
                then (match ctx_merge _UU0393_2 _UU0393_3 with
                      | Some _UU0393_4 ->
                        Infer_ok ((MkTy
                          ((usage_max (ty_usage t2) (ty_usage t3)),
                          (ty_core t2))), _UU0393_4)
                      | None -> Infer_err ErrContextCheckFailed)
                else Infer_err (ErrTypeMismatch ((ty_core t2), (ty_core t3)))
              | Infer_err err -> Infer_err err)
           | Infer_err err -> Infer_err err)
     else Infer_err (ErrTypeMismatch ((ty_core t_cond), TBooleans))
   | Infer_err err -> Infer_err err)

(** val infer_body : fn_def list -> ctx -> expr -> (ty * ctx) infer_result **)

let infer_body fenv _UU0393_ e =
  let (fenv', e') = alpha_rename_for_infer _UU0393_ fenv e in
  infer_core fenv' _UU0393_ e'

(** val params_ok_b : param list -> ctx -> bool **)

let rec params_ok_b ps _UU0393_ =
  match ps with
  | [] -> true
  | p :: ps' ->
    (&&) (ctx_check_ok p.param_name p.param_ty _UU0393_)
      (params_ok_b ps' _UU0393_)

(** val infer : fn_def list -> fn_def -> (ty * ctx) infer_result **)

let infer fenv f =
  match infer_body fenv (params_ctx f.fn_params) f.fn_body with
  | Infer_ok p ->
    let (t_body, _UU0393__out) = p in
    if ty_core_eqb (ty_core t_body) (ty_core f.fn_ret)
    then if usage_eqb (ty_usage t_body) (ty_usage f.fn_ret)
         then if params_ok_b f.fn_params _UU0393__out
              then Infer_ok (f.fn_ret, _UU0393__out)
              else Infer_err ErrContextCheckFailed
         else Infer_err (ErrUsageMismatch ((ty_usage f.fn_ret),
                (ty_usage t_body)))
    else Infer_err (ErrTypeMismatch ((ty_core f.fn_ret), (ty_core t_body)))
  | Infer_err err -> Infer_err err

(** val check_program : fn_def list -> bool **)

let check_program fenv =
  forallb (fun f ->
    match infer fenv f with
    | Infer_ok _ -> true
    | Infer_err _ -> false) fenv
