
type bool =
| True
| False

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

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

type ident = string

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
  (match eqb1 x n with
   | True -> Some (Pair (t0, b))
   | False -> ctx_lookup_b x t)

(** val ctx_consume_b : ident -> ctx -> ctx option **)

let rec ctx_consume_b x = function
| Nil -> None
| Cons (c, t) ->
  let Pair (p, b) = c in
  let Pair (n, t0) = p in
  (match eqb1 x n with
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
  (match eqb1 x n with
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
  (match eqb1 name f.fn_name with
   | True -> Some f
   | False -> lookup_fn_b name t)

(** val infer : fn_def list -> ctx -> expr -> (ty, ctx) prod option **)

let rec infer fenv _UU0393_ = function
| EUnit -> Some (Pair ((MkTy (UUnrestricted, TUnits)), _UU0393_))
| ELit l ->
  (match l with
   | LInt _ -> Some (Pair ((MkTy (UUnrestricted, TIntegers)), _UU0393_))
   | LFloat _ -> Some (Pair ((MkTy (UUnrestricted, TFloats)), _UU0393_)))
| EVar x ->
  (match ctx_lookup_b x _UU0393_ with
   | Some p ->
     let Pair (t, b) = p in
     (match usage_eqb (ty_usage t) UUnrestricted with
      | True -> Some (Pair (t, _UU0393_))
      | False ->
        (match b with
         | True -> None
         | False ->
           (match ctx_consume_b x _UU0393_ with
            | Some _UU0393_' -> Some (Pair (t, _UU0393_'))
            | None -> None)))
   | None -> None)
| ELet (_, x, t, e1, e2) ->
  (match infer fenv _UU0393_ e1 with
   | Some p ->
     let Pair (t1, _UU0393_1) = p in
     (match match ty_core_eqb (ty_core t1) (ty_core t) with
            | True -> usage_sub_bool (ty_usage t1) (ty_usage t)
            | False -> False with
      | True ->
        (match infer fenv (ctx_add_b x t _UU0393_1) e2 with
         | Some p0 ->
           let Pair (t2, _UU0393_2) = p0 in
           (match ctx_check_ok x t _UU0393_2 with
            | True -> Some (Pair (t2, (ctx_remove_b x _UU0393_2)))
            | False -> None)
         | None -> None)
      | False -> None)
   | None -> None)
| ELetInfer (_, _, _, _) -> None
| ECall (fname, args) ->
  (match lookup_fn_b fname fenv with
   | Some fdef ->
     let go =
       let rec go _UU0393_0 as_ ps =
         match as_ with
         | Nil -> (match ps with
                   | Nil -> Some _UU0393_0
                   | Cons (_, _) -> None)
         | Cons (e', es) ->
           (match ps with
            | Nil -> None
            | Cons (p, ps') ->
              (match infer fenv _UU0393_0 e' with
               | Some p0 ->
                 let Pair (t_e, _UU0393_1) = p0 in
                 (match match ty_core_eqb (ty_core t_e) (ty_core p.param_ty) with
                        | True ->
                          usage_sub_bool (ty_usage t_e) (ty_usage p.param_ty)
                        | False -> False with
                  | True -> go _UU0393_1 es ps'
                  | False -> None)
               | None -> None))
       in go
     in
     (match go _UU0393_ args fdef.fn_params with
      | Some _UU0393_' -> Some (Pair (fdef.fn_ret, _UU0393_'))
      | None -> None)
   | None -> None)
| EReplace (p, e_new) ->
  (match ctx_lookup_b p _UU0393_ with
   | Some p0 ->
     let Pair (t_x, b) = p0 in
     (match b with
      | True -> None
      | False ->
        (match infer fenv _UU0393_ e_new with
         | Some p1 ->
           let Pair (t_new, _UU0393_') = p1 in
           (match match ty_core_eqb (ty_core t_new) (ty_core t_x) with
                  | True -> usage_sub_bool (ty_usage t_new) (ty_usage t_x)
                  | False -> False with
            | True -> Some (Pair (t_x, _UU0393_'))
            | False -> None)
         | None -> None))
   | None -> None)
| EDrop e1 ->
  (match infer fenv _UU0393_ e1 with
   | Some p ->
     let Pair (_, _UU0393_') = p in
     Some (Pair ((MkTy (UUnrestricted, TUnits)), _UU0393_'))
   | None -> None)
