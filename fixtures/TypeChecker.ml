
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

(** val length : 'a1 list -> Big_int_Z.big_int **)

let rec length = function
| [] -> Big_int_Z.zero_big_int
| _ :: l' -> Big_int_Z.succ_big_int (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec sub = (fun n m -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.sub_big_int n m))

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec eqb = Big_int_Z.eq_big_int

  (** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let rec leb = Big_int_Z.le_big_int

  (** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

  let ltb n m =
    leb (Big_int_Z.succ_big_int n) m

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

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: l0 -> (f a) :: (map f l0)

(** val repeat : 'a1 -> Big_int_Z.big_int -> 'a1 list **)

let rec repeat x n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun k -> x :: (repeat x k))
    n

(** val firstn : Big_int_Z.big_int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n0 l0))
    n

(** val nth_error : 'a1 list -> Big_int_Z.big_int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l' -> nth_error l' n0)
    n

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: l0 -> fold_left f l0 (f a0 b)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

type lifetime =
| LStatic
| LVar of Big_int_Z.big_int

(** val lifetime_eqb : lifetime -> lifetime -> bool **)

let lifetime_eqb l1 l2 =
  match l1 with
  | LStatic -> (match l2 with
                | LStatic -> true
                | LVar _ -> false)
  | LVar n1 -> (match l2 with
                | LStatic -> false
                | LVar n2 -> Nat.eqb n1 n2)

type region_ctx = lifetime list

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
| TRef of lifetime * ref_kind * 'a

type ty =
| MkTy of usage * ty typeCore

(** val ty_usage : ty -> usage **)

let ty_usage = function
| MkTy (u, _) -> u

(** val ty_core : ty -> ty typeCore **)

let ty_core = function
| MkTy (_, c) -> c

(** val apply_lt_lifetime : lifetime list -> lifetime -> lifetime **)

let rec apply_lt_lifetime _UU03c3_ = function
| LStatic -> LStatic
| LVar i -> (match nth_error _UU03c3_ i with
             | Some l' -> l'
             | None -> LVar i)

(** val apply_lt_ty : lifetime list -> ty -> ty **)

let rec apply_lt_ty _UU03c3_ = function
| MkTy (u, t0) ->
  (match t0 with
   | TFn (ts, r) ->
     let map_lt =
       let rec map_lt = function
       | [] -> []
       | x :: xs' -> (apply_lt_ty _UU03c3_ x) :: (map_lt xs')
       in map_lt
     in
     MkTy (u, (TFn ((map_lt ts), (apply_lt_ty _UU03c3_ r))))
   | TRef (l, rk, t1) ->
     MkTy (u, (TRef ((apply_lt_lifetime _UU03c3_ l), rk,
       (apply_lt_ty _UU03c3_ t1))))
   | x -> MkTy (u, x))

type ident = string * Big_int_Z.big_int

(** val ident_eqb : ident -> ident -> bool **)

let ident_eqb x y =
  (&&) ((=) (fst x) (fst y)) (Nat.eqb (snd x) (snd y))

type literal =
| LInt of Big_int_Z.big_int
| LFloat of string
| LBool of bool

type place =
| PVar of ident
| PDeref of place

type expr =
| EUnit
| ELit of literal
| EVar of ident
| ELet of mutability * ident * ty * expr * expr
| ELetInfer of mutability * ident * expr * expr
| ECall of ident * expr list
| EReplace of place * expr
| EAssign of place * expr
| EBorrow of ref_kind * place
| EDeref of expr
| EDrop of expr
| EIf of expr * expr * expr

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type fn_def = { fn_name : ident; fn_lifetimes : Big_int_Z.big_int;
                fn_params : param list; fn_ret : ty; fn_body : expr }

type syntax = fn_def list

type ctx_entry = ((ident * ty) * bool) * mutability

type ctx = ctx_entry list

(** val param_ctx_entry : param -> ctx_entry **)

let param_ctx_entry p =
  (((p.param_name, p.param_ty), false), p.param_mutability)

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
    let (p, m) = c in
    let (p0, b2) = p in
    let (n, t) = p0 in
    (match _UU0393_3 with
     | [] -> None
     | c0 :: t3 ->
       let (p1, _) = c0 in
       let (p2, b3) = p1 in
       let (n', _) = p2 in
       if negb (ident_eqb n n')
       then None
       else (match ctx_merge t2 t3 with
             | Some rest ->
               (match ty_usage t with
                | ULinear ->
                  if eqb b2 b3 then Some ((((n, t), b2), m) :: rest) else None
                | _ -> Some ((((n, t), ((||) b2 b3)), m) :: rest))
             | None -> None))

(** val apply_lt_param : lifetime list -> param -> param **)

let apply_lt_param _UU03c3_ p =
  { param_mutability = p.param_mutability; param_name = p.param_name;
    param_ty = (apply_lt_ty _UU03c3_ p.param_ty) }

(** val apply_lt_params : lifetime list -> param list -> param list **)

let apply_lt_params _UU03c3_ ps =
  map (apply_lt_param _UU03c3_) ps

type borrow_entry =
| BEShared of ident
| BEMut of ident

type borrow_state = borrow_entry list

(** val be_eqb : borrow_entry -> borrow_entry -> bool **)

let be_eqb e1 e2 =
  match e1 with
  | BEShared x ->
    (match e2 with
     | BEShared y -> ident_eqb x y
     | BEMut _ -> false)
  | BEMut x -> (match e2 with
                | BEShared _ -> false
                | BEMut y -> ident_eqb x y)

(** val bs_eqb : borrow_state -> borrow_state -> bool **)

let rec bs_eqb bs1 bs2 =
  match bs1 with
  | [] -> (match bs2 with
           | [] -> true
           | _ :: _ -> false)
  | e1 :: t1 ->
    (match bs2 with
     | [] -> false
     | e2 :: t2 -> (&&) (be_eqb e1 e2) (bs_eqb t1 t2))

(** val bs_has_mut : ident -> borrow_state -> bool **)

let bs_has_mut x bs =
  existsb (fun e ->
    match e with
    | BEShared _ -> false
    | BEMut y -> ident_eqb x y) bs

(** val bs_has_any : ident -> borrow_state -> bool **)

let bs_has_any x bs =
  existsb (fun e ->
    match e with
    | BEShared y -> ident_eqb x y
    | BEMut y -> ident_eqb x y) bs

(** val bs_remove_one : borrow_entry -> borrow_state -> borrow_state **)

let rec bs_remove_one e = function
| [] -> []
| h :: t -> if be_eqb e h then t else h :: (bs_remove_one e t)

(** val bs_remove_all : borrow_state -> borrow_state -> borrow_state **)

let bs_remove_all to_remove bs =
  fold_left (fun acc e -> bs_remove_one e acc) to_remove bs

(** val bs_new_entries : borrow_state -> borrow_state -> borrow_state **)

let bs_new_entries bs_before bs_after =
  firstn (sub (length bs_after) (length bs_before)) bs_after

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

(** val ref_kind_eqb : ref_kind -> ref_kind -> bool **)

let ref_kind_eqb k1 k2 =
  match k1 with
  | RShared -> (match k2 with
                | RShared -> true
                | RUnique -> false)
  | RUnique -> (match k2 with
                | RShared -> false
                | RUnique -> true)

(** val ty_eqb : ty -> ty -> bool **)

let rec ty_eqb t1 t2 =
  let MkTy (u1, c1) = t1 in
  let MkTy (u2, c2) = t2 in
  (&&) (usage_eqb u1 u2)
    (match c1 with
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
     | TFn (ts1, r1) ->
       (match c2 with
        | TFn (ts2, r2) ->
          (&&)
            (let rec go l1 l2 =
               match l1 with
               | [] -> (match l2 with
                        | [] -> true
                        | _ :: _ -> false)
               | t3 :: l1' ->
                 (match l2 with
                  | [] -> false
                  | t4 :: l2' -> (&&) (ty_eqb t3 t4) (go l1' l2'))
             in go ts1 ts2)
            (ty_eqb r1 r2)
        | _ -> false)
     | TRef (l1, k1, t3) ->
       (match c2 with
        | TRef (l2, k2, t4) ->
          (&&) ((&&) (lifetime_eqb l1 l2) (ref_kind_eqb k1 k2)) (ty_eqb t3 t4)
        | _ -> false))

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
  | TFn (ts1, r1) ->
    (match c2 with
     | TFn (ts2, r2) ->
       (&&)
         (let rec go l1 l2 =
            match l1 with
            | [] -> (match l2 with
                     | [] -> true
                     | _ :: _ -> false)
            | t1 :: l1' ->
              (match l2 with
               | [] -> false
               | t2 :: l2' -> (&&) (ty_eqb t1 t2) (go l1' l2'))
          in go ts1 ts2)
         (ty_eqb r1 r2)
     | _ -> false)
  | TRef (l1, k1, t1) ->
    (match c2 with
     | TRef (l2, k2, t2) ->
       (&&) ((&&) (lifetime_eqb l1 l2) (ref_kind_eqb k1 k2)) (ty_eqb t1 t2)
     | _ -> false)

(** val ctx_lookup_b : ident -> ctx -> (ty * bool) option **)

let rec ctx_lookup_b x = function
| [] -> None
| c :: t ->
  let (p, _) = c in
  let (p0, b) = p in
  let (n, t0) = p0 in if ident_eqb x n then Some (t0, b) else ctx_lookup_b x t

(** val ctx_consume_b : ident -> ctx -> ctx option **)

let rec ctx_consume_b x = function
| [] -> None
| c :: t ->
  let (p, m) = c in
  let (p0, b) = p in
  let (n, t0) = p0 in
  if ident_eqb x n
  then Some ((((n, t0), true), m) :: t)
  else (match ctx_consume_b x t with
        | Some t' -> Some ((((n, t0), b), m) :: t')
        | None -> None)

(** val ctx_lookup_mut_b : ident -> ctx -> mutability option **)

let rec ctx_lookup_mut_b x = function
| [] -> None
| c :: t ->
  let (p, m) = c in
  let (p0, _) = p in
  let (n, _) = p0 in if ident_eqb x n then Some m else ctx_lookup_mut_b x t

(** val ctx_add_b : ident -> ty -> mutability -> ctx -> ctx **)

let ctx_add_b x t m _UU0393_ =
  (((x, t), false), m) :: _UU0393_

(** val ctx_remove_b : ident -> ctx -> ctx **)

let rec ctx_remove_b x = function
| [] -> []
| c :: t ->
  let (p, m) = c in
  let (p0, b) = p in
  let (n, t0) = p0 in
  if ident_eqb x n then t else (((n, t0), b), m) :: (ctx_remove_b x t)

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

(** val mk_region_ctx : Big_int_Z.big_int -> region_ctx **)

let rec mk_region_ctx n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun k -> app (mk_region_ctx k) ((LVar k) :: []))
    n

(** val wf_lifetime_b : region_ctx -> lifetime -> bool **)

let wf_lifetime_b _UU0394_ l = match l with
| LStatic -> true
| LVar _ -> existsb (lifetime_eqb l) _UU0394_

(** val wf_type_b : region_ctx -> ty -> bool **)

let rec wf_type_b _UU0394_ = function
| MkTy (_, t0) ->
  (match t0 with
   | TFn (ts, r) ->
     (&&) (forallb (wf_type_b _UU0394_) ts) (wf_type_b _UU0394_ r)
   | TRef (l, _, t_inner) ->
     (&&) (wf_lifetime_b _UU0394_ l) (wf_type_b _UU0394_ t_inner)
   | _ -> true)

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
  let (p, _) = c in
  let (p0, _) = p in let (x, _) = p0 in x :: (ctx_names _UU0393_')

(** val place_name : place -> ident **)

let rec place_name = function
| PVar x -> x
| PDeref q -> place_name q

type infer_error =
| ErrUnknownVar of ident
| ErrAlreadyConsumed of ident
| ErrTypeMismatch of ty typeCore * ty typeCore
| ErrNotMutable of ident
| ErrUsageMismatch of usage * usage
| ErrFunctionNotFound of ident
| ErrArityMismatch
| ErrContextCheckFailed
| ErrNotImplemented
| ErrImmutableBorrow of ident
| ErrNotAReference of ty typeCore
| ErrBorrowConflict of ident
| ErrLifetimeLeak
| ErrLifetimeConflict

(** val list_set_nth : Big_int_Z.big_int -> 'a1 -> 'a1 list -> 'a1 list **)

let rec list_set_nth i v l =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> match l with
              | [] -> []
              | _ :: t -> v :: t)
    (fun i' -> match l with
               | [] -> []
               | h :: t -> h :: (list_set_nth i' v t))
    i

(** val lt_subst_vec_add :
    lifetime option list -> Big_int_Z.big_int -> lifetime -> lifetime option
    list option **)

let lt_subst_vec_add _UU03c3_ i l_a =
  match nth_error _UU03c3_ i with
  | Some o ->
    (match o with
     | Some l' -> if lifetime_eqb l' l_a then Some _UU03c3_ else None
     | None -> Some (list_set_nth i (Some l_a) _UU03c3_))
  | None -> None

(** val unify_lt :
    Big_int_Z.big_int -> lifetime option list -> ty -> ty -> lifetime option
    list option **)

let rec unify_lt m _UU03c3_ t_param t_e =
  let MkTy (_, t) = t_param in
  (match t with
   | TRef (l_p, rk, t_p_inner) ->
     let MkTy (_, t0) = t_e in
     (match t0 with
      | TRef (l_a, rk', t_e_inner) ->
        if negb (ref_kind_eqb rk rk')
        then None
        else (match l_p with
              | LStatic ->
                if lifetime_eqb LStatic l_a
                then unify_lt m _UU03c3_ t_p_inner t_e_inner
                else None
              | LVar i ->
                if Nat.ltb i m
                then (match lt_subst_vec_add _UU03c3_ i l_a with
                      | Some _UU03c3_' ->
                        unify_lt m _UU03c3_' t_p_inner t_e_inner
                      | None -> None)
                else if lifetime_eqb (LVar i) l_a
                     then unify_lt m _UU03c3_ t_p_inner t_e_inner
                     else None)
      | _ -> None)
   | _ ->
     if ty_core_eqb (ty_core t_param) (ty_core t_e)
     then Some _UU03c3_
     else None)

(** val finalize_subst : lifetime option list -> lifetime list **)

let rec finalize_subst = function
| [] -> []
| o :: rest ->
  (match o with
   | Some l -> l :: (finalize_subst rest)
   | None -> LStatic :: (finalize_subst rest))

(** val build_sigma :
    Big_int_Z.big_int -> lifetime option list -> ty list -> param list ->
    lifetime option list option **)

let rec build_sigma m _UU03c3__acc arg_tys params =
  match arg_tys with
  | [] -> (match params with
           | [] -> Some _UU03c3__acc
           | _ :: _ -> None)
  | t :: ts ->
    (match params with
     | [] -> None
     | p :: ps ->
       (match unify_lt m _UU03c3__acc p.param_ty t with
        | Some _UU03c3_' -> build_sigma m _UU03c3_' ts ps
        | None -> None))

(** val check_args : ty list -> param list -> infer_error option **)

let rec check_args arg_tys params =
  match arg_tys with
  | [] -> (match params with
           | [] -> None
           | _ :: _ -> Some ErrArityMismatch)
  | t :: ts ->
    (match params with
     | [] -> Some ErrArityMismatch
     | p :: ps ->
       if ty_core_eqb (ty_core t) (ty_core p.param_ty)
       then if usage_sub_bool (ty_usage t) (ty_usage p.param_ty)
            then check_args ts ps
            else Some (ErrUsageMismatch ((ty_usage t), (ty_usage p.param_ty)))
       else Some (ErrTypeMismatch ((ty_core t), (ty_core p.param_ty))))

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
| EAssign (p, e_new) -> (place_name p) :: (free_vars_expr e_new)
| EBorrow (_, p) -> (place_name p) :: []
| EDeref e1 -> free_vars_expr e1
| EDrop e1 -> free_vars_expr e1
| EIf (e1, e2, e3) ->
  app (free_vars_expr e1) (app (free_vars_expr e2) (free_vars_expr e3))
| _ -> []

(** val param_names : param list -> ident list **)

let rec param_names = function
| [] -> []
| p :: ps' -> p.param_name :: (param_names ps')

(** val rename_place : rename_env -> place -> place **)

let rec rename_place _UU03c1_ = function
| PVar x -> PVar (lookup_rename x _UU03c1_)
| PDeref q -> PDeref (rename_place _UU03c1_ q)

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
| EAssign (p, e_new) ->
  let (e_new', used') = alpha_rename_expr _UU03c1_ used e_new in
  ((EAssign ((rename_place _UU03c1_ p), e_new')), used')
| EBorrow (rk, p) -> ((EBorrow (rk, (rename_place _UU03c1_ p))), used)
| EDeref e1 ->
  let (e1', used') = alpha_rename_expr _UU03c1_ used e1 in
  ((EDeref e1'), used')
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
  ({ fn_name = f.fn_name; fn_lifetimes = f.fn_lifetimes; fn_params = params';
  fn_ret = f.fn_ret; fn_body = body' }, used2)

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

(** val infer_core :
    fn_def list -> Big_int_Z.big_int -> ctx -> expr -> (ty * ctx) infer_result **)

let rec infer_core fenv n _UU0393_ = function
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
| ELet (m, x, t, e1, e2) ->
  (match infer_core fenv n _UU0393_ e1 with
   | Infer_ok p ->
     let (t1, _UU0393_1) = p in
     if ty_core_eqb (ty_core t1) (ty_core t)
     then if usage_sub_bool (ty_usage t1) (ty_usage t)
          then (match infer_core fenv n (ctx_add_b x t m _UU0393_1) e2 with
                | Infer_ok p0 ->
                  let (t2, _UU0393_2) = p0 in
                  if ctx_check_ok x t _UU0393_2
                  then Infer_ok (t2, (ctx_remove_b x _UU0393_2))
                  else Infer_err ErrContextCheckFailed
                | Infer_err err -> Infer_err err)
          else Infer_err (ErrUsageMismatch ((ty_usage t1), (ty_usage t)))
     else Infer_err (ErrTypeMismatch ((ty_core t1), (ty_core t)))
   | Infer_err err -> Infer_err err)
| ELetInfer (m, x, e1, e2) ->
  (match infer_core fenv n _UU0393_ e1 with
   | Infer_ok p ->
     let (t1, _UU0393_1) = p in
     (match infer_core fenv n (ctx_add_b x t1 m _UU0393_1) e2 with
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
     let m = fdef.fn_lifetimes in
     let collect =
       let rec collect _UU0393_0 = function
       | [] -> Infer_ok ([], _UU0393_0)
       | e' :: es ->
         (match infer_core fenv n _UU0393_0 e' with
          | Infer_ok p ->
            let (t_e, _UU0393_1) = p in
            (match collect _UU0393_1 es with
             | Infer_ok p0 ->
               let (tys, _UU0393_2) = p0 in Infer_ok ((t_e :: tys), _UU0393_2)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       in collect
     in
     (match collect _UU0393_ args with
      | Infer_ok p ->
        let (arg_tys, _UU0393_') = p in
        (match build_sigma m (repeat None m) arg_tys fdef.fn_params with
         | Some _UU03c3__acc ->
           let _UU03c3_ = finalize_subst _UU03c3__acc in
           let ps_subst = apply_lt_params _UU03c3_ fdef.fn_params in
           (match check_args arg_tys ps_subst with
            | Some err -> Infer_err err
            | None ->
              if forallb (wf_lifetime_b (mk_region_ctx n)) _UU03c3_
              then Infer_ok ((apply_lt_ty _UU03c3_ fdef.fn_ret), _UU0393_')
              else Infer_err ErrLifetimeLeak)
         | None -> Infer_err ErrLifetimeConflict)
      | Infer_err err -> Infer_err err)
   | None -> Infer_err (ErrFunctionNotFound fname))
| EReplace (p, e_new) ->
  (match p with
   | PVar x ->
     (match ctx_lookup_b x _UU0393_ with
      | Some p0 ->
        let (t_x, b) = p0 in
        if b
        then Infer_err (ErrAlreadyConsumed x)
        else (match ctx_lookup_mut_b x _UU0393_ with
              | Some m ->
                (match m with
                 | MImmutable -> Infer_err (ErrNotMutable x)
                 | MMutable ->
                   (match infer_core fenv n _UU0393_ e_new with
                    | Infer_ok p1 ->
                      let (t_new, _UU0393_') = p1 in
                      if ty_core_eqb (ty_core t_new) (ty_core t_x)
                      then if usage_sub_bool (ty_usage t_new) (ty_usage t_x)
                           then Infer_ok (t_x, _UU0393_')
                           else Infer_err (ErrUsageMismatch
                                  ((ty_usage t_new), (ty_usage t_x)))
                      else Infer_err (ErrTypeMismatch ((ty_core t_new),
                             (ty_core t_x)))
                    | Infer_err err -> Infer_err err))
              | None -> Infer_err (ErrUnknownVar x))
      | None -> Infer_err (ErrUnknownVar x))
   | PDeref p0 ->
     (match p0 with
      | PVar r ->
        (match ctx_lookup_b r _UU0393_ with
         | Some p1 ->
           let (t_r, b) = p1 in
           if b
           then Infer_err (ErrAlreadyConsumed r)
           else (match ty_core t_r with
                 | TRef (l, r0, t_inner) ->
                   (match r0 with
                    | RShared ->
                      Infer_err (ErrNotAReference (TRef (l, RShared,
                        t_inner)))
                    | RUnique ->
                      (match ctx_lookup_mut_b r _UU0393_ with
                       | Some m ->
                         (match m with
                          | MImmutable -> Infer_err (ErrNotMutable r)
                          | MMutable ->
                            (match infer_core fenv n _UU0393_ e_new with
                             | Infer_ok p2 ->
                               let (t_new, _UU0393_') = p2 in
                               if ty_core_eqb (ty_core t_new)
                                    (ty_core t_inner)
                               then if usage_sub_bool (ty_usage t_new)
                                         (ty_usage t_inner)
                                    then Infer_ok (t_inner, _UU0393_')
                                    else Infer_err (ErrUsageMismatch
                                           ((ty_usage t_new),
                                           (ty_usage t_inner)))
                               else Infer_err (ErrTypeMismatch
                                      ((ty_core t_new), (ty_core t_inner)))
                             | Infer_err err -> Infer_err err))
                       | None -> Infer_err (ErrUnknownVar r)))
                 | x -> Infer_err (ErrNotAReference x))
         | None -> Infer_err (ErrUnknownVar r))
      | PDeref _ -> Infer_err ErrNotImplemented))
| EAssign (p, e_new) ->
  (match p with
   | PVar x ->
     (match ctx_lookup_b x _UU0393_ with
      | Some p0 ->
        let (t_x, b) = p0 in
        if b
        then Infer_err (ErrAlreadyConsumed x)
        else (match ctx_lookup_mut_b x _UU0393_ with
              | Some m ->
                (match m with
                 | MImmutable -> Infer_err (ErrNotMutable x)
                 | MMutable ->
                   if usage_eqb (ty_usage t_x) ULinear
                   then Infer_err (ErrUsageMismatch ((ty_usage t_x), UAffine))
                   else (match infer_core fenv n _UU0393_ e_new with
                         | Infer_ok p1 ->
                           let (t_new, _UU0393_') = p1 in
                           if ty_core_eqb (ty_core t_new) (ty_core t_x)
                           then if usage_sub_bool (ty_usage t_new)
                                     (ty_usage t_x)
                                then Infer_ok ((MkTy (UUnrestricted,
                                       TUnits)), _UU0393_')
                                else Infer_err (ErrUsageMismatch
                                       ((ty_usage t_new), (ty_usage t_x)))
                           else Infer_err (ErrTypeMismatch ((ty_core t_new),
                                  (ty_core t_x)))
                         | Infer_err err -> Infer_err err))
              | None -> Infer_err (ErrUnknownVar x))
      | None -> Infer_err (ErrUnknownVar x))
   | PDeref p0 ->
     (match p0 with
      | PVar r ->
        (match ctx_lookup_b r _UU0393_ with
         | Some p1 ->
           let (t_r, b) = p1 in
           if b
           then Infer_err (ErrAlreadyConsumed r)
           else (match ty_core t_r with
                 | TRef (l, r0, t_inner) ->
                   (match r0 with
                    | RShared ->
                      Infer_err (ErrNotAReference (TRef (l, RShared,
                        t_inner)))
                    | RUnique ->
                      (match ctx_lookup_mut_b r _UU0393_ with
                       | Some m ->
                         (match m with
                          | MImmutable -> Infer_err (ErrNotMutable r)
                          | MMutable ->
                            if usage_eqb (ty_usage t_inner) ULinear
                            then Infer_err (ErrUsageMismatch
                                   ((ty_usage t_inner), UAffine))
                            else (match infer_core fenv n _UU0393_ e_new with
                                  | Infer_ok p2 ->
                                    let (t_new, _UU0393_') = p2 in
                                    if ty_core_eqb (ty_core t_new)
                                         (ty_core t_inner)
                                    then if usage_sub_bool (ty_usage t_new)
                                              (ty_usage t_inner)
                                         then Infer_ok ((MkTy (UUnrestricted,
                                                TUnits)), _UU0393_')
                                         else Infer_err (ErrUsageMismatch
                                                ((ty_usage t_new),
                                                (ty_usage t_inner)))
                                    else Infer_err (ErrTypeMismatch
                                           ((ty_core t_new),
                                           (ty_core t_inner)))
                                  | Infer_err err -> Infer_err err))
                       | None -> Infer_err (ErrUnknownVar r)))
                 | x -> Infer_err (ErrNotAReference x))
         | None -> Infer_err (ErrUnknownVar r))
      | PDeref _ -> Infer_err ErrNotImplemented))
| EBorrow (rk, p) ->
  (match rk with
   | RShared ->
     (match p with
      | PVar x ->
        (match ctx_lookup_b x _UU0393_ with
         | Some p0 ->
           let (t_x, b) = p0 in
           if b
           then Infer_err (ErrAlreadyConsumed x)
           else if usage_eqb (ty_usage t_x) ULinear
                then Infer_err (ErrUsageMismatch ((ty_usage t_x), UAffine))
                else (match rk with
                      | RShared ->
                        Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar n),
                          RShared, t_x)))), _UU0393_)
                      | RUnique ->
                        (match ctx_lookup_mut_b x _UU0393_ with
                         | Some m ->
                           (match m with
                            | MImmutable -> Infer_err (ErrImmutableBorrow x)
                            | MMutable ->
                              Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar
                                n), RUnique, t_x)))), _UU0393_))
                         | None -> Infer_err (ErrImmutableBorrow x)))
         | None -> Infer_err (ErrUnknownVar x))
      | PDeref p0 ->
        (match p0 with
         | PVar r ->
           (match ctx_lookup_b r _UU0393_ with
            | Some p1 ->
              let (t_r, b) = p1 in
              if b
              then Infer_err (ErrAlreadyConsumed r)
              else (match ty_core t_r with
                    | TRef (_, _, t_inner) ->
                      if usage_eqb (ty_usage t_r) ULinear
                      then Infer_err (ErrUsageMismatch ((ty_usage t_r),
                             UAffine))
                      else Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar n),
                             RShared, t_inner)))), _UU0393_)
                    | x -> Infer_err (ErrNotAReference x))
            | None -> Infer_err (ErrUnknownVar r))
         | PDeref _ -> Infer_err ErrNotImplemented))
   | RUnique ->
     (match p with
      | PVar x ->
        (match ctx_lookup_b x _UU0393_ with
         | Some p0 ->
           let (t_x, b) = p0 in
           if b
           then Infer_err (ErrAlreadyConsumed x)
           else if usage_eqb (ty_usage t_x) ULinear
                then Infer_err (ErrUsageMismatch ((ty_usage t_x), UAffine))
                else (match rk with
                      | RShared ->
                        Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar n),
                          RShared, t_x)))), _UU0393_)
                      | RUnique ->
                        (match ctx_lookup_mut_b x _UU0393_ with
                         | Some m ->
                           (match m with
                            | MImmutable -> Infer_err (ErrImmutableBorrow x)
                            | MMutable ->
                              Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar
                                n), RUnique, t_x)))), _UU0393_))
                         | None -> Infer_err (ErrImmutableBorrow x)))
         | None -> Infer_err (ErrUnknownVar x))
      | PDeref p0 ->
        (match p0 with
         | PVar r ->
           (match ctx_lookup_b r _UU0393_ with
            | Some p1 ->
              let (t_r, b) = p1 in
              if b
              then Infer_err (ErrAlreadyConsumed r)
              else (match ty_core t_r with
                    | TRef (l, r0, t_inner) ->
                      (match r0 with
                       | RShared ->
                         Infer_err (ErrNotAReference (TRef (l, RShared,
                           t_inner)))
                       | RUnique ->
                         if usage_eqb (ty_usage t_r) ULinear
                         then Infer_err (ErrUsageMismatch ((ty_usage t_r),
                                UAffine))
                         else (match ctx_lookup_mut_b r _UU0393_ with
                               | Some m ->
                                 (match m with
                                  | MImmutable ->
                                    Infer_err (ErrImmutableBorrow r)
                                  | MMutable ->
                                    Infer_ok ((MkTy (UUnrestricted, (TRef
                                      ((LVar n), RUnique, t_inner)))),
                                      _UU0393_))
                               | None -> Infer_err (ErrImmutableBorrow r)))
                    | x -> Infer_err (ErrNotAReference x))
            | None -> Infer_err (ErrUnknownVar r))
         | PDeref _ -> Infer_err ErrNotImplemented)))
| EDeref r ->
  (match infer_core fenv n _UU0393_ r with
   | Infer_ok p ->
     let (t_r, _UU0393_') = p in
     (match ty_core t_r with
      | TRef (_, _, t_inner) ->
        if usage_eqb (ty_usage t_inner) UUnrestricted
        then Infer_ok (t_inner, _UU0393_')
        else Infer_err (ErrUsageMismatch ((ty_usage t_inner), UUnrestricted))
      | x -> Infer_err (ErrNotAReference x))
   | Infer_err err -> Infer_err err)
| EDrop e1 ->
  (match infer_core fenv n _UU0393_ e1 with
   | Infer_ok p ->
     let (_, _UU0393_') = p in
     Infer_ok ((MkTy (UUnrestricted, TUnits)), _UU0393_')
   | Infer_err err -> Infer_err err)
| EIf (e1, e2, e3) ->
  (match infer_core fenv n _UU0393_ e1 with
   | Infer_ok p ->
     let (t_cond, _UU0393_1) = p in
     if ty_core_eqb (ty_core t_cond) TBooleans
     then (match infer_core fenv n _UU0393_1 e2 with
           | Infer_ok p0 ->
             let (t2, _UU0393_2) = p0 in
             (match infer_core fenv n _UU0393_1 e3 with
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

(** val infer_body :
    fn_def list -> Big_int_Z.big_int -> ctx -> expr -> (ty * ctx) infer_result **)

let infer_body fenv n _UU0393_ e =
  let (fenv', e') = alpha_rename_for_infer _UU0393_ fenv e in
  infer_core fenv' n _UU0393_ e'

(** val params_ok_b : param list -> ctx -> bool **)

let rec params_ok_b ps _UU0393_ =
  match ps with
  | [] -> true
  | p :: ps' ->
    (&&) (ctx_check_ok p.param_name p.param_ty _UU0393_)
      (params_ok_b ps' _UU0393_)

(** val infer : fn_def list -> fn_def -> (ty * ctx) infer_result **)

let infer fenv f =
  let n = f.fn_lifetimes in
  let _UU0394_ = mk_region_ctx n in
  if negb (wf_type_b _UU0394_ f.fn_ret)
  then Infer_err ErrLifetimeLeak
  else (match infer_body fenv n (params_ctx f.fn_params) f.fn_body with
        | Infer_ok p ->
          let (t_body, _UU0393__out) = p in
          if negb (wf_type_b _UU0394_ t_body)
          then Infer_err ErrLifetimeLeak
          else if ty_core_eqb (ty_core t_body) (ty_core f.fn_ret)
               then if usage_eqb (ty_usage t_body) (ty_usage f.fn_ret)
                    then if params_ok_b f.fn_params _UU0393__out
                         then Infer_ok (f.fn_ret, _UU0393__out)
                         else Infer_err ErrContextCheckFailed
                    else Infer_err (ErrUsageMismatch ((ty_usage f.fn_ret),
                           (ty_usage t_body)))
               else Infer_err (ErrTypeMismatch ((ty_core f.fn_ret),
                      (ty_core t_body)))
        | Infer_err err -> Infer_err err)

(** val check_program : fn_def list -> bool **)

let check_program fenv =
  forallb (fun f ->
    match infer fenv f with
    | Infer_ok _ -> true
    | Infer_err _ -> false) fenv

(** val borrow_check :
    fn_def list -> borrow_state -> ctx -> expr -> borrow_state infer_result **)

let rec borrow_check fenv bS _UU0393_ = function
| ELet (m, x, t, e1, e2) ->
  (match borrow_check fenv bS _UU0393_ e1 with
   | Infer_ok bS1 ->
     let new_from_e1 = bs_new_entries bS bS1 in
     (match borrow_check fenv bS1 (ctx_add_b x t m _UU0393_) e2 with
      | Infer_ok bS2 -> Infer_ok (bs_remove_all new_from_e1 bS2)
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| ELetInfer (_, _, e1, e2) ->
  (match borrow_check fenv bS _UU0393_ e1 with
   | Infer_ok bS1 ->
     let new_from_e1 = bs_new_entries bS bS1 in
     (match borrow_check fenv bS1 _UU0393_ e2 with
      | Infer_ok bS2 -> Infer_ok (bs_remove_all new_from_e1 bS2)
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| ECall (_, args) ->
  let rec go bS0 = function
  | [] -> Infer_ok bS0
  | a :: rest ->
    (match borrow_check fenv bS0 _UU0393_ a with
     | Infer_ok bS1 -> go bS1 rest
     | Infer_err err -> Infer_err err)
  in go bS args
| EReplace (p, e_new) ->
  (match p with
   | PVar _ -> borrow_check fenv bS _UU0393_ e_new
   | PDeref p0 ->
     (match p0 with
      | PVar r ->
        if bs_has_any r bS
        then Infer_err (ErrBorrowConflict r)
        else borrow_check fenv bS _UU0393_ e_new
      | PDeref _ -> Infer_err ErrNotImplemented))
| EAssign (p, e_new) ->
  (match p with
   | PVar _ -> borrow_check fenv bS _UU0393_ e_new
   | PDeref p0 ->
     (match p0 with
      | PVar r ->
        if bs_has_any r bS
        then Infer_err (ErrBorrowConflict r)
        else borrow_check fenv bS _UU0393_ e_new
      | PDeref _ -> Infer_err ErrNotImplemented))
| EBorrow (r0, p) ->
  (match r0 with
   | RShared ->
     (match p with
      | PVar x ->
        if bs_has_mut x bS
        then Infer_err (ErrBorrowConflict x)
        else Infer_ok ((BEShared x) :: bS)
      | PDeref p0 ->
        (match p0 with
         | PVar r ->
           if bs_has_mut r bS
           then Infer_err (ErrBorrowConflict r)
           else Infer_ok ((BEShared r) :: bS)
         | PDeref _ -> Infer_err ErrNotImplemented))
   | RUnique ->
     (match p with
      | PVar x ->
        if bs_has_any x bS
        then Infer_err (ErrBorrowConflict x)
        else Infer_ok ((BEMut x) :: bS)
      | PDeref p0 ->
        (match p0 with
         | PVar r ->
           if bs_has_any r bS
           then Infer_err (ErrBorrowConflict r)
           else Infer_ok ((BEMut r) :: bS)
         | PDeref _ -> Infer_err ErrNotImplemented)))
| EDeref e1 ->
  (match e1 with
   | EVar r ->
     if bs_has_mut r bS then Infer_err (ErrBorrowConflict r) else Infer_ok bS
   | _ -> borrow_check fenv bS _UU0393_ e1)
| EDrop e1 -> borrow_check fenv bS _UU0393_ e1
| EIf (e1, e2, e3) ->
  (match borrow_check fenv bS _UU0393_ e1 with
   | Infer_ok bS1 ->
     (match borrow_check fenv bS1 _UU0393_ e2 with
      | Infer_ok bS2 ->
        (match borrow_check fenv bS1 _UU0393_ e3 with
         | Infer_ok bS3 ->
           if bs_eqb bS2 bS3
           then Infer_ok bS2
           else Infer_err ErrContextCheckFailed
         | Infer_err err -> Infer_err err)
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| _ -> Infer_ok bS

(** val infer_full : fn_def list -> fn_def -> (ty * ctx) infer_result **)

let infer_full fenv f =
  match infer fenv f with
  | Infer_ok res ->
    let _UU0393_ = params_ctx f.fn_params in
    (match borrow_check fenv [] _UU0393_ f.fn_body with
     | Infer_ok _ -> Infer_ok res
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val infer_direct : fn_def list -> fn_def -> (ty * ctx) infer_result **)

let infer_direct fenv f =
  let n = f.fn_lifetimes in
  let _UU0394_ = mk_region_ctx n in
  if negb (wf_type_b _UU0394_ f.fn_ret)
  then Infer_err ErrLifetimeLeak
  else (match infer_core fenv n (params_ctx f.fn_params) f.fn_body with
        | Infer_ok p ->
          let (t_body, _UU0393__out) = p in
          if negb (wf_type_b _UU0394_ t_body)
          then Infer_err ErrLifetimeLeak
          else if ty_core_eqb (ty_core t_body) (ty_core f.fn_ret)
               then if usage_eqb (ty_usage t_body) (ty_usage f.fn_ret)
                    then if params_ok_b f.fn_params _UU0393__out
                         then Infer_ok (f.fn_ret, _UU0393__out)
                         else Infer_err ErrContextCheckFailed
                    else Infer_err (ErrUsageMismatch ((ty_usage f.fn_ret),
                           (ty_usage t_body)))
               else Infer_err (ErrTypeMismatch ((ty_core f.fn_ret),
                      (ty_core t_body)))
        | Infer_err err -> Infer_err err)
