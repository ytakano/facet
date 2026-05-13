
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

(** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec add = Big_int_Z.add_big_int

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
| LBound of Big_int_Z.big_int

(** val lifetime_eqb : lifetime -> lifetime -> bool **)

let lifetime_eqb l1 l2 =
  match l1 with
  | LStatic -> (match l2 with
                | LStatic -> true
                | _ -> false)
  | LVar n1 -> (match l2 with
                | LVar n2 -> Nat.eqb n1 n2
                | _ -> false)
  | LBound n1 -> (match l2 with
                  | LBound n2 -> Nat.eqb n1 n2
                  | _ -> false)

type region_ctx = lifetime list

type outlives_ctx = (lifetime * lifetime) list

(** val outlives_direct_b : outlives_ctx -> lifetime -> lifetime -> bool **)

let outlives_direct_b _UU03a9_ a b =
  (||) (lifetime_eqb a b)
    (match a with
     | LStatic -> true
     | _ ->
       existsb (fun pat ->
         let (x, y) = pat in (&&) (lifetime_eqb a x) (lifetime_eqb b y))
         _UU03a9_)

(** val outlives_b_fuel :
    Big_int_Z.big_int -> outlives_ctx -> lifetime -> lifetime -> bool **)

let rec outlives_b_fuel fuel _UU03a9_ a b =
  (||) (outlives_direct_b _UU03a9_ a b)
    ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
       (fun _ -> false)
       (fun fuel' ->
       existsb (fun pat ->
         let (x, y) = pat in
         (&&) (lifetime_eqb a x) (outlives_b_fuel fuel' _UU03a9_ y b))
         _UU03a9_)
       fuel)

(** val outlives_b : outlives_ctx -> lifetime -> lifetime -> bool **)

let outlives_b _UU03a9_ a b =
  outlives_b_fuel (length _UU03a9_) _UU03a9_ a b

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
| TForall of Big_int_Z.big_int * outlives_ctx * 'a
| TRef of lifetime * ref_kind * 'a

type ty =
| MkTy of usage * ty typeCore

(** val ty_usage : ty -> usage **)

let ty_usage = function
| MkTy (u, _) -> u

(** val ty_core : ty -> ty typeCore **)

let ty_core = function
| MkTy (_, c) -> c

(** val ref_usage_ok_b : usage -> ref_kind -> bool **)

let ref_usage_ok_b u = function
| RShared -> true
| RUnique -> (match u with
              | UUnrestricted -> false
              | _ -> true)

(** val apply_lt_lifetime : lifetime list -> lifetime -> lifetime **)

let rec apply_lt_lifetime _UU03c3_ = function
| LVar i -> (match nth_error _UU03c3_ i with
             | Some l' -> l'
             | None -> LVar i)
| x -> x

(** val apply_lt_outlives : lifetime list -> outlives_ctx -> outlives_ctx **)

let apply_lt_outlives _UU03c3_ _UU03a9_ =
  map (fun pat ->
    let (a, b) = pat in
    ((apply_lt_lifetime _UU03c3_ a), (apply_lt_lifetime _UU03c3_ b))) _UU03a9_

(** val close_fn_lifetime : Big_int_Z.big_int -> lifetime -> lifetime **)

let close_fn_lifetime m l = match l with
| LVar i -> if Nat.ltb i m then LBound i else l
| _ -> l

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
   | TForall (n, _UU03a9_, body) ->
     MkTy (u, (TForall (n, (apply_lt_outlives _UU03c3_ _UU03a9_),
       (apply_lt_ty _UU03c3_ body))))
   | TRef (l, rk, t1) ->
     MkTy (u, (TRef ((apply_lt_lifetime _UU03c3_ l), rk,
       (apply_lt_ty _UU03c3_ t1))))
   | x -> MkTy (u, x))

(** val map_lifetimes_ty : (lifetime -> lifetime) -> ty -> ty **)

let rec map_lifetimes_ty f = function
| MkTy (u, t0) ->
  (match t0 with
   | TFn (ts, r) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (map_lifetimes_ty f x) :: (go xs')
       in go
     in
     MkTy (u, (TFn ((go ts), (map_lifetimes_ty f r))))
   | TForall (n, _UU03a9_, body) ->
     MkTy (u, (TForall (n,
       (map (fun pat -> let (a, b) = pat in ((f a), (f b))) _UU03a9_),
       (map_lifetimes_ty f body))))
   | TRef (l, rk, t1) -> MkTy (u, (TRef ((f l), rk, (map_lifetimes_ty f t1))))
   | x -> MkTy (u, x))

(** val close_fn_ty : Big_int_Z.big_int -> ty -> ty **)

let close_fn_ty m t =
  map_lifetimes_ty (close_fn_lifetime m) t

(** val close_fn_outlives :
    Big_int_Z.big_int -> outlives_ctx -> outlives_ctx **)

let close_fn_outlives m _UU03a9_ =
  map (fun pat ->
    let (a, b) = pat in ((close_fn_lifetime m a), (close_fn_lifetime m b)))
    _UU03a9_

(** val open_bound_lifetime : lifetime option list -> lifetime -> lifetime **)

let open_bound_lifetime _UU03c3_ l = match l with
| LBound i ->
  (match nth_error _UU03c3_ i with
   | Some o -> (match o with
                | Some l' -> l'
                | None -> LBound i)
   | None -> LBound i)
| _ -> l

(** val open_bound_ty : lifetime option list -> ty -> ty **)

let open_bound_ty _UU03c3_ t =
  map_lifetimes_ty (open_bound_lifetime _UU03c3_) t

(** val open_bound_outlives :
    lifetime option list -> outlives_ctx -> outlives_ctx **)

let open_bound_outlives _UU03c3_ _UU03a9_ =
  map (fun pat ->
    let (a, b) = pat in
    ((open_bound_lifetime _UU03c3_ a), (open_bound_lifetime _UU03c3_ b)))
    _UU03a9_

(** val contains_lbound_lifetime : lifetime -> bool **)

let contains_lbound_lifetime = function
| LBound _ -> true
| _ -> false

(** val contains_lbound_outlives : outlives_ctx -> bool **)

let contains_lbound_outlives _UU03a9_ =
  existsb (fun pat ->
    let (a, b) = pat in
    (||) (contains_lbound_lifetime a) (contains_lbound_lifetime b)) _UU03a9_

(** val contains_lbound_ty : ty -> bool **)

let rec contains_lbound_ty = function
| MkTy (_, t0) ->
  (match t0 with
   | TFn (ts, r) ->
     (||) (existsb contains_lbound_ty ts) (contains_lbound_ty r)
   | TForall (_, _UU03a9_, body) ->
     (||) (contains_lbound_outlives _UU03a9_) (contains_lbound_ty body)
   | TRef (l, _, t1) ->
     (||) (contains_lbound_lifetime l) (contains_lbound_ty t1)
   | _ -> false)

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
| EFn of ident
| ECall of ident * expr list
| ECallExpr of expr * expr list
| EReplace of place * expr
| EAssign of place * expr
| EBorrow of ref_kind * place
| EDeref of expr
| EDrop of expr
| EIf of expr * expr * expr

(** val expr_as_place : expr -> place option **)

let rec expr_as_place = function
| EVar x -> Some (PVar x)
| EDeref e' ->
  (match expr_as_place e' with
   | Some p -> Some (PDeref p)
   | None -> None)
| _ -> None

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type fn_def = { fn_name : ident; fn_lifetimes : Big_int_Z.big_int;
                fn_outlives : outlives_ctx; fn_params : param list;
                fn_ret : ty; fn_body : expr }

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

(** val fn_value_ty : fn_def -> ty **)

let fn_value_ty f =
  let m = f.fn_lifetimes in
  let body =
    close_fn_ty m (MkTy (UUnrestricted, (TFn
      ((map (fun p -> p.param_ty) f.fn_params), f.fn_ret))))
  in
  ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
     (fun _ -> body)
     (fun _ -> MkTy (UUnrestricted, (TForall (m,
     (close_fn_outlives m f.fn_outlives), body))))
     m)

(** val place_root : place -> ident **)

let rec place_root = function
| PVar x -> x
| PDeref q -> place_root q

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

(** val expr_ref_root : expr -> ident option **)

let rec expr_ref_root = function
| EVar r -> Some r
| EDeref e' -> expr_ref_root e'
| _ -> None

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

(** val lifetime_pair_eqb :
    (lifetime * lifetime) -> (lifetime * lifetime) -> bool **)

let lifetime_pair_eqb p1 p2 =
  (&&) (lifetime_eqb (fst p1) (fst p2)) (lifetime_eqb (snd p1) (snd p2))

(** val outlives_ctx_eqb : outlives_ctx -> outlives_ctx -> bool **)

let rec outlives_ctx_eqb _UU03a9_1 _UU03a9_2 =
  match _UU03a9_1 with
  | [] -> (match _UU03a9_2 with
           | [] -> true
           | _ :: _ -> false)
  | p1 :: _UU03a9_1' ->
    (match _UU03a9_2 with
     | [] -> false
     | p2 :: _UU03a9_2' ->
       (&&) (lifetime_pair_eqb p1 p2) (outlives_ctx_eqb _UU03a9_1' _UU03a9_2'))

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
     | TForall (n1, _UU03a9_1, b1) ->
       (match c2 with
        | TForall (n2, _UU03a9_2, b2) ->
          (&&) ((&&) (Nat.eqb n1 n2) (outlives_ctx_eqb _UU03a9_1 _UU03a9_2))
            (ty_eqb b1 b2)
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
  | TForall (n1, _UU03a9_1, b1) ->
    (match c2 with
     | TForall (n2, _UU03a9_2, b2) ->
       (&&) ((&&) (Nat.eqb n1 n2) (outlives_ctx_eqb _UU03a9_1 _UU03a9_2))
         (ty_eqb b1 b2)
     | _ -> false)
  | TRef (l1, k1, t1) ->
    (match c2 with
     | TRef (l2, k2, t2) ->
       (&&) ((&&) (lifetime_eqb l1 l2) (ref_kind_eqb k1 k2)) (ty_eqb t1 t2)
     | _ -> false)

(** val ty_depth : ty -> Big_int_Z.big_int **)

let rec ty_depth = function
| MkTy (_, c) ->
  (match c with
   | TFn (ts, r) ->
     Big_int_Z.succ_big_int
       (let rec go = function
        | [] -> ty_depth r
        | t0 :: l' -> add (Big_int_Z.succ_big_int (ty_depth t0)) (go l')
        in go ts)
   | TForall (_, _UU03a9_, body) ->
     Big_int_Z.succ_big_int (add (length _UU03a9_) (ty_depth body))
   | TRef (_, _, t0) -> Big_int_Z.succ_big_int (ty_depth t0)
   | _ -> Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

(** val ty_compatible_args_contra_b_fuel :
    (outlives_ctx -> ty -> ty -> bool) -> outlives_ctx -> ty list -> ty list
    -> bool **)

let rec ty_compatible_args_contra_b_fuel compat _UU03a9_ actual expected =
  match actual with
  | [] -> (match expected with
           | [] -> true
           | _ :: _ -> false)
  | a :: actual' ->
    (match expected with
     | [] -> false
     | e :: expected' ->
       (&&) (compat _UU03a9_ e a)
         (ty_compatible_args_contra_b_fuel compat _UU03a9_ actual' expected'))

(** val ty_compatible_b_fuel :
    Big_int_Z.big_int -> outlives_ctx -> ty -> ty -> bool **)

let rec ty_compatible_b_fuel fuel _UU03a9_ t_actual t_expected =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> false)
    (fun fuel' ->
    (&&) (usage_sub_bool (ty_usage t_actual) (ty_usage t_expected))
      (match ty_core t_actual with
       | TUnits ->
         let ca = TUnits in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n, (p :: l), tb)))
          | x -> ty_core_eqb ca x)
       | TIntegers ->
         let ca = TIntegers in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n, (p :: l), tb)))
          | x -> ty_core_eqb ca x)
       | TFloats ->
         let ca = TFloats in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n, (p :: l), tb)))
          | x -> ty_core_eqb ca x)
       | TBooleans ->
         let ca = TBooleans in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n, (p :: l), tb)))
          | x -> ty_core_eqb ca x)
       | TNamed s ->
         let ca = TNamed s in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n, (p :: l), tb)))
          | x -> ty_core_eqb ca x)
       | TFn (params_a, ret_a) ->
         let ca = TFn (params_a, ret_a) in
         (match ty_core t_expected with
          | TFn (params_e, ret_e) ->
            (&&)
              (ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel')
                _UU03a9_ params_a params_e)
              (ty_compatible_b_fuel fuel' _UU03a9_ ret_a ret_e)
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n, (p :: l), tb)))
          | x -> ty_core_eqb ca x)
       | TForall (na, _UU03a9_a, ta) ->
         let ca = TForall (na, _UU03a9_a, ta) in
         (match ty_core t_expected with
          | TForall (nb, _UU03a9_b, tb) ->
            (&&)
              ((&&) (Nat.eqb na nb) (outlives_ctx_eqb _UU03a9_a _UU03a9_b))
              (ty_compatible_b_fuel fuel' _UU03a9_ ta tb)
          | x -> ty_core_eqb ca x)
       | TRef (la, rka, ta) ->
         let ca = TRef (la, rka, ta) in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n, (p :: l), tb)))
          | TRef (lb, rkb, tb) ->
            (&&) ((&&) (outlives_b _UU03a9_ la lb) (ref_kind_eqb rka rkb))
              (ty_compatible_b_fuel fuel' _UU03a9_ ta tb)
          | x -> ty_core_eqb ca x)))
    fuel

(** val ty_compatible_b : outlives_ctx -> ty -> ty -> bool **)

let ty_compatible_b _UU03a9_ t_actual t_expected =
  ty_compatible_b_fuel (add (ty_depth t_actual) (ty_depth t_expected))
    _UU03a9_ t_actual t_expected

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

(** val wf_lifetime_at_b :
    Big_int_Z.big_int -> region_ctx -> lifetime -> bool **)

let wf_lifetime_at_b bound_depth _UU0394_ l = match l with
| LStatic -> true
| LVar _ -> existsb (lifetime_eqb l) _UU0394_
| LBound i -> Nat.ltb i bound_depth

(** val wf_outlives_at_b :
    Big_int_Z.big_int -> region_ctx -> outlives_ctx -> bool **)

let wf_outlives_at_b bound_depth _UU0394_ _UU03a9_ =
  forallb (fun pat ->
    let (a, b) = pat in
    (&&) (wf_lifetime_at_b bound_depth _UU0394_ a)
      (wf_lifetime_at_b bound_depth _UU0394_ b))
    _UU03a9_

(** val wf_type_at_b : Big_int_Z.big_int -> region_ctx -> ty -> bool **)

let rec wf_type_at_b bound_depth _UU0394_ = function
| MkTy (u, t0) ->
  (match t0 with
   | TFn (ts, r) ->
     (&&) (forallb (wf_type_at_b bound_depth _UU0394_) ts)
       (wf_type_at_b bound_depth _UU0394_ r)
   | TForall (n, _UU03a9_, body) ->
     (&&) (wf_outlives_at_b (add n bound_depth) _UU0394_ _UU03a9_)
       (wf_type_at_b (add n bound_depth) _UU0394_ body)
   | TRef (l, rk, t_inner) ->
     (&&)
       ((&&) (ref_usage_ok_b u rk) (wf_lifetime_at_b bound_depth _UU0394_ l))
       (wf_type_at_b bound_depth _UU0394_ t_inner)
   | _ -> true)

(** val wf_lifetime_b : region_ctx -> lifetime -> bool **)

let wf_lifetime_b _UU0394_ l =
  wf_lifetime_at_b Big_int_Z.zero_big_int _UU0394_ l

(** val wf_type_b : region_ctx -> ty -> bool **)

let wf_type_b _UU0394_ t =
  wf_type_at_b Big_int_Z.zero_big_int _UU0394_ t

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
| ErrNotAFunction of ty typeCore
| ErrBorrowConflict of ident
| ErrLifetimeLeak
| ErrLifetimeConflict
| ErrHrtBoundUnsatisfied
| ErrHrtUnresolvedBound
| ErrHrtMonomorphicUsedBound
| ErrMalformedHrtBody of ty typeCore

(** val compatible_error : ty -> ty -> infer_error **)

let compatible_error t_actual t_expected =
  match ty_core t_actual with
  | TFn (_, _) ->
    (match ty_core t_expected with
     | TForall (_, _, body) ->
       if contains_lbound_ty body
       then ErrHrtMonomorphicUsedBound
       else ErrTypeMismatch ((ty_core t_actual), (ty_core t_expected))
     | _ ->
       if ty_core_eqb (ty_core t_actual) (ty_core t_expected)
       then ErrUsageMismatch ((ty_usage t_actual), (ty_usage t_expected))
       else ErrTypeMismatch ((ty_core t_actual), (ty_core t_expected)))
  | _ ->
    if ty_core_eqb (ty_core t_actual) (ty_core t_expected)
    then ErrUsageMismatch ((ty_usage t_actual), (ty_usage t_expected))
    else ErrTypeMismatch ((ty_core t_actual), (ty_core t_expected))

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
   | TForall (_, o, body) ->
     (match o with
      | [] ->
        if negb (contains_lbound_ty body)
        then unify_lt m _UU03c3_ body t_e
        else if ty_core_eqb (ty_core t_param) (ty_core t_e)
             then Some _UU03c3_
             else None
      | _ :: _ ->
        if ty_core_eqb (ty_core t_param) (ty_core t_e)
        then Some _UU03c3_
        else None)
   | TRef (l_p, rk, t_p_inner) ->
     let MkTy (_, t0) = t_e in
     (match t0 with
      | TRef (l_a, rk', t_e_inner) ->
        if negb (ref_kind_eqb rk rk')
        then None
        else (match l_p with
              | LVar i ->
                if Nat.ltb i m
                then (match lt_subst_vec_add _UU03c3_ i l_a with
                      | Some _UU03c3_' ->
                        unify_lt m _UU03c3_' t_p_inner t_e_inner
                      | None -> None)
                else if lifetime_eqb (LVar i) l_a
                     then unify_lt m _UU03c3_ t_p_inner t_e_inner
                     else None
              | x ->
                if lifetime_eqb x l_a
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

(** val bound_subst_vec_add :
    lifetime option list -> Big_int_Z.big_int -> lifetime -> lifetime option
    list option **)

let bound_subst_vec_add =
  lt_subst_vec_add

(** val unify_bound_lt :
    lifetime option list -> ty -> ty -> lifetime option list option **)

let rec unify_bound_lt _UU03c3_ t_param t_e =
  let MkTy (_, t) = t_param in
  (match t with
   | TFn (ps, pr) ->
     let MkTy (_, t0) = t_e in
     (match t0 with
      | TFn (es, er) ->
        let rec go _UU03c3_0 ps0 es0 =
          match ps0 with
          | [] ->
            (match es0 with
             | [] -> unify_bound_lt _UU03c3_0 pr er
             | _ :: _ -> None)
          | p :: ps' ->
            (match es0 with
             | [] -> None
             | e :: es' ->
               (match unify_bound_lt _UU03c3_0 p e with
                | Some _UU03c3_' -> go _UU03c3_' ps' es'
                | None -> None))
        in go _UU03c3_ ps es
      | _ -> None)
   | TRef (l_p, rk, t_p_inner) ->
     let MkTy (_, t0) = t_e in
     (match t0 with
      | TRef (l_a, rk', t_e_inner) ->
        if negb (ref_kind_eqb rk rk')
        then None
        else (match l_p with
              | LBound i ->
                (match bound_subst_vec_add _UU03c3_ i l_a with
                 | Some _UU03c3_' ->
                   unify_bound_lt _UU03c3_' t_p_inner t_e_inner
                 | None -> None)
              | _ ->
                if lifetime_eqb l_p l_a
                then unify_bound_lt _UU03c3_ t_p_inner t_e_inner
                else None)
      | _ -> None)
   | _ ->
     if ty_core_eqb (ty_core t_param) (ty_core t_e)
     then Some _UU03c3_
     else None)

(** val build_bound_sigma :
    lifetime option list -> ty list -> ty list -> lifetime option list option **)

let rec build_bound_sigma _UU03c3__acc arg_tys params =
  match arg_tys with
  | [] -> (match params with
           | [] -> Some _UU03c3__acc
           | _ :: _ -> None)
  | t :: ts ->
    (match params with
     | [] -> None
     | p :: ps ->
       (match unify_bound_lt _UU03c3__acc p t with
        | Some _UU03c3_' -> build_bound_sigma _UU03c3_' ts ps
        | None -> None))

(** val check_args :
    outlives_ctx -> ty list -> param list -> infer_error option **)

let rec check_args _UU03a9_ arg_tys params =
  match arg_tys with
  | [] -> (match params with
           | [] -> None
           | _ :: _ -> Some ErrArityMismatch)
  | t :: ts ->
    (match params with
     | [] -> Some ErrArityMismatch
     | p :: ps ->
       if ty_compatible_b _UU03a9_ t p.param_ty
       then check_args _UU03a9_ ts ps
       else Some (compatible_error t p.param_ty))

(** val check_arg_tys :
    outlives_ctx -> ty list -> ty list -> infer_error option **)

let rec check_arg_tys _UU03a9_ arg_tys params =
  match arg_tys with
  | [] -> (match params with
           | [] -> None
           | _ :: _ -> Some ErrArityMismatch)
  | t :: ts ->
    (match params with
     | [] -> Some ErrArityMismatch
     | p :: ps ->
       if ty_compatible_b _UU03a9_ t p
       then check_arg_tys _UU03a9_ ts ps
       else Some (compatible_error t p))

type 'a infer_result =
| Infer_ok of 'a
| Infer_err of infer_error

(** val infer_place : ctx -> place -> ty infer_result **)

let rec infer_place _UU0393_ = function
| PVar x ->
  (match ctx_lookup_b x _UU0393_ with
   | Some p0 ->
     let (t, b) = p0 in
     if b then Infer_err (ErrAlreadyConsumed x) else Infer_ok t
   | None -> Infer_err (ErrUnknownVar x))
| PDeref q ->
  (match infer_place _UU0393_ q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TRef (_, _, t) -> Infer_ok t
      | x -> Infer_err (ErrNotAReference x))
   | Infer_err err -> Infer_err err)

(** val wf_outlives_b : region_ctx -> outlives_ctx -> bool **)

let wf_outlives_b _UU0394_ _UU03a9_ =
  wf_outlives_at_b Big_int_Z.zero_big_int _UU0394_ _UU03a9_

(** val outlives_constraints_hold_b : outlives_ctx -> outlives_ctx -> bool **)

let outlives_constraints_hold_b _UU03a9_ constraints =
  forallb (fun pat -> let (a, b) = pat in outlives_b _UU03a9_ a b) constraints

(** val infer_core :
    fn_def list -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
    (ty * ctx) infer_result **)

let rec infer_core fenv _UU03a9_ n _UU0393_ = function
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
  (match infer_core fenv _UU03a9_ n _UU0393_ e1 with
   | Infer_ok p ->
     let (t1, _UU0393_1) = p in
     if ty_compatible_b _UU03a9_ t1 t
     then (match infer_core fenv _UU03a9_ n (ctx_add_b x t m _UU0393_1) e2 with
           | Infer_ok p0 ->
             let (t2, _UU0393_2) = p0 in
             if ctx_check_ok x t _UU0393_2
             then Infer_ok (t2, (ctx_remove_b x _UU0393_2))
             else Infer_err ErrContextCheckFailed
           | Infer_err err -> Infer_err err)
     else Infer_err (compatible_error t1 t)
   | Infer_err err -> Infer_err err)
| ELetInfer (m, x, e1, e2) ->
  (match infer_core fenv _UU03a9_ n _UU0393_ e1 with
   | Infer_ok p ->
     let (t1, _UU0393_1) = p in
     (match infer_core fenv _UU03a9_ n (ctx_add_b x t1 m _UU0393_1) e2 with
      | Infer_ok p0 ->
        let (t2, _UU0393_2) = p0 in
        if ctx_check_ok x t1 _UU0393_2
        then Infer_ok (t2, (ctx_remove_b x _UU0393_2))
        else Infer_err ErrContextCheckFailed
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| EFn fname ->
  (match lookup_fn_b fname fenv with
   | Some fdef -> Infer_ok ((fn_value_ty fdef), _UU0393_)
   | None -> Infer_err (ErrFunctionNotFound fname))
| ECall (fname, args) ->
  (match lookup_fn_b fname fenv with
   | Some fdef ->
     let m = fdef.fn_lifetimes in
     let collect =
       let rec collect _UU0393_0 = function
       | [] -> Infer_ok ([], _UU0393_0)
       | e' :: es ->
         (match infer_core fenv _UU03a9_ n _UU0393_0 e' with
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
           (match check_args _UU03a9_ arg_tys ps_subst with
            | Some err -> Infer_err err
            | None ->
              if forallb (wf_lifetime_b (mk_region_ctx n)) _UU03c3_
              then let _UU03a9__subst =
                     apply_lt_outlives _UU03c3_ fdef.fn_outlives
                   in
                   if outlives_constraints_hold_b _UU03a9_ _UU03a9__subst
                   then Infer_ok ((apply_lt_ty _UU03c3_ fdef.fn_ret),
                          _UU0393_')
                   else Infer_err ErrHrtBoundUnsatisfied
              else Infer_err ErrLifetimeLeak)
         | None -> Infer_err ErrLifetimeConflict)
      | Infer_err err -> Infer_err err)
   | None -> Infer_err (ErrFunctionNotFound fname))
| ECallExpr (callee, args) ->
  (match infer_core fenv _UU03a9_ n _UU0393_ callee with
   | Infer_ok p ->
     let (t_callee, _UU0393_c) = p in
     let collect =
       let rec collect _UU0393_0 = function
       | [] -> Infer_ok ([], _UU0393_0)
       | e' :: es ->
         (match infer_core fenv _UU03a9_ n _UU0393_0 e' with
          | Infer_ok p0 ->
            let (t_e, _UU0393_1) = p0 in
            (match collect _UU0393_1 es with
             | Infer_ok p1 ->
               let (tys, _UU0393_2) = p1 in Infer_ok ((t_e :: tys), _UU0393_2)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       in collect
     in
     (match collect _UU0393_c args with
      | Infer_ok p0 ->
        let (arg_tys, _UU0393_') = p0 in
        (match ty_core t_callee with
         | TFn (param_tys, ret) ->
           (match check_arg_tys _UU03a9_ arg_tys param_tys with
            | Some err -> Infer_err err
            | None -> Infer_ok (ret, _UU0393_'))
         | TForall (m, bounds, body) ->
           (match ty_core body with
            | TFn (param_tys, ret) ->
              (match build_bound_sigma (repeat None m) arg_tys param_tys with
               | Some _UU03c3_ ->
                 let param_tys_open = map (open_bound_ty _UU03c3_) param_tys
                 in
                 (match check_arg_tys _UU03a9_ arg_tys param_tys_open with
                  | Some err -> Infer_err err
                  | None ->
                    let ret_open = open_bound_ty _UU03c3_ ret in
                    let bounds_open = open_bound_outlives _UU03c3_ bounds in
                    if (||) (contains_lbound_ty ret_open)
                         (contains_lbound_outlives bounds_open)
                    then Infer_err ErrHrtUnresolvedBound
                    else if outlives_constraints_hold_b _UU03a9_ bounds_open
                         then Infer_ok (ret_open, _UU0393_')
                         else Infer_err ErrHrtBoundUnsatisfied)
               | None -> Infer_err ErrLifetimeConflict)
            | x -> Infer_err (ErrMalformedHrtBody x))
         | x -> Infer_err (ErrNotAFunction x))
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| EReplace (p0, e_new) ->
  (match p0 with
   | PVar x ->
     (match ctx_lookup_b x _UU0393_ with
      | Some p ->
        let (t_x, b) = p in
        if b
        then Infer_err (ErrAlreadyConsumed x)
        else (match ctx_lookup_mut_b x _UU0393_ with
              | Some m ->
                (match m with
                 | MImmutable -> Infer_err (ErrNotMutable x)
                 | MMutable ->
                   (match infer_core fenv _UU03a9_ n _UU0393_ e_new with
                    | Infer_ok p1 ->
                      let (t_new, _UU0393_') = p1 in
                      if ty_compatible_b _UU03a9_ t_new t_x
                      then Infer_ok (t_x, _UU0393_')
                      else Infer_err (compatible_error t_new t_x)
                    | Infer_err err -> Infer_err err))
              | None -> Infer_err (ErrUnknownVar x))
      | None -> Infer_err (ErrUnknownVar x))
   | PDeref p ->
     (match infer_place _UU0393_ p with
      | Infer_ok t_p ->
        (match ty_core t_p with
         | TRef (l, r, t_inner) ->
           (match r with
            | RShared ->
              Infer_err (ErrNotAReference (TRef (l, RShared, t_inner)))
            | RUnique ->
              (match infer_core fenv _UU03a9_ n _UU0393_ e_new with
               | Infer_ok p1 ->
                 let (t_new, _UU0393_') = p1 in
                 if ty_compatible_b _UU03a9_ t_new t_inner
                 then Infer_ok (t_inner, _UU0393_')
                 else Infer_err (compatible_error t_new t_inner)
               | Infer_err err -> Infer_err err))
         | x -> Infer_err (ErrNotAReference x))
      | Infer_err err -> Infer_err err))
| EAssign (p0, e_new) ->
  (match p0 with
   | PVar x ->
     (match ctx_lookup_b x _UU0393_ with
      | Some p ->
        let (t_x, b) = p in
        if b
        then Infer_err (ErrAlreadyConsumed x)
        else (match ctx_lookup_mut_b x _UU0393_ with
              | Some m ->
                (match m with
                 | MImmutable -> Infer_err (ErrNotMutable x)
                 | MMutable ->
                   if usage_eqb (ty_usage t_x) ULinear
                   then Infer_err (ErrUsageMismatch ((ty_usage t_x), UAffine))
                   else (match infer_core fenv _UU03a9_ n _UU0393_ e_new with
                         | Infer_ok p1 ->
                           let (t_new, _UU0393_') = p1 in
                           if ty_compatible_b _UU03a9_ t_new t_x
                           then Infer_ok ((MkTy (UUnrestricted, TUnits)),
                                  _UU0393_')
                           else Infer_err (compatible_error t_new t_x)
                         | Infer_err err -> Infer_err err))
              | None -> Infer_err (ErrUnknownVar x))
      | None -> Infer_err (ErrUnknownVar x))
   | PDeref p ->
     (match infer_place _UU0393_ p with
      | Infer_ok t_p ->
        (match ty_core t_p with
         | TRef (l, r, t_inner) ->
           (match r with
            | RShared ->
              Infer_err (ErrNotAReference (TRef (l, RShared, t_inner)))
            | RUnique ->
              if usage_eqb (ty_usage t_inner) ULinear
              then Infer_err (ErrUsageMismatch ((ty_usage t_inner), UAffine))
              else (match infer_core fenv _UU03a9_ n _UU0393_ e_new with
                    | Infer_ok p1 ->
                      let (t_new, _UU0393_') = p1 in
                      if ty_compatible_b _UU03a9_ t_new t_inner
                      then Infer_ok ((MkTy (UUnrestricted, TUnits)),
                             _UU0393_')
                      else Infer_err (compatible_error t_new t_inner)
                    | Infer_err err -> Infer_err err))
         | x -> Infer_err (ErrNotAReference x))
      | Infer_err err -> Infer_err err))
| EBorrow (rk, p0) ->
  (match rk with
   | RShared ->
     (match p0 with
      | PVar x ->
        (match ctx_lookup_b x _UU0393_ with
         | Some p ->
           let (t_x, b) = p in
           if b
           then Infer_err (ErrAlreadyConsumed x)
           else (match rk with
                 | RShared ->
                   Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar n), RShared,
                     t_x)))), _UU0393_)
                 | RUnique ->
                   (match ctx_lookup_mut_b x _UU0393_ with
                    | Some m ->
                      (match m with
                       | MImmutable -> Infer_err (ErrImmutableBorrow x)
                       | MMutable ->
                         Infer_ok ((MkTy (UAffine, (TRef ((LVar n), RUnique,
                           t_x)))), _UU0393_))
                    | None -> Infer_err (ErrImmutableBorrow x)))
         | None -> Infer_err (ErrUnknownVar x))
      | PDeref p ->
        (match infer_place _UU0393_ p with
         | Infer_ok t_p ->
           (match ty_core t_p with
            | TRef (_, _, t_inner) ->
              Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar n), RShared,
                t_inner)))), _UU0393_)
            | x -> Infer_err (ErrNotAReference x))
         | Infer_err err -> Infer_err err))
   | RUnique ->
     (match p0 with
      | PVar x ->
        (match ctx_lookup_b x _UU0393_ with
         | Some p ->
           let (t_x, b) = p in
           if b
           then Infer_err (ErrAlreadyConsumed x)
           else (match rk with
                 | RShared ->
                   Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar n), RShared,
                     t_x)))), _UU0393_)
                 | RUnique ->
                   (match ctx_lookup_mut_b x _UU0393_ with
                    | Some m ->
                      (match m with
                       | MImmutable -> Infer_err (ErrImmutableBorrow x)
                       | MMutable ->
                         Infer_ok ((MkTy (UAffine, (TRef ((LVar n), RUnique,
                           t_x)))), _UU0393_))
                    | None -> Infer_err (ErrImmutableBorrow x)))
         | None -> Infer_err (ErrUnknownVar x))
      | PDeref p ->
        (match infer_place _UU0393_ p with
         | Infer_ok t_p ->
           (match ty_core t_p with
            | TRef (l, r, t_inner) ->
              (match r with
               | RShared ->
                 Infer_err (ErrNotAReference (TRef (l, RShared, t_inner)))
               | RUnique ->
                 Infer_ok ((MkTy (UAffine, (TRef ((LVar n), RUnique,
                   t_inner)))), _UU0393_))
            | x -> Infer_err (ErrNotAReference x))
         | Infer_err err -> Infer_err err)))
| EDeref r ->
  (match expr_as_place r with
   | Some p ->
     (match infer_place _UU0393_ p with
      | Infer_ok t_r ->
        (match ty_core t_r with
         | TRef (_, _, t_inner) ->
           if usage_eqb (ty_usage t_inner) UUnrestricted
           then Infer_ok (t_inner, _UU0393_)
           else Infer_err (ErrUsageMismatch ((ty_usage t_inner),
                  UUnrestricted))
         | x -> Infer_err (ErrNotAReference x))
      | Infer_err err -> Infer_err err)
   | None ->
     (match infer_core fenv _UU03a9_ n _UU0393_ r with
      | Infer_ok p ->
        let (t_r, _UU0393_') = p in
        (match ty_core t_r with
         | TRef (_, _, t_inner) ->
           if usage_eqb (ty_usage t_inner) UUnrestricted
           then Infer_ok (t_inner, _UU0393_')
           else Infer_err (ErrUsageMismatch ((ty_usage t_inner),
                  UUnrestricted))
         | x -> Infer_err (ErrNotAReference x))
      | Infer_err err -> Infer_err err))
| EDrop e1 ->
  (match infer_core fenv _UU03a9_ n _UU0393_ e1 with
   | Infer_ok p ->
     let (_, _UU0393_') = p in
     Infer_ok ((MkTy (UUnrestricted, TUnits)), _UU0393_')
   | Infer_err err -> Infer_err err)
| EIf (e1, e2, e3) ->
  (match infer_core fenv _UU03a9_ n _UU0393_ e1 with
   | Infer_ok p ->
     let (t_cond, _UU0393_1) = p in
     if ty_core_eqb (ty_core t_cond) TBooleans
     then (match infer_core fenv _UU03a9_ n _UU0393_1 e2 with
           | Infer_ok p0 ->
             let (t2, _UU0393_2) = p0 in
             (match infer_core fenv _UU03a9_ n _UU0393_1 e3 with
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
    fn_def list -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
    (ty * ctx) infer_result **)

let infer_body =
  infer_core

(** val params_ok_b : param list -> ctx -> bool **)

let rec params_ok_b ps _UU0393_ =
  match ps with
  | [] -> true
  | p :: ps' ->
    (&&) (ctx_check_ok p.param_name p.param_ty _UU0393_)
      (params_ok_b ps' _UU0393_)

(** val wf_params_b : region_ctx -> param list -> bool **)

let rec wf_params_b _UU0394_ = function
| [] -> true
| p :: ps' -> (&&) (wf_type_b _UU0394_ p.param_ty) (wf_params_b _UU0394_ ps')

(** val infer : fn_def list -> fn_def -> (ty * ctx) infer_result **)

let infer fenv f =
  let n = f.fn_lifetimes in
  let _UU03a9_ = f.fn_outlives in
  let _UU0394_ = mk_region_ctx n in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_outlives_b _UU0394_ _UU03a9_)
       then Infer_err ErrLifetimeLeak
       else if negb (wf_type_b _UU0394_ f.fn_ret)
            then Infer_err ErrLifetimeLeak
            else if negb (wf_params_b _UU0394_ f.fn_params)
                 then Infer_err ErrLifetimeLeak
                 else (match infer_body fenv _UU03a9_ n
                               (params_ctx f.fn_params) f.fn_body with
                       | Infer_ok p ->
                         let (t_body, _UU0393__out) = p in
                         if negb (wf_type_b _UU0394_ t_body)
                         then Infer_err ErrLifetimeLeak
                         else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                              then if params_ok_b f.fn_params _UU0393__out
                                   then Infer_ok (f.fn_ret, _UU0393__out)
                                   else Infer_err ErrContextCheckFailed
                              else Infer_err
                                     (compatible_error t_body f.fn_ret)
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
| ECallExpr (callee, args) ->
  (match borrow_check fenv bS _UU0393_ callee with
   | Infer_ok bS1 ->
     let rec go bS0 = function
     | [] -> Infer_ok bS0
     | a :: rest ->
       (match borrow_check fenv bS0 _UU0393_ a with
        | Infer_ok bS2 -> go bS2 rest
        | Infer_err err -> Infer_err err)
     in go bS1 args
   | Infer_err err -> Infer_err err)
| EReplace (p0, e_new) ->
  (match p0 with
   | PVar _ -> borrow_check fenv bS _UU0393_ e_new
   | PDeref p ->
     let r = place_root p in
     if bs_has_any r bS
     then Infer_err (ErrBorrowConflict r)
     else borrow_check fenv bS _UU0393_ e_new)
| EAssign (p0, e_new) ->
  (match p0 with
   | PVar _ -> borrow_check fenv bS _UU0393_ e_new
   | PDeref p ->
     let r = place_root p in
     if bs_has_any r bS
     then Infer_err (ErrBorrowConflict r)
     else borrow_check fenv bS _UU0393_ e_new)
| EBorrow (r, p0) ->
  (match r with
   | RShared ->
     (match p0 with
      | PVar x ->
        if bs_has_mut x bS
        then Infer_err (ErrBorrowConflict x)
        else Infer_ok ((BEShared x) :: bS)
      | PDeref p ->
        let r0 = place_root p in
        if bs_has_mut r0 bS
        then Infer_err (ErrBorrowConflict r0)
        else Infer_ok ((BEShared r0) :: bS))
   | RUnique ->
     (match p0 with
      | PVar x ->
        if bs_has_any x bS
        then Infer_err (ErrBorrowConflict x)
        else Infer_ok ((BEMut x) :: bS)
      | PDeref p ->
        let r0 = place_root p in
        if bs_has_any r0 bS
        then Infer_err (ErrBorrowConflict r0)
        else Infer_ok ((BEMut r0) :: bS)))
| EDeref e1 ->
  (match expr_ref_root e1 with
   | Some r ->
     if bs_has_mut r bS
     then Infer_err (ErrBorrowConflict r)
     else borrow_check fenv bS _UU0393_ e1
   | None -> borrow_check fenv bS _UU0393_ e1)
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
  let _UU03a9_ = f.fn_outlives in
  let _UU0394_ = mk_region_ctx n in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_outlives_b _UU0394_ _UU03a9_)
       then Infer_err ErrLifetimeLeak
       else if negb (wf_type_b _UU0394_ f.fn_ret)
            then Infer_err ErrLifetimeLeak
            else if negb (wf_params_b _UU0394_ f.fn_params)
                 then Infer_err ErrLifetimeLeak
                 else (match infer_core fenv _UU03a9_ n
                               (params_ctx f.fn_params) f.fn_body with
                       | Infer_ok p ->
                         let (t_body, _UU0393__out) = p in
                         if negb (wf_type_b _UU0394_ t_body)
                         then Infer_err ErrLifetimeLeak
                         else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                              then if params_ok_b f.fn_params _UU0393__out
                                   then Infer_ok (f.fn_ret, _UU0393__out)
                                   else Infer_err ErrContextCheckFailed
                              else Infer_err
                                     (compatible_error t_body f.fn_ret)
                       | Infer_err err -> Infer_err err)
