
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

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

(** val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec add = Big_int_Z.add_big_int

(** val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec sub = (fun n m -> Big_int_Z.max_big_int Big_int_Z.zero_big_int
  (Big_int_Z.sub_big_int n m))

(** val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let rec eqb n m =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ ->
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> true)
      (fun _ -> false)
      m)
    (fun n' ->
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> false)
      (fun m' -> eqb n' m')
      m)
    n

(** val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let rec leb n m =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> true)
    (fun n' ->
    (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
      (fun _ -> false)
      (fun m' -> leb n' m')
      m)
    n

(** val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool **)

let ltb n m =
  leb (Big_int_Z.succ_big_int n) m

(** val tail_add :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec tail_add n m =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> m)
    (fun n0 -> tail_add n0 (Big_int_Z.succ_big_int m))
    n

(** val tail_addmul :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int **)

let rec tail_addmul r n m =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> r)
    (fun n0 -> tail_addmul (tail_add m r) n0 m)
    n

(** val tail_mul :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let tail_mul n m =
  tail_addmul Big_int_Z.zero_big_int n m

(** val of_uint_acc : uint -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec of_uint_acc d acc =
  match d with
  | Nil -> acc
  | D0 d0 ->
    of_uint_acc d0
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))) acc))))))))))

(** val of_uint : uint -> Big_int_Z.big_int **)

let of_uint d =
  of_uint_acc d Big_int_Z.zero_big_int

(** val of_hex_uint_acc : uint0 -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil0 -> acc
  | D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc)
  | D11 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc))
  | D12 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc)))
  | D13 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc))))
  | D14 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc)))))
  | D15 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc))))))
  | D16 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc)))))))
  | D17 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc))))))))
  | D18 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc)))))))))
  | D19 d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
      (Big_int_Z.succ_big_int
      (tail_mul (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        (Big_int_Z.succ_big_int (Big_int_Z.succ_big_int
        Big_int_Z.zero_big_int)))))))))))))))) acc))))))))))))))))

(** val of_hex_uint : uint0 -> Big_int_Z.big_int **)

let of_hex_uint d =
  of_hex_uint_acc d Big_int_Z.zero_big_int

(** val of_num_uint : uint1 -> Big_int_Z.big_int **)

let of_num_uint = function
| UIntDecimal d0 -> of_uint d0
| UIntHexadecimal d0 -> of_hex_uint d0

(** val eqb0 : bool -> bool -> bool **)

let eqb0 b1 b2 =
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

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: l0 -> f b (fold_right f a0 l0)

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
| TParam of Big_int_Z.big_int
| TStruct of string * lifetime list * 'a list
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
   | TStruct (name, lts, args) ->
     let map_lt =
       let rec map_lt = function
       | [] -> []
       | x :: xs' -> (apply_lt_ty _UU03c3_ x) :: (map_lt xs')
       in map_lt
     in
     MkTy (u, (TStruct (name, (map (apply_lt_lifetime _UU03c3_) lts),
     (map_lt args))))
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
   | TStruct (name, lts, args) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (map_lifetimes_ty f x) :: (go xs')
       in go
     in
     MkTy (u, (TStruct (name, (map f lts), (go args))))
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
   | TStruct (_, lts, args) ->
     (||) (existsb contains_lbound_lifetime lts)
       (existsb contains_lbound_ty args)
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
| PField of place * string

type expr =
| EUnit
| ELit of literal
| EVar of ident
| ELet of mutability * ident * ty * expr * expr
| ELetInfer of mutability * ident * expr * expr
| EFn of ident
| EPlace of place
| ECall of ident * expr list
| ECallExpr of expr * expr list
| EStruct of string * lifetime list * ty list * (string * expr) list
| EReplace of place * expr
| EAssign of place * expr
| EBorrow of ref_kind * place
| EDeref of expr
| EDrop of expr
| EIf of expr * expr * expr

(** val expr_as_place : expr -> place option **)

let rec expr_as_place = function
| EVar x -> Some (PVar x)
| EPlace p -> Some p
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

type field_path = string list

(** val path_segment_eqb : string -> string -> bool **)

let path_segment_eqb =
  (=)

(** val path_eqb : field_path -> field_path -> bool **)

let rec path_eqb p q =
  match p with
  | [] -> (match q with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match q with
     | [] -> false
     | y :: ys -> (&&) (path_segment_eqb x y) (path_eqb xs ys))

(** val path_prefix_b : field_path -> field_path -> bool **)

let rec path_prefix_b prefix path =
  match prefix with
  | [] -> true
  | x :: xs ->
    (match path with
     | [] -> false
     | y :: ys -> (&&) (path_segment_eqb x y) (path_prefix_b xs ys))

(** val path_conflict_b : field_path -> field_path -> bool **)

let path_conflict_b p q =
  (||) (path_prefix_b p q) (path_prefix_b q p)

(** val path_conflicts_any_b : field_path -> field_path list -> bool **)

let rec path_conflicts_any_b p = function
| [] -> false
| q :: rest -> (||) (path_conflict_b p q) (path_conflicts_any_b p rest)

(** val remove_restored_paths :
    field_path -> field_path list -> field_path list **)

let rec remove_restored_paths p = function
| [] -> []
| q :: rest ->
  if path_prefix_b p q
  then remove_restored_paths p rest
  else q :: (remove_restored_paths p rest)

type binding_state = { st_consumed : bool; st_moved_paths : field_path list }

(** val binding_state_of_bool : bool -> binding_state **)

let binding_state_of_bool b =
  { st_consumed = b; st_moved_paths = [] }

(** val binding_available_b : binding_state -> field_path -> bool **)

let binding_available_b st p =
  (&&) (negb st.st_consumed) (negb (path_conflicts_any_b p st.st_moved_paths))

(** val state_consume_path : field_path -> binding_state -> binding_state **)

let state_consume_path p st =
  match p with
  | [] -> { st_consumed = true; st_moved_paths = st.st_moved_paths }
  | _ :: _ ->
    { st_consumed = st.st_consumed; st_moved_paths =
      (p :: st.st_moved_paths) }

(** val state_restore_path : field_path -> binding_state -> binding_state **)

let state_restore_path p st =
  { st_consumed = st.st_consumed; st_moved_paths =
    (remove_restored_paths p st.st_moved_paths) }

(** val place_path : place -> (ident * field_path) option **)

let rec place_path = function
| PVar x -> Some (x, [])
| PDeref _ -> None
| PField (q, f) ->
  (match place_path q with
   | Some p0 -> let (x, path) = p0 in Some (x, (app path (f :: [])))
   | None -> None)

(** val place_suffix_path : place -> field_path **)

let rec place_suffix_path = function
| PField (q, f) -> app (place_suffix_path q) (f :: [])
| _ -> []

type field_def = { field_name : string; field_mutability : mutability;
                   field_ty : ty }

type trait_ref = { trait_ref_name : string; trait_ref_args : ty list }

type trait_bound = { bound_type_index : Big_int_Z.big_int;
                     bound_traits : trait_ref list }

type struct_def = { struct_name : string;
                    struct_lifetimes : Big_int_Z.big_int;
                    struct_type_params : Big_int_Z.big_int;
                    struct_bounds : trait_bound list;
                    struct_fields : field_def list }

type trait_def = { trait_name : string;
                   trait_type_params : Big_int_Z.big_int;
                   trait_bounds : trait_bound list }

type impl_def = { impl_lifetimes : Big_int_Z.big_int;
                  impl_type_params : Big_int_Z.big_int;
                  impl_trait_name : string; impl_trait_args : ty list;
                  impl_for_ty : ty }

type global_env = { env_structs : struct_def list;
                    env_traits : trait_def list; env_impls : impl_def list;
                    env_fns : fn_def list }

(** val lookup_struct_in : string -> struct_def list -> struct_def option **)

let rec lookup_struct_in name = function
| [] -> None
| s :: rest ->
  if (=) name s.struct_name then Some s else lookup_struct_in name rest

(** val lookup_struct : string -> global_env -> struct_def option **)

let lookup_struct name env =
  lookup_struct_in name env.env_structs

(** val lookup_field : string -> field_def list -> field_def option **)

let rec lookup_field name = function
| [] -> None
| f :: rest ->
  if (=) name f.field_name then Some f else lookup_field name rest

(** val lookup_trait_in : string -> trait_def list -> trait_def option **)

let rec lookup_trait_in name = function
| [] -> None
| t :: rest ->
  if (=) name t.trait_name then Some t else lookup_trait_in name rest

(** val lookup_trait : string -> global_env -> trait_def option **)

let lookup_trait name env =
  lookup_trait_in name env.env_traits

(** val subst_type_params_ty : ty list -> ty -> ty **)

let rec subst_type_params_ty _UU03c3_ = function
| MkTy (u, t0) ->
  (match t0 with
   | TParam i ->
     (match nth_error _UU03c3_ i with
      | Some t' -> MkTy (u, (ty_core t'))
      | None -> MkTy (u, (TParam i)))
   | TStruct (name, lts, args) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (subst_type_params_ty _UU03c3_ x) :: (go xs')
       in go
     in
     MkTy (u, (TStruct (name, lts, (go args))))
   | TFn (ps, r) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (subst_type_params_ty _UU03c3_ x) :: (go xs')
       in go
     in
     MkTy (u, (TFn ((go ps), (subst_type_params_ty _UU03c3_ r))))
   | TForall (n, _UU03a9_, body) ->
     MkTy (u, (TForall (n, _UU03a9_, (subst_type_params_ty _UU03c3_ body))))
   | TRef (l, rk, inner) ->
     MkTy (u, (TRef (l, rk, (subst_type_params_ty _UU03c3_ inner))))
   | x -> MkTy (u, x))

(** val instantiate_struct_field_ty :
    lifetime list -> ty list -> field_def -> ty **)

let instantiate_struct_field_ty lifetime_args type_args f =
  subst_type_params_ty type_args (apply_lt_ty lifetime_args f.field_ty)

(** val usage_eqb_decl : usage -> usage -> bool **)

let usage_eqb_decl u1 u2 =
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

(** val ref_kind_eqb_decl : ref_kind -> ref_kind -> bool **)

let ref_kind_eqb_decl k1 k2 =
  match k1 with
  | RShared -> (match k2 with
                | RShared -> true
                | RUnique -> false)
  | RUnique -> (match k2 with
                | RShared -> false
                | RUnique -> true)

(** val lifetime_list_eqb_decl : lifetime list -> lifetime list -> bool **)

let rec lifetime_list_eqb_decl l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match l2 with
     | [] -> false
     | y :: ys -> (&&) (lifetime_eqb x y) (lifetime_list_eqb_decl xs ys))

(** val outlives_ctx_eqb_decl : outlives_ctx -> outlives_ctx -> bool **)

let rec outlives_ctx_eqb_decl _UU03a9_1 _UU03a9_2 =
  match _UU03a9_1 with
  | [] -> (match _UU03a9_2 with
           | [] -> true
           | _ :: _ -> false)
  | p :: xs ->
    let (a1, b1) = p in
    (match _UU03a9_2 with
     | [] -> false
     | p0 :: ys ->
       let (a2, b2) = p0 in
       (&&) ((&&) (lifetime_eqb a1 a2) (lifetime_eqb b1 b2))
         (outlives_ctx_eqb_decl xs ys))

(** val ty_eqb_decl : ty -> ty -> bool **)

let rec ty_eqb_decl t1 t2 =
  let MkTy (u1, c1) = t1 in
  let MkTy (u2, c2) = t2 in
  (&&) (usage_eqb_decl u1 u2)
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
     | TParam i1 -> (match c2 with
                     | TParam i2 -> eqb i1 i2
                     | _ -> false)
     | TStruct (n1, lts1, args1) ->
       (match c2 with
        | TStruct (n2, lts2, args2) ->
          (&&) ((&&) ((=) n1 n2) (lifetime_list_eqb_decl lts1 lts2))
            (let rec go xs ys =
               match xs with
               | [] -> (match ys with
                        | [] -> true
                        | _ :: _ -> false)
               | x :: xs' ->
                 (match ys with
                  | [] -> false
                  | y :: ys' -> (&&) (ty_eqb_decl x y) (go xs' ys'))
             in go args1 args2)
        | _ -> false)
     | TFn (ps1, r1) ->
       (match c2 with
        | TFn (ps2, r2) ->
          (&&)
            (let rec go xs ys =
               match xs with
               | [] -> (match ys with
                        | [] -> true
                        | _ :: _ -> false)
               | x :: xs' ->
                 (match ys with
                  | [] -> false
                  | y :: ys' -> (&&) (ty_eqb_decl x y) (go xs' ys'))
             in go ps1 ps2)
            (ty_eqb_decl r1 r2)
        | _ -> false)
     | TForall (n1, _UU03a9_1, b1) ->
       (match c2 with
        | TForall (n2, _UU03a9_2, b2) ->
          (&&) ((&&) (eqb n1 n2) (outlives_ctx_eqb_decl _UU03a9_1 _UU03a9_2))
            (ty_eqb_decl b1 b2)
        | _ -> false)
     | TRef (l1, rk1, t3) ->
       (match c2 with
        | TRef (l2, rk2, t4) ->
          (&&) ((&&) (lifetime_eqb l1 l2) (ref_kind_eqb_decl rk1 rk2))
            (ty_eqb_decl t3 t4)
        | _ -> false))

type type_subst = ty option list

type lifetime_subst = lifetime option list

(** val repeat_none : Big_int_Z.big_int -> 'a1 option list **)

let rec repeat_none n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun n' -> None :: (repeat_none n'))
    n

(** val list_set_nth : Big_int_Z.big_int -> 'a1 -> 'a1 list -> 'a1 list **)

let rec list_set_nth i v xs =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> match xs with
              | [] -> []
              | _ :: rest -> v :: rest)
    (fun i' ->
    match xs with
    | [] -> []
    | x :: rest -> x :: (list_set_nth i' v rest))
    i

(** val bind_type_param :
    Big_int_Z.big_int -> ty -> type_subst -> type_subst option **)

let bind_type_param i t _UU03c3_ =
  match nth_error _UU03c3_ i with
  | Some o ->
    (match o with
     | Some t' -> if ty_eqb_decl t t' then Some _UU03c3_ else None
     | None -> Some (list_set_nth i (Some t) _UU03c3_))
  | None -> None

(** val bind_lifetime_param :
    Big_int_Z.big_int -> lifetime -> lifetime_subst -> lifetime_subst option **)

let bind_lifetime_param i l _UU03c3_ =
  match nth_error _UU03c3_ i with
  | Some o ->
    (match o with
     | Some l' -> if lifetime_eqb l l' then Some _UU03c3_ else None
     | None -> Some (list_set_nth i (Some l) _UU03c3_))
  | None -> None

type impl_match_state = type_subst * lifetime_subst

(** val match_lifetime :
    Big_int_Z.big_int -> lifetime -> lifetime -> impl_match_state ->
    impl_match_state option **)

let match_lifetime lt_params pattern actual st = match st with
| (ty_UU03c3_, lt_UU03c3_) ->
  (match pattern with
   | LVar i ->
     if ltb i lt_params
     then (match bind_lifetime_param i actual lt_UU03c3_ with
           | Some lt_UU03c3_' -> Some (ty_UU03c3_, lt_UU03c3_')
           | None -> None)
     else if lifetime_eqb pattern actual then Some st else None
   | _ -> if lifetime_eqb pattern actual then Some st else None)

(** val match_lifetimes :
    Big_int_Z.big_int -> lifetime list -> lifetime list -> impl_match_state
    -> impl_match_state option **)

let rec match_lifetimes lt_params patterns actuals st =
  match patterns with
  | [] -> (match actuals with
           | [] -> Some st
           | _ :: _ -> None)
  | p :: ps ->
    (match actuals with
     | [] -> None
     | a :: as_ ->
       (match match_lifetime lt_params p a st with
        | Some st' -> match_lifetimes lt_params ps as_ st'
        | None -> None))

(** val match_ty :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> ty -> ty
    -> impl_match_state -> impl_match_state option **)

let rec match_ty ty_params lt_params fuel pattern actual st =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> None)
    (fun fuel' ->
    let MkTy (u_p, c_p) = pattern in
    (match c_p with
     | TParam i ->
       if ltb i ty_params
       then if usage_eqb_decl u_p (ty_usage actual)
            then let (ty_UU03c3_, lt_UU03c3_) = st in
                 (match bind_type_param i actual ty_UU03c3_ with
                  | Some ty_UU03c3_' -> Some (ty_UU03c3_', lt_UU03c3_)
                  | None -> None)
            else None
       else if ty_eqb_decl pattern actual then Some st else None
     | _ ->
       let MkTy (u_a, c_a) = actual in
       if negb (usage_eqb_decl u_p u_a)
       then None
       else (match c_p with
             | TUnits -> (match c_a with
                          | TUnits -> Some st
                          | _ -> None)
             | TIntegers -> (match c_a with
                             | TIntegers -> Some st
                             | _ -> None)
             | TFloats -> (match c_a with
                           | TFloats -> Some st
                           | _ -> None)
             | TBooleans -> (match c_a with
                             | TBooleans -> Some st
                             | _ -> None)
             | TNamed s1 ->
               (match c_a with
                | TNamed s2 -> if (=) s1 s2 then Some st else None
                | _ -> None)
             | TParam _ -> None
             | TStruct (n1, lts1, args1) ->
               (match c_a with
                | TStruct (n2, lts2, args2) ->
                  if (=) n1 n2
                  then (match match_lifetimes lt_params lts1 lts2 st with
                        | Some st' ->
                          match_tys ty_params lt_params fuel' args1 args2 st'
                        | None -> None)
                  else None
                | _ -> None)
             | TFn (ps1, r1) ->
               (match c_a with
                | TFn (ps2, r2) ->
                  (match match_tys ty_params lt_params fuel' ps1 ps2 st with
                   | Some st' -> match_ty ty_params lt_params fuel' r1 r2 st'
                   | None -> None)
                | _ -> None)
             | TForall (n1, _UU03a9_1, b1) ->
               (match c_a with
                | TForall (n2, _UU03a9_2, b2) ->
                  if (&&) (eqb n1 n2)
                       (outlives_ctx_eqb_decl _UU03a9_1 _UU03a9_2)
                  then match_ty ty_params lt_params fuel' b1 b2 st
                  else None
                | _ -> None)
             | TRef (l1, rk1, t1) ->
               (match c_a with
                | TRef (l2, rk2, t2) ->
                  if ref_kind_eqb_decl rk1 rk2
                  then (match match_lifetime lt_params l1 l2 st with
                        | Some st' ->
                          match_ty ty_params lt_params fuel' t1 t2 st'
                        | None -> None)
                  else None
                | _ -> None))))
    fuel

(** val match_tys :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> ty list ->
    ty list -> impl_match_state -> impl_match_state option **)

and match_tys ty_params lt_params fuel patterns actuals st =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> None)
    (fun fuel' ->
    match patterns with
    | [] -> (match actuals with
             | [] -> Some st
             | _ :: _ -> None)
    | p :: ps ->
      (match actuals with
       | [] -> None
       | a :: as_ ->
         (match match_ty ty_params lt_params fuel' p a st with
          | Some st' -> match_tys ty_params lt_params fuel' ps as_ st'
          | None -> None)))
    fuel

(** val ty_match_fuel : ty -> Big_int_Z.big_int **)

let rec ty_match_fuel = function
| MkTy (_, t0) ->
  (match t0 with
   | TStruct (_, lts, args) ->
     Big_int_Z.succ_big_int
       (add (length lts)
         (fold_right (fun t1 acc -> add (ty_match_fuel t1) acc)
           Big_int_Z.zero_big_int args))
   | TFn (ps, r) ->
     Big_int_Z.succ_big_int
       (add (ty_match_fuel r)
         (fold_right (fun t1 acc -> add (ty_match_fuel t1) acc)
           Big_int_Z.zero_big_int ps))
   | TForall (_, _UU03a9_, body) ->
     Big_int_Z.succ_big_int (add (length _UU03a9_) (ty_match_fuel body))
   | TRef (_, _, inner) -> Big_int_Z.succ_big_int (ty_match_fuel inner)
   | _ -> Big_int_Z.succ_big_int Big_int_Z.zero_big_int)

(** val impl_matches_b : string -> ty list -> ty -> impl_def -> bool **)

let impl_matches_b trait_name0 trait_args for_ty i =
  if negb ((=) trait_name0 i.impl_trait_name)
  then false
  else let st0 = ((repeat_none i.impl_type_params),
         (repeat_none i.impl_lifetimes))
       in
       let fuel = Big_int_Z.succ_big_int
         (add
           (add (add (ty_match_fuel for_ty) (ty_match_fuel i.impl_for_ty))
             (fold_right (fun t acc -> add (ty_match_fuel t) acc)
               Big_int_Z.zero_big_int trait_args))
           (fold_right (fun t acc -> add (ty_match_fuel t) acc)
             Big_int_Z.zero_big_int i.impl_trait_args))
       in
       (match match_tys i.impl_type_params i.impl_lifetimes fuel
                i.impl_trait_args trait_args st0 with
        | Some st1 ->
          (match match_ty i.impl_type_params i.impl_lifetimes fuel
                   i.impl_for_ty for_ty st1 with
           | Some _ -> true
           | None -> false)
        | None -> false)

(** val matching_impls :
    string -> ty list -> ty -> impl_def list -> impl_def list **)

let rec matching_impls trait_name0 trait_args for_ty = function
| [] -> []
| i :: rest ->
  let rest' = matching_impls trait_name0 trait_args for_ty rest in
  if impl_matches_b trait_name0 trait_args for_ty i then i :: rest' else rest'

type ctx_entry = ((ident * ty) * binding_state) * mutability

type ctx = ctx_entry list

(** val ctx_lookup_state : ident -> ctx -> (ty * binding_state) option **)

let rec ctx_lookup_state x = function
| [] -> None
| c :: t ->
  let (p, _) = c in
  let (p0, st) = p in
  let (n, t0) = p0 in
  if ident_eqb x n then Some (t0, st) else ctx_lookup_state x t

(** val ctx_update_state :
    ident -> (binding_state -> binding_state) -> ctx -> ctx option **)

let rec ctx_update_state x f = function
| [] -> None
| c :: t ->
  let (p, m) = c in
  let (p0, st) = p in
  let (n, t0) = p0 in
  if ident_eqb x n
  then Some ((((n, t0), (f st)), m) :: t)
  else (match ctx_update_state x f t with
        | Some t' -> Some ((((n, t0), st), m) :: t')
        | None -> None)

(** val ctx_lookup_mut : ident -> ctx -> mutability option **)

let rec ctx_lookup_mut x = function
| [] -> None
| c :: t ->
  let (p, m) = c in
  let (p0, _) = p in
  let (n, _) = p0 in if ident_eqb x n then Some m else ctx_lookup_mut x t

(** val ctx_add : ident -> ty -> mutability -> ctx -> ctx **)

let ctx_add x t m _UU0393_ =
  (((x, t), (binding_state_of_bool false)), m) :: _UU0393_

(** val ctx_remove : ident -> ctx -> ctx **)

let rec ctx_remove x = function
| [] -> []
| c :: t ->
  let (p, m) = c in
  let (p0, st) = p in
  let (n, t0) = p0 in
  if ident_eqb x n then t else (((n, t0), st), m) :: (ctx_remove x t)

(** val param_ctx_entry : param -> ctx_entry **)

let param_ctx_entry p =
  (((p.param_name, p.param_ty), (binding_state_of_bool false)),
    p.param_mutability)

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
    let (p0, st2) = p in
    let (n, t) = p0 in
    (match _UU0393_3 with
     | [] -> None
     | c0 :: t3 ->
       let (p1, _) = c0 in
       let (p2, st3) = p1 in
       let (n', _) = p2 in
       if negb (ident_eqb n n')
       then None
       else (match ctx_merge t2 t3 with
             | Some rest ->
               (match ty_usage t with
                | ULinear ->
                  if eqb0 st2.st_consumed st3.st_consumed
                  then Some ((((n, t), { st_consumed = st2.st_consumed;
                         st_moved_paths =
                         (app st2.st_moved_paths st3.st_moved_paths) }),
                         m) :: rest)
                  else None
                | _ ->
                  Some ((((n, t), { st_consumed =
                    ((||) st2.st_consumed st3.st_consumed); st_moved_paths =
                    (app st2.st_moved_paths st3.st_moved_paths) }),
                    m) :: rest))
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
| PField (q, _) -> place_root q

(** val apply_lt_param : lifetime list -> param -> param **)

let apply_lt_param _UU03c3_ p =
  { param_mutability = p.param_mutability; param_name = p.param_name;
    param_ty = (apply_lt_ty _UU03c3_ p.param_ty) }

(** val apply_lt_params : lifetime list -> param list -> param list **)

let apply_lt_params _UU03c3_ ps =
  map (apply_lt_param _UU03c3_) ps

(** val expr_ref_root : expr -> ident option **)

let rec expr_ref_root = function
| EVar r -> Some r
| EPlace p -> Some (place_root p)
| EDeref e' -> expr_ref_root e'
| _ -> None

(** val place_name : place -> ident **)

let rec place_name = function
| PVar x -> x
| PDeref q -> place_name q
| PField (q, _) -> place_name q

type root_set = ident list

type root_env = (ident * root_set) list

(** val root_set_union : root_set -> root_set -> root_set **)

let rec root_set_union a b =
  match a with
  | [] -> b
  | x :: xs ->
    if existsb (ident_eqb x) b
    then root_set_union xs b
    else x :: (root_set_union xs b)

(** val root_sets_union : root_set list -> root_set **)

let rec root_sets_union = function
| [] -> []
| roots :: rest -> root_set_union roots (root_sets_union rest)

(** val root_env_lookup : ident -> root_env -> root_set option **)

let rec root_env_lookup x = function
| [] -> None
| p :: rest ->
  let (y, roots) = p in
  if ident_eqb x y then Some roots else root_env_lookup x rest

(** val root_env_add : ident -> root_set -> root_env -> root_env **)

let root_env_add x roots r =
  (x, roots) :: r

(** val root_env_update : ident -> root_set -> root_env -> root_env **)

let rec root_env_update x roots = function
| [] -> []
| p :: rest ->
  let (y, roots_y) = p in
  if ident_eqb x y
  then (y, roots) :: rest
  else (y, roots_y) :: (root_env_update x roots rest)

(** val root_env_remove : ident -> root_env -> root_env **)

let rec root_env_remove x = function
| [] -> []
| p :: rest ->
  let (y, roots) = p in
  if ident_eqb x y then rest else (y, roots) :: (root_env_remove x rest)

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

(** val lifetime_list_eqb : lifetime list -> lifetime list -> bool **)

let rec lifetime_list_eqb l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _ :: _ -> false)
  | lt1 :: l1' ->
    (match l2 with
     | [] -> false
     | lt2 :: l2' -> (&&) (lifetime_eqb lt1 lt2) (lifetime_list_eqb l1' l2'))

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
     | TParam i1 -> (match c2 with
                     | TParam i2 -> Nat.eqb i1 i2
                     | _ -> false)
     | TStruct (name1, lts1, args1) ->
       (match c2 with
        | TStruct (name2, lts2, args2) ->
          (&&) ((&&) ((=) name1 name2) (lifetime_list_eqb lts1 lts2))
            (let rec go_args l1 l2 =
               match l1 with
               | [] -> (match l2 with
                        | [] -> true
                        | _ :: _ -> false)
               | t3 :: l1' ->
                 (match l2 with
                  | [] -> false
                  | t4 :: l2' -> (&&) (ty_eqb t3 t4) (go_args l1' l2'))
             in go_args args1 args2)
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
  | TParam i1 -> (match c2 with
                  | TParam i2 -> Nat.eqb i1 i2
                  | _ -> false)
  | TStruct (name1, lts1, args1) ->
    (match c2 with
     | TStruct (name2, lts2, args2) ->
       (&&) ((&&) ((=) name1 name2) (lifetime_list_eqb lts1 lts2))
         (let rec go_args l1 l2 =
            match l1 with
            | [] -> (match l2 with
                     | [] -> true
                     | _ :: _ -> false)
            | t1 :: l1' ->
              (match l2 with
               | [] -> false
               | t2 :: l2' -> (&&) (ty_eqb t1 t2) (go_args l1' l2'))
          in go_args args1 args2)
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
   | TStruct (_, lts, args) ->
     Big_int_Z.succ_big_int
       (add (length lts)
         (let rec go = function
          | [] -> Big_int_Z.zero_big_int
          | t0 :: l' -> add (Big_int_Z.succ_big_int (ty_depth t0)) (go l')
          in go args))
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
       | TParam n ->
         let ca = TParam n in
         (match ty_core t_expected with
          | TForall (n0, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n0, (p :: l), tb)))
          | x -> ty_core_eqb ca x)
       | TStruct (s, l, l0) ->
         let ca = TStruct (s, l, l0) in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l1 -> ty_core_eqb ca (TForall (n, (p :: l1), tb)))
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
              (match rka with
               | RShared -> ty_compatible_b_fuel fuel' _UU03a9_ ta tb
               | RUnique -> ty_eqb ta tb)
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
  let (p0, st) = p in
  let (n, t0) = p0 in
  if ident_eqb x n then Some (t0, st.st_consumed) else ctx_lookup_b x t

(** val ctx_add_b : ident -> ty -> mutability -> ctx -> ctx **)

let ctx_add_b x t m _UU0393_ =
  (((x, t), (binding_state_of_bool false)), m) :: _UU0393_

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
   | TStruct (_, lts, args) ->
     (&&) (forallb (wf_lifetime_at_b bound_depth _UU0394_) lts)
       (forallb (wf_type_at_b bound_depth _UU0394_) args)
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
| ErrDuplicateParam of ident
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
| ErrStructNotFound of string
| ErrFieldNotFound of string
| ErrDuplicateField of string
| ErrMissingField of string
| ErrTraitImplNotFound of string * ty
| ErrTraitImplAmbiguous of string * ty

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

(** val trait_impl_error_with_args :
    global_env -> string -> ty list -> ty -> infer_error option **)

let trait_impl_error_with_args env trait_name0 trait_args for_ty =
  match lookup_trait trait_name0 env with
  | Some t ->
    if negb (Nat.eqb (length trait_args) t.trait_type_params)
    then Some ErrArityMismatch
    else (match matching_impls trait_name0 trait_args for_ty env.env_impls with
          | [] -> Some (ErrTraitImplNotFound (trait_name0, for_ty))
          | _ :: l ->
            (match l with
             | [] -> None
             | _ :: _ -> Some (ErrTraitImplAmbiguous (trait_name0, for_ty))))
  | None -> Some (ErrTraitImplNotFound (trait_name0, for_ty))

(** val instantiate_trait_ref : ty list -> trait_ref -> trait_ref **)

let instantiate_trait_ref args tr =
  { trait_ref_name = tr.trait_ref_name; trait_ref_args =
    (map (subst_type_params_ty args) tr.trait_ref_args) }

(** val check_trait_ref_for_ty :
    global_env -> trait_ref -> ty -> infer_error option **)

let check_trait_ref_for_ty env tr for_ty =
  trait_impl_error_with_args env tr.trait_ref_name tr.trait_ref_args for_ty

(** val check_trait_refs_for_ty :
    global_env -> trait_ref list -> ty -> infer_error option **)

let rec check_trait_refs_for_ty env traits for_ty =
  match traits with
  | [] -> None
  | tr :: rest ->
    (match check_trait_ref_for_ty env tr for_ty with
     | Some err -> Some err
     | None -> check_trait_refs_for_ty env rest for_ty)

(** val check_struct_bounds :
    global_env -> trait_bound list -> ty list -> infer_error option **)

let rec check_struct_bounds env bounds args =
  match bounds with
  | [] -> None
  | b :: rest ->
    (match nth_error args b.bound_type_index with
     | Some for_ty ->
       let traits = map (instantiate_trait_ref args) b.bound_traits in
       (match check_trait_refs_for_ty env traits for_ty with
        | Some err -> Some err
        | None -> check_struct_bounds env rest args)
     | None -> Some ErrArityMismatch)

(** val list_set_nth0 : Big_int_Z.big_int -> 'a1 -> 'a1 list -> 'a1 list **)

let rec list_set_nth0 i v l =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> match l with
              | [] -> []
              | _ :: t -> v :: t)
    (fun i' -> match l with
               | [] -> []
               | h :: t -> h :: (list_set_nth0 i' v t))
    i

(** val lt_subst_vec_add :
    lifetime option list -> Big_int_Z.big_int -> lifetime -> lifetime option
    list option **)

let lt_subst_vec_add _UU03c3_ i l_a =
  match nth_error _UU03c3_ i with
  | Some o ->
    (match o with
     | Some l' -> if lifetime_eqb l' l_a then Some _UU03c3_ else None
     | None -> Some (list_set_nth0 i (Some l_a) _UU03c3_))
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

(** val lookup_field_b : string -> (string * expr) list -> expr option **)

let rec lookup_field_b name = function
| [] -> None
| y :: rest ->
  let (fname, e) = y in
  if (=) name fname then Some e else lookup_field_b name rest

(** val has_field_b : string -> (string * expr) list -> bool **)

let has_field_b name fields =
  match lookup_field_b name fields with
  | Some _ -> true
  | None -> false

(** val first_duplicate_field : (string * expr) list -> string option **)

let rec first_duplicate_field = function
| [] -> None
| y :: rest ->
  let (name, _) = y in
  if has_field_b name rest then Some name else first_duplicate_field rest

(** val first_unknown_field :
    (string * expr) list -> field_def list -> string option **)

let rec first_unknown_field fields defs =
  match fields with
  | [] -> None
  | p :: rest ->
    let (name, _) = p in
    (match lookup_field name defs with
     | Some _ -> first_unknown_field rest defs
     | None -> Some name)

(** val first_missing_field :
    field_def list -> (string * expr) list -> string option **)

let rec first_missing_field defs fields =
  match defs with
  | [] -> None
  | f :: rest ->
    if has_field_b f.field_name fields
    then first_missing_field rest fields
    else Some f.field_name

(** val infer_place_env : global_env -> ctx -> place -> ty infer_result **)

let rec infer_place_env env _UU0393_ = function
| PVar x ->
  (match ctx_lookup_b x _UU0393_ with
   | Some p0 ->
     let (t, b) = p0 in
     if b then Infer_err (ErrAlreadyConsumed x) else Infer_ok t
   | None -> Infer_err (ErrUnknownVar x))
| PDeref q ->
  (match infer_place_env env _UU0393_ q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TRef (_, _, t) -> Infer_ok t
      | x -> Infer_err (ErrNotAReference x))
   | Infer_err err -> Infer_err err)
| PField (q, field) ->
  (match infer_place_env env _UU0393_ q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TStruct (sname, lts, args) ->
        (match lookup_struct sname env with
         | Some s ->
           (match lookup_field field s.struct_fields with
            | Some f -> Infer_ok (instantiate_struct_field_ty lts args f)
            | None -> Infer_err (ErrFieldNotFound field))
         | None -> Infer_err (ErrStructNotFound sname))
      | x -> Infer_err (ErrTypeMismatch (x, (TStruct ("", [], [])))))
   | Infer_err err -> Infer_err err)

(** val wf_outlives_b : region_ctx -> outlives_ctx -> bool **)

let wf_outlives_b _UU0394_ _UU03a9_ =
  wf_outlives_at_b Big_int_Z.zero_big_int _UU0394_ _UU03a9_

(** val outlives_constraints_hold_b : outlives_ctx -> outlives_ctx -> bool **)

let outlives_constraints_hold_b _UU03a9_ constraints =
  forallb (fun pat -> let (a, b) = pat in outlives_b _UU03a9_ a b) constraints

type sctx = ctx

(** val sctx_of_ctx : ctx -> sctx **)

let sctx_of_ctx _UU0393_ =
  _UU0393_

(** val ctx_of_sctx : sctx -> ctx **)

let ctx_of_sctx _UU03a3_ =
  _UU03a3_

(** val sctx_lookup : ident -> sctx -> (ty * binding_state) option **)

let sctx_lookup =
  ctx_lookup_state

(** val sctx_lookup_mut : ident -> sctx -> mutability option **)

let sctx_lookup_mut =
  ctx_lookup_mut

(** val sctx_add : ident -> ty -> mutability -> sctx -> sctx **)

let sctx_add =
  ctx_add

(** val sctx_remove : ident -> sctx -> sctx **)

let sctx_remove =
  ctx_remove

(** val sctx_update_state :
    ident -> (binding_state -> binding_state) -> sctx -> sctx option **)

let sctx_update_state =
  ctx_update_state

(** val prefix_obligation_paths :
    field_path -> field_path list -> field_path list **)

let rec prefix_obligation_paths prefix = function
| [] -> []
| p :: rest -> (app prefix p) :: (prefix_obligation_paths prefix rest)

(** val linear_obligation_paths_fuel :
    Big_int_Z.big_int -> global_env -> ty -> field_path list **)

let rec linear_obligation_paths_fuel fuel env t =
  match ty_usage t with
  | ULinear ->
    (match ty_core t with
     | TStruct (sname, lts, args) ->
       ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
          (fun _ -> [] :: [])
          (fun fuel' ->
          match lookup_struct sname env with
          | Some s ->
            if (&&) (Nat.eqb (length lts) s.struct_lifetimes)
                 (Nat.eqb (length args) s.struct_type_params)
            then let go =
                   let rec go = function
                   | [] -> []
                   | f :: rest ->
                     app
                       (prefix_obligation_paths (f.field_name :: [])
                         (linear_obligation_paths_fuel fuel' env
                           (instantiate_struct_field_ty lts args f)))
                       (go rest)
                   in go
                 in
                 (match go s.struct_fields with
                  | [] -> [] :: []
                  | f :: l -> f :: l)
            else [] :: []
          | None -> [] :: [])
          fuel)
     | _ -> [] :: [])
  | _ -> []

(** val linear_obligation_paths : global_env -> ty -> field_path list **)

let linear_obligation_paths env t =
  linear_obligation_paths_fuel (Big_int_Z.succ_big_int
    (add (length env.env_structs) (ty_depth t))) env t

(** val moved_path_satisfies_obligation_b :
    field_path list -> field_path -> bool **)

let moved_path_satisfies_obligation_b moved_paths obligation =
  existsb (fun moved -> path_prefix_b moved obligation) moved_paths

(** val moved_paths_satisfy_obligations_b :
    field_path list -> field_path list -> bool **)

let rec moved_paths_satisfy_obligations_b moved_paths = function
| [] -> true
| obligation :: rest ->
  (&&) (moved_path_satisfies_obligation_b moved_paths obligation)
    (moved_paths_satisfy_obligations_b moved_paths rest)

(** val linear_scope_ok_b : global_env -> ty -> binding_state -> bool **)

let linear_scope_ok_b env t st =
  (||) st.st_consumed
    (moved_paths_satisfy_obligations_b st.st_moved_paths
      (linear_obligation_paths env t))

(** val sctx_check_ok : global_env -> ident -> ty -> sctx -> bool **)

let sctx_check_ok env x t _UU03a3_ =
  match ty_usage t with
  | ULinear ->
    (match sctx_lookup x _UU03a3_ with
     | Some p -> let (_, st) = p in linear_scope_ok_b env t st
     | None -> false)
  | _ -> true

(** val params_ok_sctx_b : global_env -> param list -> sctx -> bool **)

let rec params_ok_sctx_b env ps _UU03a3_ =
  match ps with
  | [] -> true
  | p :: rest ->
    (&&) (sctx_check_ok env p.param_name p.param_ty _UU03a3_)
      (params_ok_sctx_b env rest _UU03a3_)

(** val params_ok_env_b : global_env -> param list -> ctx -> bool **)

let params_ok_env_b env ps _UU0393_ =
  params_ok_sctx_b env ps (sctx_of_ctx _UU0393_)

(** val sctx_path_available :
    sctx -> ident -> field_path -> unit infer_result **)

let sctx_path_available _UU03a3_ x p =
  match sctx_lookup x _UU03a3_ with
  | Some p0 ->
    let (_, st) = p0 in
    if binding_available_b st p
    then Infer_ok ()
    else Infer_err (ErrAlreadyConsumed x)
  | None -> Infer_err (ErrUnknownVar x)

(** val sctx_consume_path :
    sctx -> ident -> field_path -> sctx infer_result **)

let sctx_consume_path _UU03a3_ x p =
  match sctx_path_available _UU03a3_ x p with
  | Infer_ok _ ->
    (match sctx_update_state x (state_consume_path p) _UU03a3_ with
     | Some _UU03a3_' -> Infer_ok _UU03a3_'
     | None -> Infer_err (ErrUnknownVar x))
  | Infer_err err -> Infer_err err

(** val sctx_restore_path :
    sctx -> ident -> field_path -> sctx infer_result **)

let sctx_restore_path _UU03a3_ x p =
  match sctx_update_state x (state_restore_path p) _UU03a3_ with
  | Some _UU03a3_' -> Infer_ok _UU03a3_'
  | None -> Infer_err (ErrUnknownVar x)

(** val infer_place_sctx : global_env -> sctx -> place -> ty infer_result **)

let rec infer_place_sctx env _UU03a3_ = function
| PVar x ->
  (match sctx_lookup x _UU03a3_ with
   | Some p0 ->
     let (t, st) = p0 in
     if binding_available_b st []
     then Infer_ok t
     else Infer_err (ErrAlreadyConsumed x)
   | None -> Infer_err (ErrUnknownVar x))
| PDeref q ->
  (match infer_place_sctx env _UU03a3_ q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TRef (_, _, t) -> Infer_ok t
      | x -> Infer_err (ErrNotAReference x))
   | Infer_err err -> Infer_err err)
| PField (q, field) ->
  (match infer_place_env env (ctx_of_sctx _UU03a3_) q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TStruct (sname, lts, args) ->
        (match lookup_struct sname env with
         | Some s ->
           (match lookup_field field s.struct_fields with
            | Some f ->
              (match place_path (PField (q, field)) with
               | Some p0 ->
                 let (x, path) = p0 in
                 (match sctx_path_available _UU03a3_ x path with
                  | Infer_ok _ ->
                    Infer_ok (instantiate_struct_field_ty lts args f)
                  | Infer_err err -> Infer_err err)
               | None -> Infer_ok (instantiate_struct_field_ty lts args f))
            | None -> Infer_err (ErrFieldNotFound field))
         | None -> Infer_err (ErrStructNotFound sname))
      | x -> Infer_err (ErrTypeMismatch (x, (TStruct ("", [], [])))))
   | Infer_err err -> Infer_err err)

(** val infer_place_type_sctx :
    global_env -> sctx -> place -> ty infer_result **)

let rec infer_place_type_sctx env _UU03a3_ = function
| PVar x ->
  (match sctx_lookup x _UU03a3_ with
   | Some p0 -> let (t, _) = p0 in Infer_ok t
   | None -> Infer_err (ErrUnknownVar x))
| PDeref q ->
  (match infer_place_type_sctx env _UU03a3_ q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TRef (_, _, t) -> Infer_ok t
      | x -> Infer_err (ErrNotAReference x))
   | Infer_err err -> Infer_err err)
| PField (q, field) ->
  (match infer_place_type_sctx env _UU03a3_ q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TStruct (sname, lts, args) ->
        (match lookup_struct sname env with
         | Some s ->
           (match lookup_field field s.struct_fields with
            | Some f -> Infer_ok (instantiate_struct_field_ty lts args f)
            | None -> Infer_err (ErrFieldNotFound field))
         | None -> Infer_err (ErrStructNotFound sname))
      | x -> Infer_err (ErrTypeMismatch (x, (TStruct ("", [], [])))))
   | Infer_err err -> Infer_err err)

(** val place_under_unique_ref_b : global_env -> sctx -> place -> bool **)

let rec place_under_unique_ref_b env _UU03a3_ = function
| PVar _ -> false
| PDeref q ->
  (match infer_place_sctx env _UU03a3_ q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TRef (_, r, _) -> (match r with
                           | RShared -> false
                           | RUnique -> true)
      | _ -> false)
   | Infer_err _ -> false)
| PField (q, _) -> place_under_unique_ref_b env _UU03a3_ q

(** val writable_place_b : global_env -> sctx -> place -> bool **)

let rec writable_place_b env _UU03a3_ = function
| PVar x ->
  (match sctx_lookup_mut x _UU03a3_ with
   | Some m -> (match m with
                | MImmutable -> false
                | MMutable -> true)
   | None -> false)
| PDeref q ->
  (match infer_place_sctx env _UU03a3_ q with
   | Infer_ok tq ->
     (match ty_core tq with
      | TRef (_, r, _) -> (match r with
                           | RShared -> false
                           | RUnique -> true)
      | _ -> false)
   | Infer_err _ -> false)
| PField (q, field) ->
  if writable_place_b env _UU03a3_ q
  then (match infer_place_type_sctx env _UU03a3_ q with
        | Infer_ok tq ->
          (match ty_core tq with
           | TStruct (sname, _, _) ->
             (match lookup_struct sname env with
              | Some s ->
                (match lookup_field field s.struct_fields with
                 | Some f ->
                   (match f.field_mutability with
                    | MImmutable -> false
                    | MMutable -> true)
                 | None -> false)
              | None -> false)
           | _ -> false)
        | Infer_err _ -> false)
  else false

(** val consume_place_value :
    global_env -> sctx -> place -> ty -> sctx infer_result **)

let consume_place_value _ _UU03a3_ p t =
  if usage_eqb (ty_usage t) UUnrestricted
  then Infer_ok _UU03a3_
  else (match place_path p with
        | Some p0 -> let (x, path) = p0 in sctx_consume_path _UU03a3_ x path
        | None -> Infer_err (ErrUsageMismatch ((ty_usage t), UUnrestricted)))

(** val usage_max_tys : ty list -> usage **)

let rec usage_max_tys = function
| [] -> UUnrestricted
| t :: rest -> usage_max (ty_usage t) (usage_max_tys rest)

(** val instantiate_struct_instance_ty :
    struct_def -> lifetime list -> ty list -> ty **)

let instantiate_struct_instance_ty s lifetime_args type_args =
  MkTy
    ((usage_max_tys
       (map (instantiate_struct_field_ty lifetime_args type_args)
         s.struct_fields)),
    (TStruct (s.struct_name, lifetime_args, type_args)))

(** val infer_core_env_state_fuel :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    sctx -> expr -> (ty * sctx) infer_result **)

let rec infer_core_env_state_fuel fuel env _UU03a9_ n _UU03a3_ e =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> Infer_err ErrNotImplemented)
    (fun fuel' ->
    match e with
    | EUnit -> Infer_ok ((MkTy (UUnrestricted, TUnits)), _UU03a3_)
    | ELit l ->
      (match l with
       | LInt _ -> Infer_ok ((MkTy (UUnrestricted, TIntegers)), _UU03a3_)
       | LFloat _ -> Infer_ok ((MkTy (UUnrestricted, TFloats)), _UU03a3_)
       | LBool _ -> Infer_ok ((MkTy (UUnrestricted, TBooleans)), _UU03a3_))
    | EVar x ->
      (match infer_place_sctx env _UU03a3_ (PVar x) with
       | Infer_ok t ->
         (match consume_place_value env _UU03a3_ (PVar x) t with
          | Infer_ok _UU03a3_' -> Infer_ok (t, _UU03a3_')
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | ELet (m, x, t, e1, e2) ->
      (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_ e1 with
       | Infer_ok p ->
         let (t1, _UU03a3_1) = p in
         if ty_compatible_b _UU03a9_ t1 t
         then (match infer_core_env_state_fuel fuel' env _UU03a9_ n
                       (sctx_add x t m _UU03a3_1) e2 with
               | Infer_ok p0 ->
                 let (t2, _UU03a3_2) = p0 in
                 if sctx_check_ok env x t _UU03a3_2
                 then Infer_ok (t2, (sctx_remove x _UU03a3_2))
                 else Infer_err ErrContextCheckFailed
               | Infer_err err -> Infer_err err)
         else Infer_err (compatible_error t1 t)
       | Infer_err err -> Infer_err err)
    | ELetInfer (m, x, e1, e2) ->
      (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_ e1 with
       | Infer_ok p ->
         let (t1, _UU03a3_1) = p in
         (match infer_core_env_state_fuel fuel' env _UU03a9_ n
                  (sctx_add x t1 m _UU03a3_1) e2 with
          | Infer_ok p0 ->
            let (t2, _UU03a3_2) = p0 in
            if sctx_check_ok env x t1 _UU03a3_2
            then Infer_ok (t2, (sctx_remove x _UU03a3_2))
            else Infer_err ErrContextCheckFailed
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | EFn fname ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef -> Infer_ok ((fn_value_ty fdef), _UU03a3_)
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EPlace p ->
      (match infer_place_sctx env _UU03a3_ p with
       | Infer_ok t ->
         (match consume_place_value env _UU03a3_ p t with
          | Infer_ok _UU03a3_' -> Infer_ok (t, _UU03a3_')
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | ECall (fname, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         let m = fdef.fn_lifetimes in
         let collect =
           let rec collect _UU03a3_0 = function
           | [] -> Infer_ok ([], _UU03a3_0)
           | e' :: es ->
             (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_0
                      e' with
              | Infer_ok p ->
                let (t_e, _UU03a3_1) = p in
                (match collect _UU03a3_1 es with
                 | Infer_ok p0 ->
                   let (tys, _UU03a3_2) = p0 in
                   Infer_ok ((t_e :: tys), _UU03a3_2)
                 | Infer_err err -> Infer_err err)
              | Infer_err err -> Infer_err err)
           in collect
         in
         (match collect _UU03a3_ args with
          | Infer_ok p ->
            let (arg_tys, _UU03a3_') = p in
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
                              _UU03a3_')
                       else Infer_err ErrHrtBoundUnsatisfied
                  else Infer_err ErrLifetimeLeak)
             | None -> Infer_err ErrLifetimeConflict)
          | Infer_err err -> Infer_err err)
       | None -> Infer_err (ErrFunctionNotFound fname))
    | ECallExpr (callee, args) ->
      (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_ callee with
       | Infer_ok p ->
         let (t_callee, _UU03a3_c) = p in
         let collect =
           let rec collect _UU03a3_0 = function
           | [] -> Infer_ok ([], _UU03a3_0)
           | e' :: es ->
             (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_0
                      e' with
              | Infer_ok p0 ->
                let (t_e, _UU03a3_1) = p0 in
                (match collect _UU03a3_1 es with
                 | Infer_ok p1 ->
                   let (tys, _UU03a3_2) = p1 in
                   Infer_ok ((t_e :: tys), _UU03a3_2)
                 | Infer_err err -> Infer_err err)
              | Infer_err err -> Infer_err err)
           in collect
         in
         (match collect _UU03a3_c args with
          | Infer_ok p0 ->
            let (arg_tys, _UU03a3_') = p0 in
            (match ty_core t_callee with
             | TFn (param_tys, ret) ->
               (match check_arg_tys _UU03a9_ arg_tys param_tys with
                | Some err -> Infer_err err
                | None -> Infer_ok (ret, _UU03a3_'))
             | TForall (m, bounds, body) ->
               (match ty_core body with
                | TFn (param_tys, ret) ->
                  (match build_bound_sigma (repeat None m) arg_tys param_tys with
                   | Some _UU03c3_ ->
                     let param_tys_open =
                       map (open_bound_ty _UU03c3_) param_tys
                     in
                     (match check_arg_tys _UU03a9_ arg_tys param_tys_open with
                      | Some err -> Infer_err err
                      | None ->
                        let ret_open = open_bound_ty _UU03c3_ ret in
                        let bounds_open = open_bound_outlives _UU03c3_ bounds
                        in
                        if (||) (contains_lbound_ty ret_open)
                             (contains_lbound_outlives bounds_open)
                        then Infer_err ErrHrtUnresolvedBound
                        else if outlives_constraints_hold_b _UU03a9_
                                  bounds_open
                             then Infer_ok (ret_open, _UU03a3_')
                             else Infer_err ErrHrtBoundUnsatisfied)
                   | None -> Infer_err ErrLifetimeConflict)
                | x -> Infer_err (ErrMalformedHrtBody x))
             | x -> Infer_err (ErrNotAFunction x))
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | EStruct (sname, lts, args, fields) ->
      (match lookup_struct sname env with
       | Some s ->
         if negb (Nat.eqb (length lts) s.struct_lifetimes)
         then Infer_err ErrArityMismatch
         else if negb (Nat.eqb (length args) s.struct_type_params)
              then Infer_err ErrArityMismatch
              else (match check_struct_bounds env s.struct_bounds args with
                    | Some err -> Infer_err err
                    | None ->
                      (match first_duplicate_field fields with
                       | Some name -> Infer_err (ErrDuplicateField name)
                       | None ->
                         (match first_unknown_field fields s.struct_fields with
                          | Some name -> Infer_err (ErrFieldNotFound name)
                          | None ->
                            (match first_missing_field s.struct_fields fields with
                             | Some name -> Infer_err (ErrMissingField name)
                             | None ->
                               let go =
                                 let rec go _UU03a3_0 = function
                                 | [] -> Infer_ok _UU03a3_0
                                 | f :: rest ->
                                   (match lookup_field_b f.field_name fields with
                                    | Some e_field ->
                                      (match infer_core_env_state_fuel fuel'
                                               env _UU03a9_ n _UU03a3_0
                                               e_field with
                                       | Infer_ok p ->
                                         let (t_field, _UU03a3_1) = p in
                                         let t_expected =
                                           instantiate_struct_field_ty lts
                                             args f
                                         in
                                         if ty_compatible_b _UU03a9_ t_field
                                              t_expected
                                         then go _UU03a3_1 rest
                                         else Infer_err
                                                (compatible_error t_field
                                                  t_expected)
                                       | Infer_err err -> Infer_err err)
                                    | None ->
                                      Infer_err (ErrMissingField f.field_name))
                                 in go
                               in
                               (match go _UU03a3_ s.struct_fields with
                                | Infer_ok _UU03a3_' ->
                                  Infer_ok
                                    ((instantiate_struct_instance_ty s lts
                                       args),
                                    _UU03a3_')
                                | Infer_err err -> Infer_err err)))))
       | None -> Infer_err (ErrStructNotFound sname))
    | EReplace (p, e_new) ->
      (match infer_place_sctx env _UU03a3_ p with
       | Infer_ok t_old ->
         let root = place_name p in
         (match place_path p with
          | Some p0 ->
            let (x, path) = p0 in
            (match sctx_lookup_mut x _UU03a3_ with
             | Some m ->
               (match m with
                | MImmutable -> Infer_err (ErrNotMutable x)
                | MMutable ->
                  if writable_place_b env _UU03a3_ p
                  then (match infer_core_env_state_fuel fuel' env _UU03a9_ n
                                _UU03a3_ e_new with
                        | Infer_ok p1 ->
                          let (t_new, _UU03a3_1) = p1 in
                          if ty_compatible_b _UU03a9_ t_new t_old
                          then (match sctx_path_available _UU03a3_1 x path with
                                | Infer_ok _ ->
                                  (match sctx_restore_path _UU03a3_1 x path with
                                   | Infer_ok _UU03a3_2 ->
                                     Infer_ok (t_old, _UU03a3_2)
                                   | Infer_err err -> Infer_err err)
                                | Infer_err err -> Infer_err err)
                          else Infer_err (compatible_error t_new t_old)
                        | Infer_err err -> Infer_err err)
                  else Infer_err (ErrNotMutable x))
             | None -> Infer_err (ErrUnknownVar x))
          | None ->
            if writable_place_b env _UU03a3_ p
            then (match infer_core_env_state_fuel fuel' env _UU03a9_ n
                          _UU03a3_ e_new with
                  | Infer_ok p0 ->
                    let (t_new, _UU03a3_1) = p0 in
                    if ty_compatible_b _UU03a9_ t_new t_old
                    then Infer_ok (t_old, _UU03a3_1)
                    else Infer_err (compatible_error t_new t_old)
                  | Infer_err err -> Infer_err err)
            else Infer_err (ErrNotMutable root))
       | Infer_err err -> Infer_err err)
    | EAssign (p, e_new) ->
      (match infer_place_sctx env _UU03a3_ p with
       | Infer_ok t_old ->
         if usage_eqb (ty_usage t_old) ULinear
         then Infer_err (ErrUsageMismatch ((ty_usage t_old), UAffine))
         else let root = place_name p in
              (match place_path p with
               | Some p0 ->
                 let (x, path) = p0 in
                 (match sctx_lookup_mut x _UU03a3_ with
                  | Some m ->
                    (match m with
                     | MImmutable -> Infer_err (ErrNotMutable x)
                     | MMutable ->
                       if writable_place_b env _UU03a3_ p
                       then (match infer_core_env_state_fuel fuel' env
                                     _UU03a9_ n _UU03a3_ e_new with
                             | Infer_ok p1 ->
                               let (t_new, _UU03a3_1) = p1 in
                               if ty_compatible_b _UU03a9_ t_new t_old
                               then (match sctx_path_available _UU03a3_1 x
                                             path with
                                     | Infer_ok _ ->
                                       Infer_ok ((MkTy (UUnrestricted,
                                         TUnits)), _UU03a3_1)
                                     | Infer_err err -> Infer_err err)
                               else Infer_err (compatible_error t_new t_old)
                             | Infer_err err -> Infer_err err)
                       else Infer_err (ErrNotMutable x))
                  | None -> Infer_err (ErrUnknownVar x))
               | None ->
                 if writable_place_b env _UU03a3_ p
                 then (match infer_core_env_state_fuel fuel' env _UU03a9_ n
                               _UU03a3_ e_new with
                       | Infer_ok p0 ->
                         let (t_new, _UU03a3_1) = p0 in
                         if ty_compatible_b _UU03a9_ t_new t_old
                         then Infer_ok ((MkTy (UUnrestricted, TUnits)),
                                _UU03a3_1)
                         else Infer_err (compatible_error t_new t_old)
                       | Infer_err err -> Infer_err err)
                 else Infer_err (ErrNotMutable root))
       | Infer_err err -> Infer_err err)
    | EBorrow (rk, p) ->
      (match infer_place_sctx env _UU03a3_ p with
       | Infer_ok t_p ->
         (match rk with
          | RShared ->
            Infer_ok ((MkTy (UUnrestricted, (TRef ((LVar n), RShared,
              t_p)))), _UU03a3_)
          | RUnique ->
            (match place_path p with
             | Some p0 ->
               let (x, _) = p0 in
               (match sctx_lookup_mut x _UU03a3_ with
                | Some m ->
                  (match m with
                   | MImmutable -> Infer_err (ErrImmutableBorrow x)
                   | MMutable ->
                     Infer_ok ((MkTy (UAffine, (TRef ((LVar n), RUnique,
                       t_p)))), _UU03a3_))
                | None -> Infer_err (ErrUnknownVar x))
             | None ->
               if place_under_unique_ref_b env _UU03a3_ p
               then Infer_ok ((MkTy (UAffine, (TRef ((LVar n), RUnique,
                      t_p)))), _UU03a3_)
               else Infer_err (ErrImmutableBorrow (place_name p))))
       | Infer_err err -> Infer_err err)
    | EDeref r ->
      (match expr_as_place r with
       | Some p ->
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_r ->
            (match ty_core t_r with
             | TRef (_, _, t_inner) ->
               if usage_eqb (ty_usage t_inner) UUnrestricted
               then Infer_ok (t_inner, _UU03a3_)
               else Infer_err (ErrUsageMismatch ((ty_usage t_inner),
                      UUnrestricted))
             | x -> Infer_err (ErrNotAReference x))
          | Infer_err err -> Infer_err err)
       | None ->
         (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_ r with
          | Infer_ok p ->
            let (t_r, _UU03a3_') = p in
            (match ty_core t_r with
             | TRef (_, _, t_inner) ->
               if usage_eqb (ty_usage t_inner) UUnrestricted
               then Infer_ok (t_inner, _UU03a3_')
               else Infer_err (ErrUsageMismatch ((ty_usage t_inner),
                      UUnrestricted))
             | x -> Infer_err (ErrNotAReference x))
          | Infer_err err -> Infer_err err))
    | EDrop e1 ->
      (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_ e1 with
       | Infer_ok p ->
         let (_, _UU03a3_') = p in
         Infer_ok ((MkTy (UUnrestricted, TUnits)), _UU03a3_')
       | Infer_err err -> Infer_err err)
    | EIf (e1, e2, e3) ->
      (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_ e1 with
       | Infer_ok p ->
         let (t_cond, _UU03a3_1) = p in
         if ty_core_eqb (ty_core t_cond) TBooleans
         then (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_1
                       e2 with
               | Infer_ok p0 ->
                 let (t2, _UU03a3_2) = p0 in
                 (match infer_core_env_state_fuel fuel' env _UU03a9_ n
                          _UU03a3_1 e3 with
                  | Infer_ok p1 ->
                    let (t3, _UU03a3_3) = p1 in
                    if ty_core_eqb (ty_core t2) (ty_core t3)
                    then (match ctx_merge (ctx_of_sctx _UU03a3_2)
                                  (ctx_of_sctx _UU03a3_3) with
                          | Some _UU0393_4 ->
                            Infer_ok ((MkTy
                              ((usage_max (ty_usage t2) (ty_usage t3)),
                              (ty_core t2))), (sctx_of_ctx _UU0393_4))
                          | None -> Infer_err ErrContextCheckFailed)
                    else Infer_err (ErrTypeMismatch ((ty_core t2),
                           (ty_core t3)))
                  | Infer_err err -> Infer_err err)
               | Infer_err err -> Infer_err err)
         else Infer_err (ErrTypeMismatch ((ty_core t_cond), TBooleans))
       | Infer_err err -> Infer_err err))
    fuel

(** val infer_core_env :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
    (ty * ctx) infer_result **)

let infer_core_env env _UU03a9_ n _UU0393_ e =
  match infer_core_env_state_fuel
          (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) env
          _UU03a9_ n (sctx_of_ctx _UU0393_) e with
  | Infer_ok p ->
    let (t, _UU03a3_) = p in Infer_ok (t, (ctx_of_sctx _UU03a3_))
  | Infer_err err -> Infer_err err

(** val root_set_eqb : root_set -> root_set -> bool **)

let rec root_set_eqb a b =
  match a with
  | [] -> (match b with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match b with
     | [] -> false
     | y :: ys -> (&&) (ident_eqb x y) (root_set_eqb xs ys))

(** val root_env_eqb : root_env -> root_env -> bool **)

let rec root_env_eqb r1 r2 =
  match r1 with
  | [] -> (match r2 with
           | [] -> true
           | _ :: _ -> false)
  | p :: rest1 ->
    let (x1, roots1) = p in
    (match r2 with
     | [] -> false
     | p0 :: rest2 ->
       let (x2, roots2) = p0 in
       (&&) ((&&) (ident_eqb x1 x2) (root_set_eqb roots1 roots2))
         (root_env_eqb rest1 rest2))

(** val roots_exclude_b : ident -> root_set -> bool **)

let roots_exclude_b x roots =
  negb (existsb (ident_eqb x) roots)

(** val root_env_excludes_b : ident -> root_env -> bool **)

let rec root_env_excludes_b x = function
| [] -> true
| p :: rest ->
  let (y, roots) = p in
  (&&) (if ident_eqb x y then true else roots_exclude_b x roots)
    (root_env_excludes_b x rest)

(** val infer_place_roots :
    global_env -> sctx -> root_env -> place ->
    (((ty * ident) * field_path) * root_set) infer_result **)

let infer_place_roots env _UU03a3_ r p =
  match place_path p with
  | Some p0 ->
    let (x, path) = p0 in
    (match infer_place_sctx env _UU03a3_ p with
     | Infer_ok t ->
       (match root_env_lookup x r with
        | Some roots -> Infer_ok (((t, x), path), roots)
        | None -> Infer_err ErrContextCheckFailed)
     | Infer_err err -> Infer_err err)
  | None -> Infer_err ErrNotImplemented

(** val consume_direct_place_value_roots :
    global_env -> sctx -> root_env -> place -> ((ty * sctx) * root_set)
    infer_result **)

let consume_direct_place_value_roots env _UU03a3_ r p =
  match infer_place_roots env _UU03a3_ r p with
  | Infer_ok p0 ->
    let (p1, roots) = p0 in
    let (p2, path) = p1 in
    let (t, x) = p2 in
    if usage_eqb (ty_usage t) UUnrestricted
    then Infer_ok ((t, _UU03a3_), roots)
    else (match sctx_consume_path _UU03a3_ x path with
          | Infer_ok _UU03a3_' -> Infer_ok ((t, _UU03a3_'), roots)
          | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val infer_core_env_state_fuel_roots :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    root_env -> sctx -> expr -> (((ty * sctx) * root_env) * root_set)
    infer_result **)

let rec infer_core_env_state_fuel_roots fuel env _UU03a9_ n r _UU03a3_ e =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> Infer_err ErrNotImplemented)
    (fun fuel' ->
    match e with
    | EUnit -> Infer_ok ((((MkTy (UUnrestricted, TUnits)), _UU03a3_), r), [])
    | ELit l ->
      (match l with
       | LInt _ ->
         Infer_ok ((((MkTy (UUnrestricted, TIntegers)), _UU03a3_), r), [])
       | LFloat _ ->
         Infer_ok ((((MkTy (UUnrestricted, TFloats)), _UU03a3_), r), [])
       | LBool _ ->
         Infer_ok ((((MkTy (UUnrestricted, TBooleans)), _UU03a3_), r), []))
    | EVar x ->
      (match consume_direct_place_value_roots env _UU03a3_ r (PVar x) with
       | Infer_ok p -> let (p0, roots) = p in Infer_ok ((p0, r), roots)
       | Infer_err err -> Infer_err err)
    | ELet (m, x, t, e1, e2) ->
      (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r _UU03a3_
               e1 with
       | Infer_ok p ->
         let (p0, roots1) = p in
         let (p1, r1) = p0 in
         let (t1, _UU03a3_1) = p1 in
         if ty_compatible_b _UU03a9_ t1 t
         then (match root_env_lookup x r1 with
               | Some _ -> Infer_err ErrContextCheckFailed
               | None ->
                 (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                          (root_env_add x roots1 r1)
                          (sctx_add x t m _UU03a3_1) e2 with
                  | Infer_ok p2 ->
                    let (p3, roots2) = p2 in
                    let (p4, r2) = p3 in
                    let (t2, _UU03a3_2) = p4 in
                    if (&&)
                         ((&&) (sctx_check_ok env x t _UU03a3_2)
                           (roots_exclude_b x roots2))
                         (root_env_excludes_b x (root_env_remove x r2))
                    then Infer_ok (((t2, (sctx_remove x _UU03a3_2)),
                           (root_env_remove x r2)), roots2)
                    else Infer_err ErrContextCheckFailed
                  | Infer_err err -> Infer_err err))
         else Infer_err (compatible_error t1 t)
       | Infer_err err -> Infer_err err)
    | ELetInfer (m, x, e1, e2) ->
      (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r _UU03a3_
               e1 with
       | Infer_ok p ->
         let (p0, roots1) = p in
         let (p1, r1) = p0 in
         let (t1, _UU03a3_1) = p1 in
         (match root_env_lookup x r1 with
          | Some _ -> Infer_err ErrContextCheckFailed
          | None ->
            (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                     (root_env_add x roots1 r1) (sctx_add x t1 m _UU03a3_1) e2 with
             | Infer_ok p2 ->
               let (p3, roots2) = p2 in
               let (p4, r2) = p3 in
               let (t2, _UU03a3_2) = p4 in
               if (&&)
                    ((&&) (sctx_check_ok env x t1 _UU03a3_2)
                      (roots_exclude_b x roots2))
                    (root_env_excludes_b x (root_env_remove x r2))
               then Infer_ok (((t2, (sctx_remove x _UU03a3_2)),
                      (root_env_remove x r2)), roots2)
               else Infer_err ErrContextCheckFailed
             | Infer_err err -> Infer_err err))
       | Infer_err err -> Infer_err err)
    | EFn fname ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef -> Infer_ok ((((fn_value_ty fdef), _UU03a3_), r), [])
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EPlace p ->
      (match consume_direct_place_value_roots env _UU03a3_ r p with
       | Infer_ok p0 -> let (p1, roots) = p0 in Infer_ok ((p1, r), roots)
       | Infer_err err -> Infer_err err)
    | ECall (fname, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         let m = fdef.fn_lifetimes in
         let collect =
           let rec collect _UU03a3_0 r0 = function
           | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
           | e' :: es ->
             (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r0
                      _UU03a3_0 e' with
              | Infer_ok p ->
                let (p0, roots_e) = p in
                let (p1, r1) = p0 in
                let (t_e, _UU03a3_1) = p1 in
                (match collect _UU03a3_1 r1 es with
                 | Infer_ok p2 ->
                   let (p3, roots_es) = p2 in
                   let (p4, r2) = p3 in
                   let (tys, _UU03a3_2) = p4 in
                   Infer_ok ((((t_e :: tys), _UU03a3_2), r2),
                   (roots_e :: roots_es))
                 | Infer_err err -> Infer_err err)
              | Infer_err err -> Infer_err err)
           in collect
         in
         (match collect _UU03a3_ r args with
          | Infer_ok p ->
            let (p0, arg_roots) = p in
            let (p1, r') = p0 in
            let (arg_tys, _UU03a3_') = p1 in
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
                       then Infer_ok ((((apply_lt_ty _UU03c3_ fdef.fn_ret),
                              _UU03a3_'), r'), (root_sets_union arg_roots))
                       else Infer_err ErrHrtBoundUnsatisfied
                  else Infer_err ErrLifetimeLeak)
             | None -> Infer_err ErrLifetimeConflict)
          | Infer_err err -> Infer_err err)
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EStruct (sname, lts, args, fields) ->
      (match lookup_struct sname env with
       | Some s ->
         if negb (Nat.eqb (length lts) s.struct_lifetimes)
         then Infer_err ErrArityMismatch
         else if negb (Nat.eqb (length args) s.struct_type_params)
              then Infer_err ErrArityMismatch
              else (match check_struct_bounds env s.struct_bounds args with
                    | Some err -> Infer_err err
                    | None ->
                      (match first_duplicate_field fields with
                       | Some name -> Infer_err (ErrDuplicateField name)
                       | None ->
                         (match first_unknown_field fields s.struct_fields with
                          | Some name -> Infer_err (ErrFieldNotFound name)
                          | None ->
                            (match first_missing_field s.struct_fields fields with
                             | Some name -> Infer_err (ErrMissingField name)
                             | None ->
                               let go =
                                 let rec go _UU03a3_0 r0 = function
                                 | [] -> Infer_ok ((_UU03a3_0, r0), [])
                                 | f :: rest ->
                                   (match lookup_field_b f.field_name fields with
                                    | Some e_field ->
                                      (match infer_core_env_state_fuel_roots
                                               fuel' env _UU03a9_ n r0
                                               _UU03a3_0 e_field with
                                       | Infer_ok p ->
                                         let (p0, roots_field) = p in
                                         let (p1, r1) = p0 in
                                         let (t_field, _UU03a3_1) = p1 in
                                         let t_expected =
                                           instantiate_struct_field_ty lts
                                             args f
                                         in
                                         if ty_compatible_b _UU03a9_ t_field
                                              t_expected
                                         then (match go _UU03a3_1 r1 rest with
                                               | Infer_ok p2 ->
                                                 let (p3, roots_rest) = p2 in
                                                 Infer_ok (p3,
                                                 (root_set_union roots_field
                                                   roots_rest))
                                               | Infer_err err ->
                                                 Infer_err err)
                                         else Infer_err
                                                (compatible_error t_field
                                                  t_expected)
                                       | Infer_err err -> Infer_err err)
                                    | None ->
                                      Infer_err (ErrMissingField f.field_name))
                                 in go
                               in
                               (match go _UU03a3_ r s.struct_fields with
                                | Infer_ok p ->
                                  let (p0, roots) = p in
                                  let (_UU03a3_', r') = p0 in
                                  Infer_ok
                                  ((((instantiate_struct_instance_ty s lts
                                       args),
                                  _UU03a3_'), r'), roots)
                                | Infer_err err -> Infer_err err)))))
       | None -> Infer_err (ErrStructNotFound sname))
    | EReplace (p, e_new) ->
      (match place_path p with
       | Some p0 ->
         let (x, path) = p0 in
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_old ->
            (match root_env_lookup x r with
             | Some roots_result ->
               (match sctx_lookup_mut x _UU03a3_ with
                | Some m ->
                  (match m with
                   | MImmutable -> Infer_err (ErrNotMutable x)
                   | MMutable ->
                     if writable_place_b env _UU03a3_ p
                     then (match infer_core_env_state_fuel_roots fuel' env
                                   _UU03a9_ n r _UU03a3_ e_new with
                           | Infer_ok p1 ->
                             let (p2, roots_new) = p1 in
                             let (p3, r1) = p2 in
                             let (t_new, _UU03a3_1) = p3 in
                             (match root_env_lookup x r1 with
                              | Some roots_old ->
                                if ty_compatible_b _UU03a9_ t_new t_old
                                then (match sctx_path_available _UU03a3_1 x
                                              path with
                                      | Infer_ok _ ->
                                        (match sctx_restore_path _UU03a3_1 x
                                                 path with
                                         | Infer_ok _UU03a3_2 ->
                                           Infer_ok (((t_old, _UU03a3_2),
                                             (root_env_update x
                                               (root_set_union roots_old
                                                 roots_new)
                                               r1)),
                                             roots_result)
                                         | Infer_err err -> Infer_err err)
                                      | Infer_err err -> Infer_err err)
                                else Infer_err (compatible_error t_new t_old)
                              | None -> Infer_err ErrContextCheckFailed)
                           | Infer_err err -> Infer_err err)
                     else Infer_err (ErrNotMutable x))
                | None -> Infer_err (ErrUnknownVar x))
             | None -> Infer_err ErrContextCheckFailed)
          | Infer_err err -> Infer_err err)
       | None -> Infer_err ErrNotImplemented)
    | EAssign (p, e_new) ->
      (match place_path p with
       | Some p0 ->
         let (x, path) = p0 in
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_old ->
            if usage_eqb (ty_usage t_old) ULinear
            then Infer_err (ErrUsageMismatch ((ty_usage t_old), UAffine))
            else (match sctx_lookup_mut x _UU03a3_ with
                  | Some m ->
                    (match m with
                     | MImmutable -> Infer_err (ErrNotMutable x)
                     | MMutable ->
                       if writable_place_b env _UU03a3_ p
                       then (match infer_core_env_state_fuel_roots fuel' env
                                     _UU03a9_ n r _UU03a3_ e_new with
                             | Infer_ok p1 ->
                               let (p2, roots_new) = p1 in
                               let (p3, r1) = p2 in
                               let (t_new, _UU03a3_1) = p3 in
                               (match root_env_lookup x r1 with
                                | Some roots_old ->
                                  if ty_compatible_b _UU03a9_ t_new t_old
                                  then (match sctx_path_available _UU03a3_1 x
                                                path with
                                        | Infer_ok _ ->
                                          Infer_ok ((((MkTy (UUnrestricted,
                                            TUnits)), _UU03a3_1),
                                            (root_env_update x
                                              (root_set_union roots_old
                                                roots_new)
                                              r1)),
                                            [])
                                        | Infer_err err -> Infer_err err)
                                  else Infer_err
                                         (compatible_error t_new t_old)
                                | None -> Infer_err ErrContextCheckFailed)
                             | Infer_err err -> Infer_err err)
                       else Infer_err (ErrNotMutable x))
                  | None -> Infer_err (ErrUnknownVar x))
          | Infer_err err -> Infer_err err)
       | None -> Infer_err ErrNotImplemented)
    | EBorrow (rk, p) ->
      (match place_path p with
       | Some p0 ->
         let (x, _) = p0 in
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_p ->
            (match rk with
             | RShared ->
               Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n), RShared,
                 t_p)))), _UU03a3_), r), (x :: []))
             | RUnique ->
               (match sctx_lookup_mut x _UU03a3_ with
                | Some m ->
                  (match m with
                   | MImmutable -> Infer_err (ErrImmutableBorrow x)
                   | MMutable ->
                     Infer_ok ((((MkTy (UAffine, (TRef ((LVar n), RUnique,
                       t_p)))), _UU03a3_), r), (x :: [])))
                | None -> Infer_err (ErrUnknownVar x)))
          | Infer_err err -> Infer_err err)
       | None -> Infer_err ErrNotImplemented)
    | EDrop e1 ->
      (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r _UU03a3_
               e1 with
       | Infer_ok p ->
         let (p0, _) = p in
         let (p1, r') = p0 in
         let (_, _UU03a3_') = p1 in
         Infer_ok ((((MkTy (UUnrestricted, TUnits)), _UU03a3_'), r'), [])
       | Infer_err err -> Infer_err err)
    | EIf (e1, e2, e3) ->
      (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r _UU03a3_
               e1 with
       | Infer_ok p ->
         let (p0, _) = p in
         let (p1, r1) = p0 in
         let (t_cond, _UU03a3_1) = p1 in
         if ty_core_eqb (ty_core t_cond) TBooleans
         then (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r1
                       _UU03a3_1 e2 with
               | Infer_ok p2 ->
                 let (p3, roots2) = p2 in
                 let (p4, r2) = p3 in
                 let (t2, _UU03a3_2) = p4 in
                 (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                          r1 _UU03a3_1 e3 with
                  | Infer_ok p5 ->
                    let (p6, roots3) = p5 in
                    let (p7, r3) = p6 in
                    let (t3, _UU03a3_3) = p7 in
                    if ty_core_eqb (ty_core t2) (ty_core t3)
                    then if root_env_eqb r2 r3
                         then (match ctx_merge (ctx_of_sctx _UU03a3_2)
                                       (ctx_of_sctx _UU03a3_3) with
                               | Some _UU0393_4 ->
                                 Infer_ok ((((MkTy
                                   ((usage_max (ty_usage t2) (ty_usage t3)),
                                   (ty_core t2))), (sctx_of_ctx _UU0393_4)),
                                   r2), (root_set_union roots2 roots3))
                               | None -> Infer_err ErrContextCheckFailed)
                         else Infer_err ErrContextCheckFailed
                    else Infer_err (ErrTypeMismatch ((ty_core t2),
                           (ty_core t3)))
                  | Infer_err err -> Infer_err err)
               | Infer_err err -> Infer_err err)
         else Infer_err (ErrTypeMismatch ((ty_core t_cond), TBooleans))
       | Infer_err err -> Infer_err err)
    | _ -> Infer_err ErrNotImplemented)
    fuel

(** val infer_core_env_roots :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx ->
    expr -> (((ty * ctx) * root_env) * root_set) infer_result **)

let infer_core_env_roots env _UU03a9_ n r _UU0393_ e =
  match infer_core_env_state_fuel_roots
          (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) env
          _UU03a9_ n r (sctx_of_ctx _UU0393_) e with
  | Infer_ok p ->
    let (p0, roots) = p in
    let (p1, r') = p0 in
    let (t, _UU03a3_) = p1 in
    Infer_ok (((t, (ctx_of_sctx _UU03a3_)), r'), roots)
  | Infer_err err -> Infer_err err

(** val wf_params_b : region_ctx -> param list -> bool **)

let rec wf_params_b _UU0394_ = function
| [] -> true
| p :: ps' -> (&&) (wf_type_b _UU0394_ p.param_ty) (wf_params_b _UU0394_ ps')

(** val string_in : string -> string list -> bool **)

let rec string_in x = function
| [] -> false
| y :: ys -> if (=) x y then true else string_in x ys

(** val duplicate_param_name_aux :
    string list -> param list -> ident option **)

let rec duplicate_param_name_aux seen = function
| [] -> None
| p :: ps' ->
  if string_in (fst p.param_name) seen
  then Some p.param_name
  else duplicate_param_name_aux ((fst p.param_name) :: seen) ps'

(** val duplicate_param_name : param list -> ident option **)

let duplicate_param_name ps =
  duplicate_param_name_aux [] ps

(** val infer_env : global_env -> fn_def -> (ty * ctx) infer_result **)

let infer_env env f =
  let n = f.fn_lifetimes in
  let _UU03a9_ = f.fn_outlives in
  let _UU0394_ = mk_region_ctx n in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_type_b _UU0394_ f.fn_ret)
       then Infer_err ErrLifetimeLeak
       else if negb (wf_params_b _UU0394_ f.fn_params)
            then Infer_err ErrLifetimeLeak
            else (match duplicate_param_name f.fn_params with
                  | Some x -> Infer_err (ErrDuplicateParam x)
                  | None ->
                    (match infer_core_env env _UU03a9_ n
                             (params_ctx f.fn_params) f.fn_body with
                     | Infer_ok p ->
                       let (t_body, _UU0393__out) = p in
                       if negb (wf_type_b _UU0394_ t_body)
                       then Infer_err ErrLifetimeLeak
                       else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                            then if params_ok_env_b env f.fn_params
                                      _UU0393__out
                                 then Infer_ok (f.fn_ret, _UU0393__out)
                                 else Infer_err ErrContextCheckFailed
                            else Infer_err (compatible_error t_body f.fn_ret)
                     | Infer_err err -> Infer_err err))

(** val infer_env_roots :
    global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
    infer_result **)

let infer_env_roots env f r0 =
  let n = f.fn_lifetimes in
  let _UU03a9_ = f.fn_outlives in
  let _UU0394_ = mk_region_ctx n in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_type_b _UU0394_ f.fn_ret)
       then Infer_err ErrLifetimeLeak
       else if negb (wf_params_b _UU0394_ f.fn_params)
            then Infer_err ErrLifetimeLeak
            else (match duplicate_param_name f.fn_params with
                  | Some x -> Infer_err (ErrDuplicateParam x)
                  | None ->
                    (match infer_core_env_roots env _UU03a9_ n r0
                             (params_ctx f.fn_params) f.fn_body with
                     | Infer_ok p ->
                       let (p0, roots) = p in
                       let (p1, r_out) = p0 in
                       let (t_body, _UU0393__out) = p1 in
                       if negb (wf_type_b _UU0394_ t_body)
                       then Infer_err ErrLifetimeLeak
                       else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                            then if params_ok_env_b env f.fn_params
                                      _UU0393__out
                                 then Infer_ok (((f.fn_ret, _UU0393__out),
                                        r_out), roots)
                                 else Infer_err ErrContextCheckFailed
                            else Infer_err (compatible_error t_body f.fn_ret)
                     | Infer_err err -> Infer_err err))

type path_borrow_entry =
| PBShared of ident * field_path
| PBMut of ident * field_path

type path_borrow_state = path_borrow_entry list

(** val pbe_target_eqb : ident -> field_path -> path_borrow_entry -> bool **)

let pbe_target_eqb x p = function
| PBShared (y, q) -> (&&) (ident_eqb x y) (path_conflict_b p q)
| PBMut (y, q) -> (&&) (ident_eqb x y) (path_conflict_b p q)

(** val pbs_has_mut : ident -> field_path -> path_borrow_state -> bool **)

let pbs_has_mut x p pBS =
  existsb (fun e ->
    match e with
    | PBShared (_, _) -> false
    | PBMut (y, q) -> (&&) (ident_eqb x y) (path_conflict_b p q)) pBS

(** val pbs_has_any : ident -> field_path -> path_borrow_state -> bool **)

let pbs_has_any x p pBS =
  existsb (pbe_target_eqb x p) pBS

(** val borrow_target_of_place : place -> ident * field_path **)

let borrow_target_of_place p =
  ((place_root p), (place_suffix_path p))

(** val path_borrow_entry_eqb :
    path_borrow_entry -> path_borrow_entry -> bool **)

let path_borrow_entry_eqb a b =
  match a with
  | PBShared (x, p) ->
    (match b with
     | PBShared (y, q) -> (&&) (ident_eqb x y) (path_eqb p q)
     | PBMut (_, _) -> false)
  | PBMut (x, p) ->
    (match b with
     | PBShared (_, _) -> false
     | PBMut (y, q) -> (&&) (ident_eqb x y) (path_eqb p q))

(** val pbs_remove_one :
    path_borrow_entry -> path_borrow_state -> path_borrow_state **)

let rec pbs_remove_one e = function
| [] -> []
| h :: rest ->
  if path_borrow_entry_eqb e h then rest else h :: (pbs_remove_one e rest)

(** val pbs_remove_all :
    path_borrow_state -> path_borrow_state -> path_borrow_state **)

let pbs_remove_all to_remove pBS =
  fold_left (fun acc e -> pbs_remove_one e acc) to_remove pBS

(** val pbs_new_entries :
    path_borrow_state -> path_borrow_state -> path_borrow_state **)

let pbs_new_entries before after =
  firstn (sub (length after) (length before)) after

(** val pbs_eqb : path_borrow_state -> path_borrow_state -> bool **)

let rec pbs_eqb a b =
  match a with
  | [] -> (match b with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match b with
     | [] -> false
     | y :: ys -> (&&) (path_borrow_entry_eqb x y) (pbs_eqb xs ys))

(** val pbs_access_allowed_b :
    ident -> field_path -> path_borrow_state -> ty -> bool **)

let pbs_access_allowed_b x p pBS t =
  (&&) (negb (pbs_has_mut x p pBS))
    ((||) (usage_eqb (ty_usage t) UUnrestricted) (negb (pbs_has_any x p pBS)))

(** val borrow_check_place_access :
    global_env -> path_borrow_state -> ctx -> place -> unit infer_result **)

let borrow_check_place_access env pBS _UU0393_ p =
  match place_path p with
  | Some p0 ->
    let (x, path) = p0 in
    (match infer_place_env env _UU0393_ p with
     | Infer_ok t ->
       if pbs_access_allowed_b x path pBS t
       then Infer_ok ()
       else Infer_err (ErrBorrowConflict x)
     | Infer_err err -> Infer_err err)
  | None -> Infer_ok ()

(** val borrow_check_env :
    global_env -> path_borrow_state -> ctx -> expr -> path_borrow_state
    infer_result **)

let rec borrow_check_env env pBS _UU0393_ = function
| EVar x ->
  (match borrow_check_place_access env pBS _UU0393_ (PVar x) with
   | Infer_ok _ -> Infer_ok pBS
   | Infer_err err -> Infer_err err)
| ELet (m, x, t, e1, e2) ->
  (match borrow_check_env env pBS _UU0393_ e1 with
   | Infer_ok pBS1 ->
     let new_from_e1 = pbs_new_entries pBS pBS1 in
     (match borrow_check_env env pBS1 (ctx_add_b x t m _UU0393_) e2 with
      | Infer_ok pBS2 -> Infer_ok (pbs_remove_all new_from_e1 pBS2)
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| ELetInfer (_, _, e1, e2) ->
  (match borrow_check_env env pBS _UU0393_ e1 with
   | Infer_ok pBS1 ->
     let new_from_e1 = pbs_new_entries pBS pBS1 in
     (match borrow_check_env env pBS1 _UU0393_ e2 with
      | Infer_ok pBS2 -> Infer_ok (pbs_remove_all new_from_e1 pBS2)
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| EPlace p ->
  (match borrow_check_place_access env pBS _UU0393_ p with
   | Infer_ok _ -> Infer_ok pBS
   | Infer_err err -> Infer_err err)
| ECall (_, args) ->
  let rec go pBS0 = function
  | [] -> Infer_ok pBS0
  | a :: rest ->
    (match borrow_check_env env pBS0 _UU0393_ a with
     | Infer_ok pBS1 -> go pBS1 rest
     | Infer_err err -> Infer_err err)
  in go pBS args
| ECallExpr (callee, args) ->
  (match borrow_check_env env pBS _UU0393_ callee with
   | Infer_ok pBS1 ->
     let rec go pBS0 = function
     | [] -> Infer_ok pBS0
     | a :: rest ->
       (match borrow_check_env env pBS0 _UU0393_ a with
        | Infer_ok pBS2 -> go pBS2 rest
        | Infer_err err -> Infer_err err)
     in go pBS1 args
   | Infer_err err -> Infer_err err)
| EStruct (_, _, _, fields) ->
  let rec go pBS0 = function
  | [] -> Infer_ok pBS0
  | p :: rest ->
    let (_, e_field) = p in
    (match borrow_check_env env pBS0 _UU0393_ e_field with
     | Infer_ok pBS1 -> go pBS1 rest
     | Infer_err err -> Infer_err err)
  in go pBS fields
| EReplace (p, e_new) ->
  let (x, path) = borrow_target_of_place p in
  if pbs_has_any x path pBS
  then Infer_err (ErrBorrowConflict x)
  else borrow_check_env env pBS _UU0393_ e_new
| EAssign (p, e_new) ->
  let (x, path) = borrow_target_of_place p in
  if pbs_has_any x path pBS
  then Infer_err (ErrBorrowConflict x)
  else borrow_check_env env pBS _UU0393_ e_new
| EBorrow (r, p) ->
  (match r with
   | RShared ->
     let (x, path) = borrow_target_of_place p in
     if pbs_has_mut x path pBS
     then Infer_err (ErrBorrowConflict x)
     else Infer_ok ((PBShared (x, path)) :: pBS)
   | RUnique ->
     let (x, path) = borrow_target_of_place p in
     if pbs_has_any x path pBS
     then Infer_err (ErrBorrowConflict x)
     else Infer_ok ((PBMut (x, path)) :: pBS))
| EDeref e1 ->
  (match expr_ref_root e1 with
   | Some r ->
     if pbs_has_mut r [] pBS
     then Infer_err (ErrBorrowConflict r)
     else borrow_check_env env pBS _UU0393_ e1
   | None -> borrow_check_env env pBS _UU0393_ e1)
| EDrop e1 -> borrow_check_env env pBS _UU0393_ e1
| EIf (e1, e2, e3) ->
  (match borrow_check_env env pBS _UU0393_ e1 with
   | Infer_ok pBS1 ->
     (match borrow_check_env env pBS1 _UU0393_ e2 with
      | Infer_ok pBS2 ->
        (match borrow_check_env env pBS1 _UU0393_ e3 with
         | Infer_ok pBS3 ->
           if pbs_eqb pBS2 pBS3
           then Infer_ok pBS2
           else Infer_err ErrContextCheckFailed
         | Infer_err err -> Infer_err err)
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)
| _ -> Infer_ok pBS

(** val infer_full_env : global_env -> fn_def -> (ty * ctx) infer_result **)

let infer_full_env env f =
  match infer_env env f with
  | Infer_ok res ->
    (match borrow_check_env env [] (params_ctx f.fn_params) f.fn_body with
     | Infer_ok _ -> Infer_ok res
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val infer_full_env_roots :
    global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
    infer_result **)

let infer_full_env_roots env f r0 =
  match infer_env_roots env f r0 with
  | Infer_ok res ->
    (match borrow_check_env env [] (params_ctx f.fn_params) f.fn_body with
     | Infer_ok _ -> Infer_ok res
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val check_program_env : global_env -> bool **)

let check_program_env env =
  forallb (fun f ->
    match infer_full_env env f with
    | Infer_ok _ -> true
    | Infer_err _ -> false) env.env_fns
