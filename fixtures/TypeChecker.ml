
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

(** val max : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let rec max = Big_int_Z.max_big_int

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

type 'a core_trait_ref = { core_trait_ref_name : string;
                           core_trait_ref_args : 'a list }

type 'a core_trait_bound = { core_bound_type_index : Big_int_Z.big_int;
                             core_bound_traits : 'a core_trait_ref list }

type 'a typeCore =
| TUnits
| TIntegers
| TFloats
| TBooleans
| TNamed of string
| TParam of Big_int_Z.big_int
| TStruct of string * lifetime list * 'a list
| TEnum of string * lifetime list * 'a list
| TFn of 'a list * 'a
| TClosure of lifetime * 'a list * 'a
| TForall of Big_int_Z.big_int * outlives_ctx * 'a
| TTypeForall of Big_int_Z.big_int * 'a core_trait_bound list * 'a
| TAssoc of 'a * string * 'a list * string
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

(** val map_core_trait_ref :
    ('a1 -> 'a2) -> 'a1 core_trait_ref -> 'a2 core_trait_ref **)

let map_core_trait_ref f tr =
  { core_trait_ref_name = tr.core_trait_ref_name; core_trait_ref_args =
    (map f tr.core_trait_ref_args) }

(** val map_core_trait_bound :
    ('a1 -> 'a2) -> 'a1 core_trait_bound -> 'a2 core_trait_bound **)

let map_core_trait_bound f b =
  { core_bound_type_index = b.core_bound_type_index; core_bound_traits =
    (map (map_core_trait_ref f) b.core_bound_traits) }

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
   | TEnum (name, lts, args) ->
     let map_lt =
       let rec map_lt = function
       | [] -> []
       | x :: xs' -> (apply_lt_ty _UU03c3_ x) :: (map_lt xs')
       in map_lt
     in
     MkTy (u, (TEnum (name, (map (apply_lt_lifetime _UU03c3_) lts),
     (map_lt args))))
   | TFn (ts, r) ->
     let map_lt =
       let rec map_lt = function
       | [] -> []
       | x :: xs' -> (apply_lt_ty _UU03c3_ x) :: (map_lt xs')
       in map_lt
     in
     MkTy (u, (TFn ((map_lt ts), (apply_lt_ty _UU03c3_ r))))
   | TClosure (l, ts, r) ->
     let map_lt =
       let rec map_lt = function
       | [] -> []
       | x :: xs' -> (apply_lt_ty _UU03c3_ x) :: (map_lt xs')
       in map_lt
     in
     MkTy (u, (TClosure ((apply_lt_lifetime _UU03c3_ l), (map_lt ts),
     (apply_lt_ty _UU03c3_ r))))
   | TForall (n, _UU03a9_, body) ->
     MkTy (u, (TForall (n, (apply_lt_outlives _UU03c3_ _UU03a9_),
       (apply_lt_ty _UU03c3_ body))))
   | TTypeForall (n, bounds, body) ->
     MkTy (u, (TTypeForall (n,
       (map (map_core_trait_bound (apply_lt_ty _UU03c3_)) bounds),
       (apply_lt_ty _UU03c3_ body))))
   | TAssoc (for_ty, trait_name0, trait_args, assoc_name) ->
     MkTy (u, (TAssoc ((apply_lt_ty _UU03c3_ for_ty), trait_name0,
       (map (apply_lt_ty _UU03c3_) trait_args), assoc_name)))
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
   | TEnum (name, lts, args) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (map_lifetimes_ty f x) :: (go xs')
       in go
     in
     MkTy (u, (TEnum (name, (map f lts), (go args))))
   | TFn (ts, r) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (map_lifetimes_ty f x) :: (go xs')
       in go
     in
     MkTy (u, (TFn ((go ts), (map_lifetimes_ty f r))))
   | TClosure (l, ts, r) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (map_lifetimes_ty f x) :: (go xs')
       in go
     in
     MkTy (u, (TClosure ((f l), (go ts), (map_lifetimes_ty f r))))
   | TForall (n, _UU03a9_, body) ->
     MkTy (u, (TForall (n,
       (map (fun pat -> let (a, b) = pat in ((f a), (f b))) _UU03a9_),
       (map_lifetimes_ty f body))))
   | TTypeForall (n, bounds, body) ->
     MkTy (u, (TTypeForall (n, bounds, (map_lifetimes_ty f body))))
   | TAssoc (for_ty, trait_name0, trait_args, assoc_name) ->
     MkTy (u, (TAssoc ((map_lifetimes_ty f for_ty), trait_name0,
       (map (map_lifetimes_ty f) trait_args), assoc_name)))
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
   | TEnum (_, lts, args) ->
     (||) (existsb contains_lbound_lifetime lts)
       (existsb contains_lbound_ty args)
   | TFn (ts, r) ->
     (||) (existsb contains_lbound_ty ts) (contains_lbound_ty r)
   | TClosure (l, ts, r) ->
     (||) ((||) (contains_lbound_lifetime l) (existsb contains_lbound_ty ts))
       (contains_lbound_ty r)
   | TForall (_, _UU03a9_, body) ->
     (||) (contains_lbound_outlives _UU03a9_) (contains_lbound_ty body)
   | TTypeForall (_, bounds, body) ->
     (||)
       (existsb (fun b ->
         existsb (fun tr ->
           existsb contains_lbound_ty tr.core_trait_ref_args)
           b.core_bound_traits)
         bounds)
       (contains_lbound_ty body)
   | TAssoc (for_ty, _, trait_args, _) ->
     (||) (contains_lbound_ty for_ty) (existsb contains_lbound_ty trait_args)
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
| EMakeClosure of ident * ident list
| EPlace of place
| ECall of ident * expr list
| ECallGeneric of ident * ty list * expr list
| ECallExpr of expr * expr list
| ECallExprGeneric of expr * ty list * expr list
| EStruct of string * lifetime list * ty list * (string * expr) list
| EEnum of string * string * lifetime list * lifetime list * ty list
   * expr list
| EMatch of expr * ((string * ident list) * expr) list
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

(** val match_branch_name : ((string * ident list) * expr) -> string **)

let match_branch_name = function
| (p, _) -> let (name, _) = p in name

type param = { param_mutability : mutability; param_name : ident;
               param_ty : ty }

type trait_ref = { trait_ref_name : string; trait_ref_args : ty list }

type trait_bound = { bound_type_index : Big_int_Z.big_int;
                     bound_traits : trait_ref list }

type fn_def = { fn_name : ident; fn_lifetimes : Big_int_Z.big_int;
                fn_outlives : outlives_ctx; fn_captures : param list;
                fn_params : param list; fn_ret : ty; fn_body : expr;
                fn_type_params : Big_int_Z.big_int;
                fn_bounds : trait_bound list }

type syntax = fn_def list

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

(** val place_resolved_write_direct_parent_b : place -> bool **)

let place_resolved_write_direct_parent_b = function
| PDeref q -> (match place_path q with
               | Some _ -> true
               | None -> false)
| _ -> false

(** val place_suffix_path : place -> field_path **)

let rec place_suffix_path = function
| PField (q, f) -> app (place_suffix_path q) (f :: [])
| _ -> []

type field_def = { field_name : string; field_mutability : mutability;
                   field_ty : ty }

type struct_def = { struct_name : string;
                    struct_lifetimes : Big_int_Z.big_int;
                    struct_type_params : Big_int_Z.big_int;
                    struct_bounds : trait_bound list;
                    struct_fields : field_def list }

type enum_variant_def = { enum_variant_name : string;
                          enum_variant_lifetimes : Big_int_Z.big_int;
                          enum_variant_fields : ty list }

type enum_def = { enum_name : string; enum_lifetimes : Big_int_Z.big_int;
                  enum_type_params : Big_int_Z.big_int;
                  enum_bounds : trait_bound list;
                  enum_outlives : outlives_ctx;
                  enum_variants : enum_variant_def list }

type trait_assoc_def = { trait_assoc_name : string;
                         trait_assoc_bounds : trait_ref list }

type trait_method_sig = { trait_method_name : string;
                          trait_method_lifetimes : Big_int_Z.big_int;
                          trait_method_type_params : Big_int_Z.big_int;
                          trait_method_params : param list;
                          trait_method_ret : ty;
                          trait_method_bounds : trait_bound list }

type trait_def = { trait_name : string;
                   trait_type_params : Big_int_Z.big_int;
                   trait_bounds : trait_bound list;
                   trait_assoc_types : trait_assoc_def list;
                   trait_methods : trait_method_sig list }

type impl_assoc_def = { impl_assoc_name : string; impl_assoc_ty : ty }

type impl_def = { impl_lifetimes : Big_int_Z.big_int;
                  impl_type_params : Big_int_Z.big_int;
                  impl_trait_name : string; impl_trait_args : ty list;
                  impl_for_ty : ty; impl_assoc_types : impl_assoc_def list;
                  impl_methods : fn_def list }

type global_env = { env_structs : struct_def list; env_enums : enum_def list;
                    env_traits : trait_def list; env_impls : impl_def list;
                    env_local_bounds : trait_bound list; env_fns : fn_def list }

(** val global_env_with_local_bounds :
    global_env -> trait_bound list -> global_env **)

let global_env_with_local_bounds env bounds =
  { env_structs = env.env_structs; env_enums = env.env_enums; env_traits =
    env.env_traits; env_impls = env.env_impls; env_local_bounds = bounds;
    env_fns = env.env_fns }

(** val core_trait_ref_of_trait_ref : trait_ref -> ty core_trait_ref **)

let core_trait_ref_of_trait_ref tr =
  { core_trait_ref_name = tr.trait_ref_name; core_trait_ref_args =
    tr.trait_ref_args }

(** val core_trait_bound_of_trait_bound :
    trait_bound -> ty core_trait_bound **)

let core_trait_bound_of_trait_bound b =
  { core_bound_type_index = b.bound_type_index; core_bound_traits =
    (map core_trait_ref_of_trait_ref b.bound_traits) }

(** val trait_ref_of_core_trait_ref : ty core_trait_ref -> trait_ref **)

let trait_ref_of_core_trait_ref tr =
  { trait_ref_name = tr.core_trait_ref_name; trait_ref_args =
    tr.core_trait_ref_args }

(** val trait_bound_of_core_trait_bound :
    ty core_trait_bound -> trait_bound **)

let trait_bound_of_core_trait_bound b =
  { bound_type_index = b.core_bound_type_index; bound_traits =
    (map trait_ref_of_core_trait_ref b.core_bound_traits) }

(** val trait_bounds_of_core_trait_bounds :
    ty core_trait_bound list -> trait_bound list **)

let trait_bounds_of_core_trait_bounds bounds =
  map trait_bound_of_core_trait_bound bounds

(** val lookup_struct_in : string -> struct_def list -> struct_def option **)

let rec lookup_struct_in name = function
| [] -> None
| s :: rest ->
  if (=) name s.struct_name then Some s else lookup_struct_in name rest

(** val lookup_struct : string -> global_env -> struct_def option **)

let lookup_struct name env =
  lookup_struct_in name env.env_structs

(** val lookup_enum_in : string -> enum_def list -> enum_def option **)

let rec lookup_enum_in name = function
| [] -> None
| e :: rest ->
  if (=) name e.enum_name then Some e else lookup_enum_in name rest

(** val lookup_enum : string -> global_env -> enum_def option **)

let lookup_enum name env =
  lookup_enum_in name env.env_enums

(** val lookup_enum_variant :
    string -> enum_variant_def list -> enum_variant_def option **)

let rec lookup_enum_variant name = function
| [] -> None
| v :: rest ->
  if (=) name v.enum_variant_name
  then Some v
  else lookup_enum_variant name rest

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

(** val usage_max_decl : usage -> usage -> usage **)

let usage_max_decl u1 u2 =
  match u1 with
  | ULinear -> ULinear
  | UAffine -> (match u2 with
                | ULinear -> ULinear
                | _ -> UAffine)
  | UUnrestricted -> u2

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
       let rec go xs fallback =
         match xs with
         | [] -> fallback
         | x :: xs' ->
           (match fallback with
            | [] -> (subst_type_params_ty _UU03c3_ x) :: (go xs' [])
            | _ :: fb' -> (subst_type_params_ty _UU03c3_ x) :: (go xs' fb'))
       in go
     in
     MkTy (u, (TStruct (name, lts, (go args _UU03c3_))))
   | TEnum (name, lts, args) ->
     let go =
       let rec go xs fallback =
         match xs with
         | [] -> fallback
         | x :: xs' ->
           (match fallback with
            | [] -> (subst_type_params_ty _UU03c3_ x) :: (go xs' [])
            | _ :: fb' -> (subst_type_params_ty _UU03c3_ x) :: (go xs' fb'))
       in go
     in
     MkTy (u, (TEnum (name, lts, (go args _UU03c3_))))
   | TFn (ps, r) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (subst_type_params_ty _UU03c3_ x) :: (go xs')
       in go
     in
     MkTy (u, (TFn ((go ps), (subst_type_params_ty _UU03c3_ r))))
   | TClosure (env, ps, r) ->
     let go =
       let rec go = function
       | [] -> []
       | x :: xs' -> (subst_type_params_ty _UU03c3_ x) :: (go xs')
       in go
     in
     MkTy (u, (TClosure (env, (go ps), (subst_type_params_ty _UU03c3_ r))))
   | TForall (n, _UU03a9_, body) ->
     MkTy (u, (TForall (n, _UU03a9_, (subst_type_params_ty _UU03c3_ body))))
   | TAssoc (for_ty, trait_name0, trait_args, assoc_name) ->
     MkTy (u, (TAssoc ((subst_type_params_ty _UU03c3_ for_ty), trait_name0,
       (map (subst_type_params_ty _UU03c3_) trait_args), assoc_name)))
   | TRef (l, rk, inner) ->
     MkTy (u, (TRef (l, rk, (subst_type_params_ty _UU03c3_ inner))))
   | x -> MkTy (u, x))

(** val subst_type_params_expr : ty list -> expr -> expr **)

let rec subst_type_params_expr _UU03c3_ = function
| ELet (mut, x, t, e1, e2) ->
  ELet (mut, x, (subst_type_params_ty _UU03c3_ t),
    (subst_type_params_expr _UU03c3_ e1),
    (subst_type_params_expr _UU03c3_ e2))
| ELetInfer (mut, x, e1, e2) ->
  ELetInfer (mut, x, (subst_type_params_expr _UU03c3_ e1),
    (subst_type_params_expr _UU03c3_ e2))
| ECall (fname, args) ->
  let go =
    let rec go = function
    | [] -> []
    | e' :: es' -> (subst_type_params_expr _UU03c3_ e') :: (go es')
    in go
  in
  ECall (fname, (go args))
| ECallGeneric (fname, type_args, args) ->
  let go =
    let rec go = function
    | [] -> []
    | e' :: es' -> (subst_type_params_expr _UU03c3_ e') :: (go es')
    in go
  in
  ECallGeneric (fname, (map (subst_type_params_ty _UU03c3_) type_args),
  (go args))
| ECallExpr (ef, args) ->
  let go =
    let rec go = function
    | [] -> []
    | e' :: es' -> (subst_type_params_expr _UU03c3_ e') :: (go es')
    in go
  in
  ECallExpr ((subst_type_params_expr _UU03c3_ ef), (go args))
| ECallExprGeneric (ef, type_args, args) ->
  let go =
    let rec go = function
    | [] -> []
    | e' :: es' -> (subst_type_params_expr _UU03c3_ e') :: (go es')
    in go
  in
  ECallExprGeneric ((subst_type_params_expr _UU03c3_ ef),
  (map (subst_type_params_ty _UU03c3_) type_args), (go args))
| EStruct (name, lts, type_args, fields) ->
  let go =
    let rec go = function
    | [] -> []
    | p :: fs' ->
      let (field, e') = p in
      (field, (subst_type_params_expr _UU03c3_ e')) :: (go fs')
    in go
  in
  EStruct (name, lts, (map (subst_type_params_ty _UU03c3_) type_args),
  (go fields))
| EEnum (name, variant, lts, variant_lts, type_args, args) ->
  let go =
    let rec go = function
    | [] -> []
    | e' :: es' -> (subst_type_params_expr _UU03c3_ e') :: (go es')
    in go
  in
  EEnum (name, variant, lts, variant_lts,
  (map (subst_type_params_ty _UU03c3_) type_args), (go args))
| EMatch (discr, branches) ->
  let go =
    let rec go = function
    | [] -> []
    | p :: bs' ->
      let (p0, e') = p in
      let (name, binders) = p0 in
      ((name, binders), (subst_type_params_expr _UU03c3_ e')) :: (go bs')
    in go
  in
  EMatch ((subst_type_params_expr _UU03c3_ discr), (go branches))
| EReplace (p, rhs) -> EReplace (p, (subst_type_params_expr _UU03c3_ rhs))
| EAssign (p, rhs) -> EAssign (p, (subst_type_params_expr _UU03c3_ rhs))
| EDeref e' -> EDeref (subst_type_params_expr _UU03c3_ e')
| EDrop e' -> EDrop (subst_type_params_expr _UU03c3_ e')
| EIf (e1, e2, e3) ->
  EIf ((subst_type_params_expr _UU03c3_ e1),
    (subst_type_params_expr _UU03c3_ e2),
    (subst_type_params_expr _UU03c3_ e3))
| x -> x

(** val instantiate_struct_field_ty :
    lifetime list -> ty list -> field_def -> ty **)

let instantiate_struct_field_ty lifetime_args type_args f =
  subst_type_params_ty type_args (apply_lt_ty lifetime_args f.field_ty)

(** val variant_lifetime_witnesses : Big_int_Z.big_int -> lifetime list **)

let rec variant_lifetime_witnesses n =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> [])
    (fun k -> app (variant_lifetime_witnesses k) ((LBound k) :: []))
    n

(** val instantiate_enum_variant_field_ty :
    lifetime list -> lifetime list -> ty list -> ty -> ty **)

let instantiate_enum_variant_field_ty lifetime_args variant_lifetime_args type_args t =
  subst_type_params_ty type_args
    (apply_lt_ty (app variant_lifetime_args lifetime_args) t)

(** val usage_max_ty_list : ty list -> usage **)

let rec usage_max_ty_list = function
| [] -> UUnrestricted
| t :: rest -> usage_max_decl (ty_usage t) (usage_max_ty_list rest)

(** val usage_max_enum_variants : enum_variant_def list -> usage **)

let rec usage_max_enum_variants = function
| [] -> UUnrestricted
| v :: rest ->
  usage_max_decl (usage_max_ty_list v.enum_variant_fields)
    (usage_max_enum_variants rest)

(** val instantiate_enum_ty : enum_def -> lifetime list -> ty list -> ty **)

let instantiate_enum_ty e lifetime_args type_args =
  MkTy ((usage_max_enum_variants e.enum_variants), (TEnum (e.enum_name,
    lifetime_args, type_args)))

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
     | TEnum (n1, lts1, args1) ->
       (match c2 with
        | TEnum (n2, lts2, args2) ->
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
     | TClosure (env1, ps1, r1) ->
       (match c2 with
        | TClosure (env2, ps2, r2) ->
          (&&)
            ((&&) (lifetime_eqb env1 env2)
              (let rec go xs ys =
                 match xs with
                 | [] -> (match ys with
                          | [] -> true
                          | _ :: _ -> false)
                 | x :: xs' ->
                   (match ys with
                    | [] -> false
                    | y :: ys' -> (&&) (ty_eqb_decl x y) (go xs' ys'))
               in go ps1 ps2))
            (ty_eqb_decl r1 r2)
        | _ -> false)
     | TForall (n1, _UU03a9_1, b1) ->
       (match c2 with
        | TForall (n2, _UU03a9_2, b2) ->
          (&&) ((&&) (eqb n1 n2) (outlives_ctx_eqb_decl _UU03a9_1 _UU03a9_2))
            (ty_eqb_decl b1 b2)
        | _ -> false)
     | TTypeForall (n1, bs1, b1) ->
       (match c2 with
        | TTypeForall (n2, bs2, b2) ->
          (&&)
            ((&&) (eqb n1 n2)
              (let rec go_bounds xs ys =
                 match xs with
                 | [] -> (match ys with
                          | [] -> true
                          | _ :: _ -> false)
                 | x :: xs' ->
                   (match ys with
                    | [] -> false
                    | y :: ys' ->
                      (&&)
                        ((&&)
                          (eqb x.core_bound_type_index
                            y.core_bound_type_index)
                          (let rec go_refs rs ss =
                             match rs with
                             | [] ->
                               (match ss with
                                | [] -> true
                                | _ :: _ -> false)
                             | r :: rs' ->
                               (match ss with
                                | [] -> false
                                | s :: ss' ->
                                  (&&)
                                    ((&&)
                                      ((=) r.core_trait_ref_name
                                        s.core_trait_ref_name)
                                      (let rec go_args as_ bs =
                                         match as_ with
                                         | [] ->
                                           (match bs with
                                            | [] -> true
                                            | _ :: _ -> false)
                                         | a :: as' ->
                                           (match bs with
                                            | [] -> false
                                            | b :: bs' ->
                                              (&&) (ty_eqb_decl a b)
                                                (go_args as' bs'))
                                       in go_args r.core_trait_ref_args
                                            s.core_trait_ref_args))
                                    (go_refs rs' ss'))
                           in go_refs x.core_bound_traits y.core_bound_traits))
                        (go_bounds xs' ys'))
               in go_bounds bs1 bs2))
            (ty_eqb_decl b1 b2)
        | _ -> false)
     | TAssoc (for1, trait1, args1, assoc1) ->
       (match c2 with
        | TAssoc (for2, trait2, args2, assoc2) ->
          (&&)
            ((&&) ((&&) (ty_eqb_decl for1 for2) ((=) trait1 trait2))
              (let rec go xs ys =
                 match xs with
                 | [] -> (match ys with
                          | [] -> true
                          | _ :: _ -> false)
                 | x :: xs' ->
                   (match ys with
                    | [] -> false
                    | y :: ys' -> (&&) (ty_eqb_decl x y) (go xs' ys'))
               in go args1 args2))
            ((=) assoc1 assoc2)
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
             | TEnum (n1, lts1, args1) ->
               (match c_a with
                | TEnum (n2, lts2, args2) ->
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
             | TTypeForall (n1, bs1, b1) ->
               (match c_a with
                | TTypeForall (n2, bs2, b2) ->
                  if (&&) (eqb n1 n2)
                       (ty_eqb_decl (MkTy (UUnrestricted, (TTypeForall (n1,
                         bs1, b1)))) (MkTy (UUnrestricted, (TTypeForall (n2,
                         bs2, b2)))))
                  then Some st
                  else None
                | _ -> None)
             | TAssoc (for1, trait1, args1, assoc1) ->
               (match c_a with
                | TAssoc (for2, trait2, args2, assoc2) ->
                  if (&&) ((=) trait1 trait2) ((=) assoc1 assoc2)
                  then (match match_ty ty_params lt_params fuel' for1 for2 st with
                        | Some st' ->
                          match_tys ty_params lt_params fuel' args1 args2 st'
                        | None -> None)
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
                | _ -> None)
             | _ -> None)))
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
   | TEnum (_, lts, args) ->
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
   | TTypeForall (_, bounds, body) ->
     Big_int_Z.succ_big_int (add (length bounds) (ty_match_fuel body))
   | TAssoc (for_ty, _, trait_args, _) ->
     Big_int_Z.succ_big_int
       (add (ty_match_fuel for_ty)
         (fold_right (fun t1 acc -> add (ty_match_fuel t1) acc)
           Big_int_Z.zero_big_int trait_args))
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

(** val fn_body_params : fn_def -> param list **)

let fn_body_params f =
  app f.fn_params f.fn_captures

(** val fn_binding_params : fn_def -> param list **)

let fn_binding_params f =
  app f.fn_params f.fn_captures

(** val fn_body_ctx : fn_def -> ctx **)

let fn_body_ctx f =
  params_ctx (fn_body_params f)

(** val usage_max : usage -> usage -> usage **)

let usage_max u1 u2 =
  match u1 with
  | ULinear -> ULinear
  | UAffine -> (match u2 with
                | ULinear -> ULinear
                | _ -> UAffine)
  | UUnrestricted -> u2

(** val closure_capture_usage : ty list -> usage **)

let rec closure_capture_usage = function
| [] -> UUnrestricted
| t :: rest -> usage_max (ty_usage t) (closure_capture_usage rest)

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

(** val lookup_expr_branch :
    string -> ((string * ident list) * expr) list -> expr option **)

let rec lookup_expr_branch name = function
| [] -> None
| p :: rest ->
  let (p0, e) = p in
  let (name', _) = p0 in
  if (=) name name' then Some e else lookup_expr_branch name rest

(** val lookup_expr_branch_binders :
    string -> ((string * ident list) * expr) list -> ident list option **)

let rec lookup_expr_branch_binders name = function
| [] -> None
| p :: rest ->
  let (p0, _) = p in
  let (name', binders) = p0 in
  if (=) name name'
  then Some binders
  else lookup_expr_branch_binders name rest

(** val fn_signature_ty_with_usage : usage -> fn_def -> ty **)

let fn_signature_ty_with_usage u f =
  let m = f.fn_lifetimes in
  let body =
    close_fn_ty m (MkTy (UUnrestricted, (TFn
      ((map (fun p -> p.param_ty) f.fn_params), f.fn_ret))))
  in
  if eqb f.fn_type_params Big_int_Z.zero_big_int
  then ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
          (fun _ -> let MkTy (_, core) = body in MkTy (u, core))
          (fun _ -> MkTy (u, (TForall (m,
          (close_fn_outlives m f.fn_outlives), body))))
          m)
  else let type_bounds =
         map (map_core_trait_bound (close_fn_ty m))
           (map core_trait_bound_of_trait_bound f.fn_bounds)
       in
       let type_body = MkTy (UUnrestricted, (TTypeForall (f.fn_type_params,
         type_bounds, body)))
       in
       ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
          (fun _ -> MkTy (u, (TTypeForall (f.fn_type_params, type_bounds,
          body))))
          (fun _ -> MkTy (u, (TForall (m,
          (close_fn_outlives m f.fn_outlives), type_body))))
          m)

(** val closure_value_ty_at : lifetime -> fn_def -> ty list -> ty **)

let closure_value_ty_at env_lt f captured_tys =
  let u = closure_capture_usage captured_tys in
  let m = f.fn_lifetimes in
  let body =
    close_fn_ty m (MkTy (UUnrestricted, (TClosure (env_lt,
      (map (fun p -> p.param_ty) f.fn_params), f.fn_ret))))
  in
  ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
     (fun _ -> let MkTy (_, core) = body in MkTy (u, core))
     (fun _ -> MkTy (u, (TForall (m, (close_fn_outlives m f.fn_outlives),
     body))))
     m)

(** val fn_value_ty : fn_def -> ty **)

let fn_value_ty f =
  fn_signature_ty_with_usage UUnrestricted f

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

(** val apply_type_param : ty list -> param -> param **)

let apply_type_param type_args p =
  { param_mutability = p.param_mutability; param_name = p.param_name;
    param_ty = (subst_type_params_ty type_args p.param_ty) }

(** val apply_type_params : ty list -> param list -> param list **)

let apply_type_params type_args ps =
  map (apply_type_param type_args) ps

(** val subst_type_params_ctx_entry : ty list -> ctx_entry -> ctx_entry **)

let subst_type_params_ctx_entry type_args = function
| (p, m) ->
  let (p0, st) = p in
  let (x, t) = p0 in (((x, (subst_type_params_ty type_args t)), st), m)

(** val subst_type_params_ctx : ty list -> ctx -> ctx **)

let subst_type_params_ctx type_args _UU0393_ =
  map (subst_type_params_ctx_entry type_args) _UU0393_

(** val expr_ref_root : expr -> ident option **)

let rec expr_ref_root = function
| EVar r -> Some r
| EPlace p -> Some (place_root p)
| EDeref e' -> expr_ref_root e'
| _ -> None

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
  then max n (max_ident_index base used')
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
| PField (q, _) -> place_name q

(** val expr_names : expr -> ident list **)

let rec expr_names = function
| EVar x -> x :: []
| ELet (_, x, _, e1, e2) -> x :: (app (expr_names e1) (expr_names e2))
| ELetInfer (_, x, e1, e2) -> x :: (app (expr_names e1) (expr_names e2))
| EMakeClosure (_, captures) -> captures
| EPlace p -> (place_name p) :: []
| ECall (_, args) ->
  let rec go = function
  | [] -> []
  | arg :: rest -> app (expr_names arg) (go rest)
  in go args
| ECallGeneric (_, _, args) ->
  let rec go = function
  | [] -> []
  | arg :: rest -> app (expr_names arg) (go rest)
  in go args
| ECallExpr (callee, args) ->
  let go =
    let rec go = function
    | [] -> []
    | arg :: rest -> app (expr_names arg) (go rest)
    in go
  in
  app (expr_names callee) (go args)
| ECallExprGeneric (callee, _, args) ->
  let go =
    let rec go = function
    | [] -> []
    | arg :: rest -> app (expr_names arg) (go rest)
    in go
  in
  app (expr_names callee) (go args)
| EStruct (_, _, _, fields) ->
  let rec go = function
  | [] -> []
  | p :: rest -> let (_, e0) = p in app (expr_names e0) (go rest)
  in go fields
| EEnum (_, _, _, _, _, payloads) ->
  let rec go = function
  | [] -> []
  | e0 :: rest -> app (expr_names e0) (go rest)
  in go payloads
| EMatch (scrut, branches) ->
  let go =
    let rec go = function
    | [] -> []
    | p :: rest -> let (_, e0) = p in app (expr_names e0) (go rest)
    in go
  in
  app (expr_names scrut) (go branches)
| EReplace (p, e_new) -> (place_name p) :: (expr_names e_new)
| EAssign (p, e_new) -> (place_name p) :: (expr_names e_new)
| EBorrow (_, p) -> (place_name p) :: []
| EDeref e1 -> expr_names e1
| EDrop e1 -> expr_names e1
| EIf (e1, e2, e3) ->
  app (expr_names e1) (app (expr_names e2) (expr_names e3))
| _ -> []

(** val free_vars_expr : expr -> ident list **)

let free_vars_expr =
  expr_names

(** val param_names : param list -> ident list **)

let rec param_names = function
| [] -> []
| p :: ps' -> p.param_name :: (param_names ps')

(** val rename_place : rename_env -> place -> place **)

let rec rename_place _UU03c1_ = function
| PVar x -> PVar (lookup_rename x _UU03c1_)
| PDeref q -> PDeref (rename_place _UU03c1_ q)
| PField (q, f) -> PField ((rename_place _UU03c1_ q), f)

(** val alpha_rename_idents :
    rename_env -> ident list -> ident list -> (ident
    list * rename_env) * ident list **)

let rec alpha_rename_idents _UU03c1_ used = function
| [] -> (([], _UU03c1_), used)
| x :: rest ->
  let x' = fresh_ident x used in
  let used1 = x' :: used in
  let (p, used2) = alpha_rename_idents _UU03c1_ used1 rest in
  let (rest', _UU03c1_') = p in
  (((x' :: rest'), ((x, x') :: _UU03c1_')), used2)

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
| EMakeClosure (fname, captures) ->
  ((EMakeClosure (fname,
    (map (fun x -> lookup_rename x _UU03c1_) captures))), used)
| EPlace p -> ((EPlace (rename_place _UU03c1_ p)), used)
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
| ECallGeneric (fname, type_args, args) ->
  let go =
    let rec go used0 = function
    | [] -> ([], used0)
    | arg :: rest ->
      let (arg', used1) = alpha_rename_expr _UU03c1_ used0 arg in
      let (rest', used2) = go used1 rest in ((arg' :: rest'), used2)
    in go
  in
  let (args', used') = go used args in
  ((ECallGeneric (fname, type_args, args')), used')
| ECallExpr (callee, args) ->
  let (callee', used1) = alpha_rename_expr _UU03c1_ used callee in
  let go =
    let rec go used0 = function
    | [] -> ([], used0)
    | arg :: rest ->
      let (arg', used1') = alpha_rename_expr _UU03c1_ used0 arg in
      let (rest', used2) = go used1' rest in ((arg' :: rest'), used2)
    in go
  in
  let (args', used') = go used1 args in ((ECallExpr (callee', args')), used')
| ECallExprGeneric (callee, type_args, args) ->
  let (callee', used1) = alpha_rename_expr _UU03c1_ used callee in
  let go =
    let rec go used0 = function
    | [] -> ([], used0)
    | arg :: rest ->
      let (arg', used1') = alpha_rename_expr _UU03c1_ used0 arg in
      let (rest', used2) = go used1' rest in ((arg' :: rest'), used2)
    in go
  in
  let (args', used') = go used1 args in
  ((ECallExprGeneric (callee', type_args, args')), used')
| EStruct (name, lts, args, fields) ->
  let go =
    let rec go used0 = function
    | [] -> ([], used0)
    | p :: rest ->
      let (fname, e0) = p in
      let (e', used1) = alpha_rename_expr _UU03c1_ used0 e0 in
      let (rest', used2) = go used1 rest in (((fname, e') :: rest'), used2)
    in go
  in
  let (fields', used') = go used fields in
  ((EStruct (name, lts, args, fields')), used')
| EEnum (enum_name0, variant_name, lts, variant_lts, args, payloads) ->
  let go =
    let rec go used0 = function
    | [] -> ([], used0)
    | e0 :: rest ->
      let (e', used1) = alpha_rename_expr _UU03c1_ used0 e0 in
      let (rest', used2) = go used1 rest in ((e' :: rest'), used2)
    in go
  in
  let (payloads', used') = go used payloads in
  ((EEnum (enum_name0, variant_name, lts, variant_lts, args, payloads')),
  used')
| EMatch (scrut, branches) ->
  let (scrut', used1) = alpha_rename_expr _UU03c1_ used scrut in
  let go =
    let rec go used0 = function
    | [] -> ([], used0)
    | p :: rest ->
      let (p0, e0) = p in
      let (variant_name, binders) = p0 in
      let binder_seed = app binders (app (free_vars_expr e0) used0) in
      let (p1, used1') = alpha_rename_idents _UU03c1_ binder_seed binders in
      let (binders', _UU03c1__branch) = p1 in
      let (e', used2') = alpha_rename_expr _UU03c1__branch used1' e0 in
      let (rest', used3) = go used2' rest in
      ((((variant_name, binders'), e') :: rest'), used3)
    in go
  in
  let (branches', used') = go used1 branches in
  ((EMatch (scrut', branches')), used')
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
  let (p0, used') = alpha_rename_params _UU03c1_ (x' :: used) ps' in
  let (ps'', _UU03c1_') = p0 in
  (((p' :: ps''), ((x, x') :: _UU03c1_')), used')

(** val alpha_rename_fn_def : ident list -> fn_def -> fn_def * ident list **)

let alpha_rename_fn_def used f =
  let used0 =
    app (param_names f.fn_params)
      (app (param_names f.fn_captures) (app (free_vars_expr f.fn_body) used))
  in
  let (p, used1) = alpha_rename_params [] used0 f.fn_params in
  let (params', _UU03c1_) = p in
  let (body', used2) = alpha_rename_expr _UU03c1_ used1 f.fn_body in
  ({ fn_name = f.fn_name; fn_lifetimes = f.fn_lifetimes; fn_outlives =
  f.fn_outlives; fn_captures = f.fn_captures; fn_params = params'; fn_ret =
  f.fn_ret; fn_body = body'; fn_type_params = f.fn_type_params; fn_bounds =
  f.fn_bounds }, used2)

(** val alpha_rename_syntax_go :
    ident list -> syntax -> syntax * ident list **)

let rec alpha_rename_syntax_go used = function
| [] -> ([], used)
| f :: fs ->
  let (f', used1) = alpha_rename_fn_def used f in
  let (fs', used2) = alpha_rename_syntax_go used1 fs in ((f' :: fs'), used2)

(** val alpha_rename_syntax : syntax -> syntax **)

let alpha_rename_syntax s =
  fst (alpha_rename_syntax_go [] s)

type root_atom =
| RStore of ident
| RParam of ident

type root_set = root_atom list

type root_env = (ident * root_set) list

(** val initial_root_env_for_params_origin :
    param list -> param list -> root_env **)

let rec initial_root_env_for_params_origin ps_orig ps_current =
  match ps_orig with
  | [] -> []
  | p_orig :: ps_orig' ->
    (match ps_current with
     | [] -> []
     | p_current :: ps_current' ->
       (p_current.param_name, ((RParam
         p_orig.param_name) :: [])) :: (initial_root_env_for_params_origin
                                         ps_orig' ps_current'))

(** val initial_root_env_for_params : param list -> root_env **)

let initial_root_env_for_params ps =
  initial_root_env_for_params_origin ps ps

(** val initial_root_env_for_fn : fn_def -> root_env **)

let initial_root_env_for_fn f =
  initial_root_env_for_params f.fn_params

(** val root_atom_eqb : root_atom -> root_atom -> bool **)

let root_atom_eqb a b =
  match a with
  | RStore x -> (match b with
                 | RStore y -> ident_eqb x y
                 | RParam _ -> false)
  | RParam x -> (match b with
                 | RStore _ -> false
                 | RParam y -> ident_eqb x y)

(** val root_set_union : root_set -> root_set -> root_set **)

let rec root_set_union a b =
  match a with
  | [] -> b
  | x :: xs ->
    if existsb (root_atom_eqb x) b
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

(** val args_local_store_names_with :
    (expr -> ident list) -> expr list -> ident list **)

let rec args_local_store_names_with expr_names0 = function
| [] -> []
| e :: rest ->
  app (expr_names0 e) (args_local_store_names_with expr_names0 rest)

(** val fields_local_store_names_with :
    (expr -> ident list) -> (string * expr) list -> ident list **)

let rec fields_local_store_names_with expr_names0 = function
| [] -> []
| p :: rest ->
  let (_, e) = p in
  app (expr_names0 e) (fields_local_store_names_with expr_names0 rest)

(** val match_branches_local_store_names_with :
    (expr -> ident list) -> ((string * ident list) * expr) list -> ident list **)

let rec match_branches_local_store_names_with expr_names0 = function
| [] -> []
| p :: rest ->
  let (p0, e) = p in
  let (_, binders) = p0 in
  app binders
    (app (expr_names0 e)
      (match_branches_local_store_names_with expr_names0 rest))

(** val expr_local_store_names : expr -> ident list **)

let rec expr_local_store_names = function
| ELet (_, x, _, e1, e2) ->
  app (expr_local_store_names e1) (x :: (expr_local_store_names e2))
| ELetInfer (_, x, e1, e2) ->
  app (expr_local_store_names e1) (x :: (expr_local_store_names e2))
| ECall (_, args) -> args_local_store_names_with expr_local_store_names args
| ECallGeneric (_, _, args) ->
  args_local_store_names_with expr_local_store_names args
| ECallExpr (callee, args) ->
  app (expr_local_store_names callee)
    (args_local_store_names_with expr_local_store_names args)
| ECallExprGeneric (callee, _, args) ->
  app (expr_local_store_names callee)
    (args_local_store_names_with expr_local_store_names args)
| EStruct (_, _, _, fields) ->
  fields_local_store_names_with expr_local_store_names fields
| EEnum (_, _, _, _, _, payloads) ->
  args_local_store_names_with expr_local_store_names payloads
| EMatch (scrut, branches) ->
  app (expr_local_store_names scrut)
    (match_branches_local_store_names_with expr_local_store_names branches)
| EReplace (_, e_new) -> expr_local_store_names e_new
| EAssign (_, e_new) -> expr_local_store_names e_new
| EDeref e' -> expr_local_store_names e'
| EDrop e' -> expr_local_store_names e'
| EIf (e1, e2, e3) ->
  app (expr_local_store_names e1)
    (app (expr_local_store_names e2) (expr_local_store_names e3))
| _ -> []

(** val args_local_store_names : expr list -> ident list **)

let args_local_store_names args =
  args_local_store_names_with expr_local_store_names args

(** val root_provenance_place_name : place -> ident **)

let rec root_provenance_place_name = function
| PVar x -> x
| PDeref q -> root_provenance_place_name q
| PField (q, _) -> root_provenance_place_name q

(** val root_of_place : place -> root_set **)

let root_of_place p =
  match place_path p with
  | Some p0 -> let (x, _) = p0 in (RStore x) :: []
  | None -> (RStore (root_provenance_place_name p)) :: []

(** val place_root_lookup : root_env -> place -> root_set option **)

let place_root_lookup r p =
  match place_path p with
  | Some p0 -> let (x, _) = p0 in root_env_lookup x r
  | None -> root_env_lookup (root_provenance_place_name p) r

(** val place_borrow_roots : root_env -> place -> root_set option **)

let place_borrow_roots r p =
  match place_path p with
  | Some _ -> Some (root_of_place p)
  | None -> place_root_lookup r p

(** val same_store_root : ident -> root_set -> bool **)

let rec same_store_root x = function
| [] -> true
| r :: rest ->
  (match r with
   | RStore y -> (&&) (ident_eqb y x) (same_store_root x rest)
   | RParam _ -> false)

(** val singleton_store_root : root_set -> ident option **)

let singleton_store_root = function
| [] -> None
| r :: rest ->
  (match r with
   | RStore x -> if same_store_root x rest then Some x else None
   | RParam _ -> None)

(** val resolve_root_set_fuel :
    Big_int_Z.big_int -> root_env -> root_set -> root_set option **)

let rec resolve_root_set_fuel fuel r roots =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> None)
    (fun fuel' ->
    match singleton_store_root roots with
    | Some x ->
      (match root_env_lookup x r with
       | Some roots' ->
         (match singleton_store_root roots' with
          | Some y ->
            if ident_eqb x y
            then Some roots
            else resolve_root_set_fuel fuel' r roots'
          | None -> resolve_root_set_fuel fuel' r roots')
       | None -> Some roots)
    | None -> Some roots)
    fuel

(** val resolve_root_set : root_env -> root_set -> root_set option **)

let resolve_root_set r roots =
  resolve_root_set_fuel (Big_int_Z.succ_big_int (length r)) r roots

(** val place_resolved_roots : root_env -> place -> root_set option **)

let place_resolved_roots r p =
  match place_borrow_roots r p with
  | Some roots -> resolve_root_set r roots
  | None -> None

(** val place_resolved_write_target : root_env -> place -> ident option **)

let rec place_resolved_write_target r = function
| PVar x -> Some x
| PDeref q ->
  (match place_resolved_write_target r q with
   | Some target ->
     (match root_env_lookup target r with
      | Some roots -> singleton_store_root roots
      | None -> None)
   | None -> None)
| PField (q, _) -> place_resolved_write_target r q

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
     | TEnum (name1, lts1, args1) ->
       (match c2 with
        | TEnum (name2, lts2, args2) ->
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
     | TClosure (env1, ts1, r1) ->
       (match c2 with
        | TClosure (env2, ts2, r2) ->
          (&&)
            ((&&) (lifetime_eqb env1 env2)
              (let rec go l1 l2 =
                 match l1 with
                 | [] -> (match l2 with
                          | [] -> true
                          | _ :: _ -> false)
                 | t3 :: l1' ->
                   (match l2 with
                    | [] -> false
                    | t4 :: l2' -> (&&) (ty_eqb t3 t4) (go l1' l2'))
               in go ts1 ts2))
            (ty_eqb r1 r2)
        | _ -> false)
     | TForall (n1, _UU03a9_1, b1) ->
       (match c2 with
        | TForall (n2, _UU03a9_2, b2) ->
          (&&) ((&&) (Nat.eqb n1 n2) (outlives_ctx_eqb _UU03a9_1 _UU03a9_2))
            (ty_eqb b1 b2)
        | _ -> false)
     | TTypeForall (n1, bs1, b1) ->
       (match c2 with
        | TTypeForall (n2, bs2, b2) ->
          (&&)
            ((&&) (Nat.eqb n1 n2)
              (let rec go_bounds xs ys =
                 match xs with
                 | [] -> (match ys with
                          | [] -> true
                          | _ :: _ -> false)
                 | x :: xs' ->
                   (match ys with
                    | [] -> false
                    | y :: ys' ->
                      (&&)
                        ((&&)
                          (Nat.eqb x.core_bound_type_index
                            y.core_bound_type_index)
                          (let rec go_refs rs ss =
                             match rs with
                             | [] ->
                               (match ss with
                                | [] -> true
                                | _ :: _ -> false)
                             | r :: rs' ->
                               (match ss with
                                | [] -> false
                                | s :: ss' ->
                                  (&&)
                                    ((&&)
                                      ((=) r.core_trait_ref_name
                                        s.core_trait_ref_name)
                                      (let rec go_args as_ bs =
                                         match as_ with
                                         | [] ->
                                           (match bs with
                                            | [] -> true
                                            | _ :: _ -> false)
                                         | a :: as' ->
                                           (match bs with
                                            | [] -> false
                                            | b :: bs' ->
                                              (&&) (ty_eqb a b)
                                                (go_args as' bs'))
                                       in go_args r.core_trait_ref_args
                                            s.core_trait_ref_args))
                                    (go_refs rs' ss'))
                           in go_refs x.core_bound_traits y.core_bound_traits))
                        (go_bounds xs' ys'))
               in go_bounds bs1 bs2))
            (ty_eqb b1 b2)
        | _ -> false)
     | TAssoc (for1, trait1, args1, assoc1) ->
       (match c2 with
        | TAssoc (for2, trait2, args2, assoc2) ->
          (&&)
            ((&&) ((&&) (ty_eqb for1 for2) ((=) trait1 trait2))
              (let rec go_args l1 l2 =
                 match l1 with
                 | [] -> (match l2 with
                          | [] -> true
                          | _ :: _ -> false)
                 | t3 :: l1' ->
                   (match l2 with
                    | [] -> false
                    | t4 :: l2' -> (&&) (ty_eqb t3 t4) (go_args l1' l2'))
               in go_args args1 args2))
            ((=) assoc1 assoc2)
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
  | TEnum (name1, lts1, args1) ->
    (match c2 with
     | TEnum (name2, lts2, args2) ->
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
  | TClosure (env1, ts1, r1) ->
    (match c2 with
     | TClosure (env2, ts2, r2) ->
       (&&)
         ((&&) (lifetime_eqb env1 env2)
           (let rec go l1 l2 =
              match l1 with
              | [] -> (match l2 with
                       | [] -> true
                       | _ :: _ -> false)
              | t1 :: l1' ->
                (match l2 with
                 | [] -> false
                 | t2 :: l2' -> (&&) (ty_eqb t1 t2) (go l1' l2'))
            in go ts1 ts2))
         (ty_eqb r1 r2)
     | _ -> false)
  | TForall (n1, _UU03a9_1, b1) ->
    (match c2 with
     | TForall (n2, _UU03a9_2, b2) ->
       (&&) ((&&) (Nat.eqb n1 n2) (outlives_ctx_eqb _UU03a9_1 _UU03a9_2))
         (ty_eqb b1 b2)
     | _ -> false)
  | TTypeForall (n1, bs1, b1) ->
    (match c2 with
     | TTypeForall (n2, bs2, b2) ->
       (&&)
         ((&&) (Nat.eqb n1 n2)
           (let rec go_bounds xs ys =
              match xs with
              | [] -> (match ys with
                       | [] -> true
                       | _ :: _ -> false)
              | x :: xs' ->
                (match ys with
                 | [] -> false
                 | y :: ys' ->
                   (&&)
                     ((&&)
                       (Nat.eqb x.core_bound_type_index
                         y.core_bound_type_index)
                       (let rec go_refs rs ss =
                          match rs with
                          | [] -> (match ss with
                                   | [] -> true
                                   | _ :: _ -> false)
                          | r :: rs' ->
                            (match ss with
                             | [] -> false
                             | s :: ss' ->
                               (&&)
                                 ((&&)
                                   ((=) r.core_trait_ref_name
                                     s.core_trait_ref_name)
                                   (let rec go_args as_ bs =
                                      match as_ with
                                      | [] ->
                                        (match bs with
                                         | [] -> true
                                         | _ :: _ -> false)
                                      | a :: as' ->
                                        (match bs with
                                         | [] -> false
                                         | b :: bs' ->
                                           (&&) (ty_eqb a b) (go_args as' bs'))
                                    in go_args r.core_trait_ref_args
                                         s.core_trait_ref_args))
                                 (go_refs rs' ss'))
                        in go_refs x.core_bound_traits y.core_bound_traits))
                     (go_bounds xs' ys'))
            in go_bounds bs1 bs2))
         (ty_eqb b1 b2)
     | _ -> false)
  | TAssoc (for1, trait1, args1, assoc1) ->
    (match c2 with
     | TAssoc (for2, trait2, args2, assoc2) ->
       (&&)
         ((&&) ((&&) (ty_eqb for1 for2) ((=) trait1 trait2))
           (let rec go_args l1 l2 =
              match l1 with
              | [] -> (match l2 with
                       | [] -> true
                       | _ :: _ -> false)
              | t1 :: l1' ->
                (match l2 with
                 | [] -> false
                 | t2 :: l2' -> (&&) (ty_eqb t1 t2) (go_args l1' l2'))
            in go_args args1 args2))
         ((=) assoc1 assoc2)
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
   | TEnum (_, lts, args) ->
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
   | TClosure (_, ts, r) ->
     Big_int_Z.succ_big_int
       (let rec go = function
        | [] -> ty_depth r
        | t0 :: l' -> add (Big_int_Z.succ_big_int (ty_depth t0)) (go l')
        in go ts)
   | TForall (_, _UU03a9_, body) ->
     Big_int_Z.succ_big_int (add (length _UU03a9_) (ty_depth body))
   | TTypeForall (_, bounds, body) ->
     Big_int_Z.succ_big_int
       (add (ty_depth body)
         (let rec go_bounds = function
          | [] -> Big_int_Z.zero_big_int
          | b :: bs' ->
            add
              (let rec go_refs = function
               | [] -> Big_int_Z.zero_big_int
               | tr :: rs' ->
                 add
                   (let rec go_args = function
                    | [] -> Big_int_Z.zero_big_int
                    | arg :: args' ->
                      add (Big_int_Z.succ_big_int (ty_depth arg))
                        (go_args args')
                    in go_args tr.core_trait_ref_args)
                   (go_refs rs')
               in go_refs b.core_bound_traits)
              (go_bounds bs')
          in go_bounds bounds))
   | TAssoc (for_ty, _, trait_args, _) ->
     Big_int_Z.succ_big_int
       (add (ty_depth for_ty)
         (let rec go_args = function
          | [] -> Big_int_Z.zero_big_int
          | arg :: args' ->
            add (Big_int_Z.succ_big_int (ty_depth arg)) (go_args args')
          in go_args trait_args))
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
       | TFn (params_a, ret_a) ->
         let ca = TFn (params_a, ret_a) in
         (match ty_core t_expected with
          | TFn (params_e, ret_e) ->
            (&&)
              (ty_compatible_args_contra_b_fuel (ty_compatible_b_fuel fuel')
                _UU03a9_ params_a params_e)
              (ty_compatible_b_fuel fuel' _UU03a9_ ret_a ret_e)
          | TClosure (_, params_e, ret_e) ->
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
       | TClosure (env_a, params_a, ret_a) ->
         let ca = TClosure (env_a, params_a, ret_a) in
         (match ty_core t_expected with
          | TClosure (env_e, params_e, ret_e) ->
            (&&)
              ((&&) (outlives_b _UU03a9_ env_a env_e)
                (ty_compatible_args_contra_b_fuel
                  (ty_compatible_b_fuel fuel') _UU03a9_ params_a params_e))
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
       | TTypeForall (na, ba, ta) ->
         let ca = TTypeForall (na, ba, ta) in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l -> ty_core_eqb ca (TForall (n, (p :: l), tb)))
          | TTypeForall (nb, bb, tb) ->
            (&&)
              ((&&) (Nat.eqb na nb)
                (let rec go_bounds xs ys =
                   match xs with
                   | [] -> (match ys with
                            | [] -> true
                            | _ :: _ -> false)
                   | x :: xs' ->
                     (match ys with
                      | [] -> false
                      | y :: ys' ->
                        (&&)
                          ((&&)
                            (Nat.eqb x.core_bound_type_index
                              y.core_bound_type_index)
                            (let rec go_refs rs ss =
                               match rs with
                               | [] ->
                                 (match ss with
                                  | [] -> true
                                  | _ :: _ -> false)
                               | r :: rs' ->
                                 (match ss with
                                  | [] -> false
                                  | s :: ss' ->
                                    (&&)
                                      ((&&)
                                        ((=) r.core_trait_ref_name
                                          s.core_trait_ref_name)
                                        (let rec go_args as_ bs =
                                           match as_ with
                                           | [] ->
                                             (match bs with
                                              | [] -> true
                                              | _ :: _ -> false)
                                           | a :: as' ->
                                             (match bs with
                                              | [] -> false
                                              | b :: bs' ->
                                                (&&) (ty_eqb a b)
                                                  (go_args as' bs'))
                                         in go_args r.core_trait_ref_args
                                              s.core_trait_ref_args))
                                      (go_refs rs' ss'))
                             in go_refs x.core_bound_traits
                                  y.core_bound_traits))
                          (go_bounds xs' ys'))
                 in go_bounds ba bb))
              (ty_compatible_b_fuel fuel' _UU03a9_ ta tb)
          | x -> ty_core_eqb ca x)
       | TAssoc (t, s, l, s0) ->
         let ca = TAssoc (t, s, l, s0) in
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l0 -> ty_core_eqb ca (TForall (n, (p :: l0), tb)))
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
          | x -> ty_core_eqb ca x)
       | x ->
         (match ty_core t_expected with
          | TForall (n, o, tb) ->
            (match o with
             | [] ->
               (&&) (negb (contains_lbound_ty tb))
                 (ty_compatible_b_fuel fuel' _UU03a9_ t_actual tb)
             | p :: l1 -> ty_core_eqb x (TForall (n, (p :: l1), tb)))
          | x0 -> ty_core_eqb x x0)))
    fuel

(** val ty_compatible_b : outlives_ctx -> ty -> ty -> bool **)

let ty_compatible_b _UU03a9_ t_actual t_expected =
  ty_compatible_b_fuel (add (ty_depth t_actual) (ty_depth t_expected))
    _UU03a9_ t_actual t_expected

(** val capture_ref_free_ty_b_fuel :
    Big_int_Z.big_int -> global_env -> ty -> bool **)

let rec capture_ref_free_ty_b_fuel fuel env t =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> false)
    (fun fuel' ->
    let MkTy (_, t0) = t in
    (match t0 with
     | TUnits -> true
     | TIntegers -> true
     | TFloats -> true
     | TBooleans -> true
     | TStruct (name, lts, args) ->
       (&&) (forallb (capture_ref_free_ty_b_fuel fuel' env) args)
         (match lookup_struct name env with
          | Some sdef ->
            forallb (fun f ->
              capture_ref_free_ty_b_fuel fuel' env
                (instantiate_struct_field_ty lts args f))
              sdef.struct_fields
          | None -> false)
     | TEnum (name, lts, args) ->
       (&&) (forallb (capture_ref_free_ty_b_fuel fuel' env) args)
         (match lookup_enum name env with
          | Some edef ->
            forallb (fun v ->
              forallb (fun t1 ->
                capture_ref_free_ty_b_fuel fuel' env
                  (instantiate_enum_variant_field_ty lts [] args t1))
                v.enum_variant_fields)
              edef.enum_variants
          | None -> false)
     | TFn (ts, r) ->
       (&&) (forallb (capture_ref_free_ty_b_fuel fuel' env) ts)
         (capture_ref_free_ty_b_fuel fuel' env r)
     | TForall (_, _, body) -> capture_ref_free_ty_b_fuel fuel' env body
     | TTypeForall (_, _, body) -> capture_ref_free_ty_b_fuel fuel' env body
     | TAssoc (for_ty, _, trait_args, _) ->
       (&&) (capture_ref_free_ty_b_fuel fuel' env for_ty)
         (forallb (capture_ref_free_ty_b_fuel fuel' env) trait_args)
     | _ -> false))
    fuel

(** val capture_ref_free_ty_b : global_env -> ty -> bool **)

let capture_ref_free_ty_b env t =
  capture_ref_free_ty_b_fuel (Big_int_Z.succ_big_int
    (add (add (length env.env_structs) (length env.env_enums)) (ty_depth t)))
    env t

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

(** val ctx_remove_b : ident -> ctx -> ctx **)

let rec ctx_remove_b x = function
| [] -> []
| c :: t ->
  let (p, m) = c in
  let (p0, st) = p in
  let (n, t0) = p0 in
  if ident_eqb x n then t else (((n, t0), st), m) :: (ctx_remove_b x t)

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
   | TEnum (_, lts, args) ->
     (&&) (forallb (wf_lifetime_at_b bound_depth _UU0394_) lts)
       (forallb (wf_type_at_b bound_depth _UU0394_) args)
   | TFn (ts, r) ->
     (&&) (forallb (wf_type_at_b bound_depth _UU0394_) ts)
       (wf_type_at_b bound_depth _UU0394_ r)
   | TClosure (l, ts, r) ->
     (&&)
       ((&&) (wf_lifetime_at_b bound_depth _UU0394_ l)
         (forallb (wf_type_at_b bound_depth _UU0394_) ts))
       (wf_type_at_b bound_depth _UU0394_ r)
   | TForall (n, _UU03a9_, body) ->
     (&&) (wf_outlives_at_b (add n bound_depth) _UU0394_ _UU03a9_)
       (wf_type_at_b (add n bound_depth) _UU0394_ body)
   | TTypeForall (_, bounds, body) ->
     (&&)
       (forallb (fun b ->
         forallb (fun tr ->
           forallb (wf_type_at_b bound_depth _UU0394_) tr.core_trait_ref_args)
           b.core_bound_traits)
         bounds)
       (wf_type_at_b bound_depth _UU0394_ body)
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
| ErrEnumNotFound of string
| ErrVariantNotFound of string
| ErrNotAnEnum of ty typeCore
| ErrDuplicateVariant of string
| ErrMissingVariant of string
| ErrMatchPayloadUnsupported of string
| ErrFieldNotFound of string
| ErrDuplicateField of string
| ErrMissingField of string
| ErrTraitImplNotFound of string * ty
| ErrTraitImplAmbiguous of string * ty
| ErrTypeArgInferenceFailed
| ErrEndToEndSafetyGateFailed
| ErrGlobalNamesNotUnique
| ErrInFunction of ident * infer_error

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

(** val no_captures_b : fn_def -> bool **)

let no_captures_b f =
  match f.fn_captures with
  | [] -> true
  | _ :: _ -> false

type 'a infer_result =
| Infer_ok of 'a
| Infer_err of infer_error

(** val infer_if_bool :
    bool -> 'a1 infer_result -> 'a1 infer_result -> 'a1 infer_result **)

let infer_if_bool b ok err =
  if b then ok else err

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

(** val subst_type_params_trait_ref : ty list -> trait_ref -> trait_ref **)

let subst_type_params_trait_ref args tr =
  { trait_ref_name = tr.trait_ref_name; trait_ref_args =
    (map (subst_type_params_ty args) tr.trait_ref_args) }

(** val subst_type_params_trait_bound :
    ty list -> trait_bound -> trait_bound **)

let subst_type_params_trait_bound args b =
  { bound_type_index = b.bound_type_index; bound_traits =
    (map (subst_type_params_trait_ref args) b.bound_traits) }

(** val subst_type_params_trait_bounds :
    ty list -> trait_bound list -> trait_bound list **)

let subst_type_params_trait_bounds args bounds =
  map (subst_type_params_trait_bound args) bounds

(** val ty_list_eqb : ty list -> ty list -> bool **)

let rec ty_list_eqb xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs' ->
    (match ys with
     | [] -> false
     | y :: ys' -> (&&) (ty_eqb x y) (ty_list_eqb xs' ys'))

(** val trait_ref_eqb : trait_ref -> trait_ref -> bool **)

let trait_ref_eqb a b =
  (&&) ((=) a.trait_ref_name b.trait_ref_name)
    (ty_list_eqb a.trait_ref_args b.trait_ref_args)

(** val local_bound_satisfies_trait :
    trait_bound list -> Big_int_Z.big_int -> trait_ref -> bool **)

let local_bound_satisfies_trait bounds type_index tr =
  existsb (fun b ->
    (&&) (Nat.eqb b.bound_type_index type_index)
      (existsb (trait_ref_eqb tr) b.bound_traits))
    bounds

(** val local_bounds_satisfy_trait_ref_for_ty :
    trait_bound list -> trait_ref -> ty -> bool **)

let local_bounds_satisfy_trait_ref_for_ty bounds tr for_ty =
  match ty_core for_ty with
  | TParam i -> local_bound_satisfies_trait bounds i tr
  | _ -> false

(** val check_trait_ref_for_ty :
    global_env -> trait_ref -> ty -> infer_error option **)

let check_trait_ref_for_ty env tr for_ty =
  if local_bounds_satisfy_trait_ref_for_ty env.env_local_bounds tr for_ty
  then None
  else trait_impl_error_with_args env tr.trait_ref_name tr.trait_ref_args
         for_ty

(** val check_trait_refs_for_ty :
    global_env -> trait_ref list -> ty -> infer_error option **)

let rec check_trait_refs_for_ty env traits for_ty =
  match traits with
  | [] -> None
  | tr :: rest ->
    (match check_trait_ref_for_ty env tr for_ty with
     | Some err -> Some err
     | None -> check_trait_refs_for_ty env rest for_ty)

(** val type_arg_list_set_nth :
    Big_int_Z.big_int -> ty option -> ty option list -> ty option list **)

let rec type_arg_list_set_nth i v _UU03c3_ =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ ->
    match _UU03c3_ with
    | [] -> []
    | _ :: rest -> v :: rest)
    (fun i' ->
    match _UU03c3_ with
    | [] -> []
    | h :: rest -> h :: (type_arg_list_set_nth i' v rest))
    i

(** val type_arg_subst_vec_add :
    ty option list -> Big_int_Z.big_int -> ty -> ty option list option **)

let type_arg_subst_vec_add _UU03c3_ i t =
  match nth_error _UU03c3_ i with
  | Some o ->
    (match o with
     | Some t_old -> if ty_eqb t_old t then Some _UU03c3_ else None
     | None -> Some (type_arg_list_set_nth i (Some t) _UU03c3_))
  | None -> None

(** val infer_type_args_from_ty :
    Big_int_Z.big_int -> ty -> ty -> ty option list -> ty option list option **)

let rec infer_type_args_from_ty fuel formal actual _UU03c3_ =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> None)
    (fun fuel' ->
    let MkTy (u_f, t) = formal in
    (match t with
     | TParam i ->
       let MkTy (_, c_a) = actual in
       type_arg_subst_vec_add _UU03c3_ i (MkTy (u_f, c_a))
     | TStruct (name_f, lts_f, args_f) ->
       let MkTy (_, t0) = actual in
       (match t0 with
        | TStruct (name_a, lts_a, args_a) ->
          if (&&) ((=) name_f name_a) (lifetime_list_eqb lts_f lts_a)
          then infer_type_args_from_tys fuel' args_f args_a _UU03c3_
          else None
        | _ ->
          if ty_core_eqb (ty_core formal) (ty_core actual)
          then Some _UU03c3_
          else None)
     | TEnum (name_f, lts_f, args_f) ->
       let MkTy (_, t0) = actual in
       (match t0 with
        | TEnum (name_a, lts_a, args_a) ->
          if (&&) ((=) name_f name_a) (lifetime_list_eqb lts_f lts_a)
          then infer_type_args_from_tys fuel' args_f args_a _UU03c3_
          else None
        | _ ->
          if ty_core_eqb (ty_core formal) (ty_core actual)
          then Some _UU03c3_
          else None)
     | TFn (ps_f, ret_f) ->
       let MkTy (_, t0) = actual in
       (match t0 with
        | TFn (ps_a, ret_a) ->
          (match infer_type_args_from_tys fuel' ps_f ps_a _UU03c3_ with
           | Some _UU03c3_' ->
             infer_type_args_from_ty fuel' ret_f ret_a _UU03c3_'
           | None -> None)
        | _ ->
          if ty_core_eqb (ty_core formal) (ty_core actual)
          then Some _UU03c3_
          else None)
     | TClosure (_, ps_f, ret_f) ->
       let MkTy (_, t0) = actual in
       (match t0 with
        | TClosure (_, ps_a, ret_a) ->
          (match infer_type_args_from_tys fuel' ps_f ps_a _UU03c3_ with
           | Some _UU03c3_' ->
             infer_type_args_from_ty fuel' ret_f ret_a _UU03c3_'
           | None -> None)
        | _ ->
          if ty_core_eqb (ty_core formal) (ty_core actual)
          then Some _UU03c3_
          else None)
     | TForall (n_f, _UU03a9__f, body_f) ->
       let MkTy (_, t0) = actual in
       (match t0 with
        | TForall (n_a, _UU03a9__a, body_a) ->
          if (&&) (Nat.eqb n_f n_a) (outlives_ctx_eqb _UU03a9__f _UU03a9__a)
          then infer_type_args_from_ty fuel' body_f body_a _UU03c3_
          else None
        | _ ->
          if ty_core_eqb (ty_core formal) (ty_core actual)
          then Some _UU03c3_
          else None)
     | TTypeForall (n_f, bounds_f, body_f) ->
       let MkTy (_, t0) = actual in
       (match t0 with
        | TTypeForall (n_a, bounds_a, body_a) ->
          if (&&) (Nat.eqb n_f n_a)
               (ty_eqb (MkTy (UUnrestricted, (TTypeForall (n_f, bounds_f,
                 body_f)))) (MkTy (UUnrestricted, (TTypeForall (n_a,
                 bounds_a, body_a)))))
          then Some _UU03c3_
          else None
        | _ ->
          if ty_core_eqb (ty_core formal) (ty_core actual)
          then Some _UU03c3_
          else None)
     | TRef (_, rk_f, inner_f) ->
       let MkTy (_, t0) = actual in
       (match t0 with
        | TRef (_, rk_a, inner_a) ->
          if ref_kind_eqb rk_f rk_a
          then infer_type_args_from_ty fuel' inner_f inner_a _UU03c3_
          else None
        | _ ->
          if ty_core_eqb (ty_core formal) (ty_core actual)
          then Some _UU03c3_
          else None)
     | _ ->
       if ty_core_eqb (ty_core formal) (ty_core actual)
       then Some _UU03c3_
       else None))
    fuel

(** val infer_type_args_from_tys :
    Big_int_Z.big_int -> ty list -> ty list -> ty option list -> ty option
    list option **)

and infer_type_args_from_tys fuel formals actuals _UU03c3_ =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> None)
    (fun fuel' ->
    match formals with
    | [] -> (match actuals with
             | [] -> Some _UU03c3_
             | _ :: _ -> None)
    | f :: fs ->
      (match actuals with
       | [] -> None
       | a :: as_ ->
         (match infer_type_args_from_ty fuel' f a _UU03c3_ with
          | Some _UU03c3_' -> infer_type_args_from_tys fuel' fs as_ _UU03c3_'
          | None -> None)))
    fuel

(** val infer_type_args_from_params :
    param list -> ty list -> ty option list -> ty option list option **)

let rec infer_type_args_from_params params arg_tys _UU03c3_ =
  match params with
  | [] -> (match arg_tys with
           | [] -> Some _UU03c3_
           | _ :: _ -> None)
  | p :: ps ->
    (match arg_tys with
     | [] -> None
     | a :: as_ ->
       (match infer_type_args_from_ty
                (add (ty_depth p.param_ty) (ty_depth a)) p.param_ty a _UU03c3_ with
        | Some _UU03c3_' -> infer_type_args_from_params ps as_ _UU03c3_'
        | None -> None))

(** val finalize_type_args : ty option list -> ty list option **)

let rec finalize_type_args = function
| [] -> Some []
| o :: rest ->
  (match o with
   | Some t ->
     (match finalize_type_args rest with
      | Some ts -> Some (t :: ts)
      | None -> None)
   | None -> None)

(** val infer_call_type_args_expected :
    fn_def -> ty list -> ty option -> ty list option **)

let infer_call_type_args_expected fdef arg_tys expected =
  match infer_type_args_from_params fdef.fn_params arg_tys
          (repeat None fdef.fn_type_params) with
  | Some _UU03c3__args ->
    let _UU03c3__expected =
      match expected with
      | Some t_expected ->
        infer_type_args_from_ty
          (add (ty_depth fdef.fn_ret) (ty_depth t_expected)) fdef.fn_ret
          t_expected _UU03c3__args
      | None -> Some _UU03c3__args
    in
    (match _UU03c3__expected with
     | Some _UU03c3_ -> finalize_type_args _UU03c3_
     | None -> None)
  | None -> None

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

(** val complete_bound_sigma_with_vars_from :
    Big_int_Z.big_int -> Big_int_Z.big_int -> lifetime option list ->
    lifetime option list **)

let rec complete_bound_sigma_with_vars_from n i = function
| [] -> []
| o :: rest ->
  (match o with
   | Some l ->
     (Some
       l) :: (complete_bound_sigma_with_vars_from n (Big_int_Z.succ_big_int
               i) rest)
   | None ->
     (if Nat.ltb i n then Some (LVar i) else None) :: (complete_bound_sigma_with_vars_from
                                                        n
                                                        (Big_int_Z.succ_big_int
                                                        i) rest))

(** val complete_bound_sigma_with_vars :
    Big_int_Z.big_int -> lifetime option list -> lifetime option list **)

let complete_bound_sigma_with_vars n _UU03c3_ =
  complete_bound_sigma_with_vars_from n Big_int_Z.zero_big_int _UU03c3_

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

(** val tys_depth : ty list -> Big_int_Z.big_int **)

let rec tys_depth = function
| [] -> Big_int_Z.zero_big_int
| t :: ts' -> add (ty_depth t) (tys_depth ts')

(** val infer_type_forall_args :
    Big_int_Z.big_int -> ty list -> ty list -> ty list option **)

let infer_type_forall_args type_params param_tys arg_tys =
  match infer_type_args_from_tys (Big_int_Z.succ_big_int
          (add (tys_depth param_tys) (tys_depth arg_tys))) param_tys arg_tys
          (repeat None type_params) with
  | Some _UU03c3_ -> finalize_type_args _UU03c3_
  | None -> None

(** val check_type_forall_bounds :
    global_env -> ty core_trait_bound list -> ty list -> infer_error option **)

let check_type_forall_bounds env bounds type_args =
  check_struct_bounds env (trait_bounds_of_core_trait_bounds bounds) type_args

(** val infer_type_forall_call_env :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> ty core_trait_bound
    list -> ty -> ty list -> ty infer_result **)

let infer_type_forall_call_env env _UU03a9_ type_params bounds body arg_tys =
  match ty_core body with
  | TFn (param_tys, ret) ->
    (match infer_type_forall_args type_params param_tys arg_tys with
     | Some type_args ->
       (match check_type_forall_bounds env bounds type_args with
        | Some err -> Infer_err err
        | None ->
          (match check_arg_tys _UU03a9_ arg_tys
                   (map (subst_type_params_ty type_args) param_tys) with
           | Some err -> Infer_err err
           | None -> Infer_ok (subst_type_params_ty type_args ret)))
     | None -> Infer_err ErrTypeArgInferenceFailed)
  | x -> Infer_err (ErrMalformedHrtBody x)

(** val infer_type_forall_call_env_elab :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> ty core_trait_bound
    list -> ty -> ty list -> (ty list * ty) infer_result **)

let infer_type_forall_call_env_elab env _UU03a9_ type_params bounds body arg_tys =
  match ty_core body with
  | TFn (param_tys, ret) ->
    (match infer_type_forall_args type_params param_tys arg_tys with
     | Some type_args ->
       (match check_type_forall_bounds env bounds type_args with
        | Some err -> Infer_err err
        | None ->
          (match check_arg_tys _UU03a9_ arg_tys
                   (map (subst_type_params_ty type_args) param_tys) with
           | Some err -> Infer_err err
           | None ->
             Infer_ok (type_args, (subst_type_params_ty type_args ret))))
     | None -> Infer_err ErrTypeArgInferenceFailed)
  | x -> Infer_err (ErrMalformedHrtBody x)

(** val shared_ref_lifetime_of_ty : ty -> lifetime option **)

let shared_ref_lifetime_of_ty = function
| MkTy (_, t0) ->
  (match t0 with
   | TRef (l, r, _) -> (match r with
                        | RShared -> Some l
                        | RUnique -> None)
   | _ -> None)

(** val collect_shared_ref_lifetimes : ty list -> lifetime list **)

let rec collect_shared_ref_lifetimes = function
| [] -> []
| t :: rest ->
  (match shared_ref_lifetime_of_ty t with
   | Some l -> l :: (collect_shared_ref_lifetimes rest)
   | None -> collect_shared_ref_lifetimes rest)

(** val all_outlive_b : outlives_ctx -> lifetime list -> lifetime -> bool **)

let rec all_outlive_b _UU03a9_ lts env_lt =
  match lts with
  | [] -> true
  | l :: rest ->
    (&&) (outlives_b _UU03a9_ l env_lt) (all_outlive_b _UU03a9_ rest env_lt)

(** val find_closure_env_lifetime :
    outlives_ctx -> lifetime list -> lifetime list -> lifetime option **)

let rec find_closure_env_lifetime _UU03a9_ lts = function
| [] -> None
| l :: rest ->
  if all_outlive_b _UU03a9_ lts l
  then Some l
  else find_closure_env_lifetime _UU03a9_ lts rest

(** val infer_closure_env_lifetime :
    outlives_ctx -> ty list -> lifetime infer_result **)

let infer_closure_env_lifetime _UU03a9_ captured_tys =
  let lts = collect_shared_ref_lifetimes captured_tys in
  (match lts with
   | [] -> Infer_ok LStatic
   | _ :: _ ->
     (match find_closure_env_lifetime _UU03a9_ lts lts with
      | Some env_lt -> Infer_ok env_lt
      | None -> Infer_err ErrLifetimeConflict))

(** val closure_capture_allowed_b :
    global_env -> outlives_ctx -> lifetime -> ty -> bool **)

let closure_capture_allowed_b env _UU03a9_ env_lt t =
  (||) (capture_ref_free_ty_b env t)
    (let MkTy (_, t0) = t in
     (match t0 with
      | TRef (l, r, _) ->
        (match r with
         | RShared -> outlives_b _UU03a9_ l env_lt
         | RUnique -> false)
      | _ -> false))

(** val closure_captures_allowed_b :
    global_env -> outlives_ctx -> lifetime -> ty list -> bool **)

let rec closure_captures_allowed_b env _UU03a9_ env_lt = function
| [] -> true
| t :: rest ->
  (&&) (closure_capture_allowed_b env _UU03a9_ env_lt t)
    (closure_captures_allowed_b env _UU03a9_ env_lt rest)

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

(** val lookup_branch_b :
    string -> ((string * ident list) * expr) list -> expr option **)

let lookup_branch_b =
  lookup_expr_branch

(** val has_branch_b :
    string -> ((string * ident list) * expr) list -> bool **)

let rec has_branch_b name = function
| [] -> false
| p :: rest ->
  let (p0, _) = p in
  let (name', _) = p0 in
  if (=) name name' then true else has_branch_b name rest

(** val first_duplicate_branch :
    ((string * ident list) * expr) list -> string option **)

let rec first_duplicate_branch = function
| [] -> None
| b :: rest ->
  let name = match_branch_name b in
  if has_branch_b name rest then Some name else first_duplicate_branch rest

(** val first_unknown_variant_branch :
    ((string * ident list) * expr) list -> enum_variant_def list -> string
    option **)

let rec first_unknown_variant_branch branches defs =
  match branches with
  | [] -> None
  | p :: rest ->
    let (p0, _) = p in
    let (name, _) = p0 in
    (match lookup_enum_variant name defs with
     | Some _ -> first_unknown_variant_branch rest defs
     | None -> Some name)

(** val first_missing_variant_branch :
    enum_variant_def list -> ((string * ident list) * expr) list -> string
    option **)

let rec first_missing_variant_branch defs branches =
  match defs with
  | [] -> None
  | v :: rest ->
    if has_branch_b v.enum_variant_name branches
    then first_missing_variant_branch rest branches
    else Some v.enum_variant_name

(** val first_payload_binder_branch :
    ((string * ident list) * expr) list -> string option **)

let rec first_payload_binder_branch = function
| [] -> None
| p :: rest ->
  let (p0, _) = p in
  let (name, l) = p0 in
  (match l with
   | [] -> first_payload_binder_branch rest
   | _ :: _ -> Some name)

(** val first_payload_variant : enum_variant_def list -> string option **)

let rec first_payload_variant = function
| [] -> None
| v :: rest ->
  (match v.enum_variant_fields with
   | [] -> first_payload_variant rest
   | _ :: _ -> Some v.enum_variant_name)

(** val first_unsupported_match_payload :
    ((string * ident list) * expr) list -> enum_variant_def list -> string
    option **)

let first_unsupported_match_payload branches defs =
  match first_payload_binder_branch branches with
  | Some name -> Some name
  | None -> first_payload_variant defs

(** val usage_max_tys_nonempty : ty -> ty list -> usage **)

let rec usage_max_tys_nonempty head = function
| [] -> ty_usage head
| t :: rest -> usage_max (ty_usage head) (usage_max_tys_nonempty t rest)

(** val ctx_merge_many : ctx -> ctx list -> ctx option **)

let rec ctx_merge_many head = function
| [] -> Some head
| c :: rest ->
  (match ctx_merge head c with
   | Some merged -> ctx_merge_many merged rest
   | None -> None)

(** val match_binder_params :
    ident list -> ty list -> param list infer_result **)

let rec match_binder_params binders tys =
  match binders with
  | [] ->
    (match tys with
     | [] -> Infer_ok []
     | _ :: _ -> Infer_err ErrArityMismatch)
  | x :: xs ->
    (match tys with
     | [] -> Infer_err ErrArityMismatch
     | t :: ts ->
       (match match_binder_params xs ts with
        | Infer_ok ps ->
          Infer_ok ({ param_mutability = MImmutable; param_name = x;
            param_ty = t } :: ps)
        | Infer_err err -> Infer_err err))

(** val instantiate_enum_variant_field_tys :
    lifetime list -> ty list -> enum_variant_def -> ty list **)

let instantiate_enum_variant_field_tys lts args v =
  map
    (instantiate_enum_variant_field_ty lts
      (variant_lifetime_witnesses v.enum_variant_lifetimes) args)
    v.enum_variant_fields

(** val match_payload_params :
    ident list -> lifetime list -> ty list -> enum_variant_def -> param list
    infer_result **)

let match_payload_params binders lts args v =
  match_binder_params binders (instantiate_enum_variant_field_tys lts args v)

(** val ctx_add_params : param list -> ctx -> ctx **)

let ctx_add_params ps _UU0393_ =
  app (params_ctx ps) _UU0393_

(** val ctx_remove_params : param list -> ctx -> ctx **)

let rec ctx_remove_params ps _UU0393_ =
  match ps with
  | [] -> _UU0393_
  | p :: rest -> ctx_remove_params rest (ctx_remove_b p.param_name _UU0393_)

(** val ident_in_b : ident -> ident list -> bool **)

let rec ident_in_b x = function
| [] -> false
| y :: rest -> (||) (ident_eqb x y) (ident_in_b x rest)

(** val ident_nodup_b : ident list -> bool **)

let rec ident_nodup_b = function
| [] -> true
| x :: rest -> (&&) (negb (ident_in_b x rest)) (ident_nodup_b rest)

(** val params_names_nodup_b : param list -> bool **)

let params_names_nodup_b ps =
  ident_nodup_b (ctx_names (params_ctx ps))

(** val ctx_lookup_params_none_b : param list -> ctx -> bool **)

let rec ctx_lookup_params_none_b ps _UU0393_ =
  match ps with
  | [] -> true
  | p :: rest ->
    (match ctx_lookup_state p.param_name _UU0393_ with
     | Some _ -> false
     | None -> ctx_lookup_params_none_b rest _UU0393_)

(** val unrestricted_unit_params_of_binders : ident list -> param list **)

let rec unrestricted_unit_params_of_binders = function
| [] -> []
| x :: rest ->
  { param_mutability = MImmutable; param_name = x; param_ty = (MkTy
    (UUnrestricted, TUnits)) } :: (unrestricted_unit_params_of_binders rest)

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

(** val enum_outlives_hold_b :
    outlives_ctx -> enum_def -> lifetime list -> bool **)

let enum_outlives_hold_b _UU03a9_ edef lts =
  outlives_constraints_hold_b _UU03a9_
    (apply_lt_outlives lts edef.enum_outlives)

(** val infer_hrt_call_env :
    outlives_ctx -> Big_int_Z.big_int -> Big_int_Z.big_int -> outlives_ctx ->
    ty -> ty list -> ty infer_result **)

let infer_hrt_call_env _UU03a9_ n m bounds body arg_tys =
  match ty_core body with
  | TFn (param_tys, ret) ->
    (match build_bound_sigma (repeat None m) arg_tys param_tys with
     | Some _UU03c3_ ->
       (match check_arg_tys _UU03a9_ arg_tys
                (map (open_bound_ty _UU03c3_) param_tys) with
        | Some err -> Infer_err err
        | None ->
          if (||) (contains_lbound_ty (open_bound_ty _UU03c3_ ret))
               (contains_lbound_outlives
                 (open_bound_outlives _UU03c3_ bounds))
          then Infer_err ErrHrtUnresolvedBound
          else if outlives_constraints_hold_b _UU03a9_
                    (open_bound_outlives _UU03c3_ bounds)
               then Infer_ok (open_bound_ty _UU03c3_ ret)
               else Infer_err ErrHrtBoundUnsatisfied)
     | None -> Infer_err ErrLifetimeConflict)
  | TClosure (env_lt, param_tys, ret) ->
    (match build_bound_sigma (repeat None m) arg_tys param_tys with
     | Some _UU03c3_0 ->
       let _UU03c3_ = complete_bound_sigma_with_vars n _UU03c3_0 in
       (match check_arg_tys _UU03a9_ arg_tys
                (map (open_bound_ty _UU03c3_) param_tys) with
        | Some err -> Infer_err err
        | None ->
          let env_open = open_bound_lifetime _UU03c3_ env_lt in
          let ret_open = open_bound_ty _UU03c3_ ret in
          let bounds_open = open_bound_outlives _UU03c3_ bounds in
          if (||)
               ((||) (contains_lbound_lifetime env_open)
                 (contains_lbound_ty ret_open))
               (contains_lbound_outlives bounds_open)
          then Infer_err ErrHrtUnresolvedBound
          else if outlives_constraints_hold_b _UU03a9_ bounds_open
               then Infer_ok ret_open
               else Infer_err ErrHrtBoundUnsatisfied)
     | None -> Infer_err ErrLifetimeConflict)
  | x -> Infer_err (ErrMalformedHrtBody x)

(** val open_core_trait_bounds :
    lifetime option list -> ty core_trait_bound list -> ty core_trait_bound
    list **)

let open_core_trait_bounds _UU03c3_ bounds =
  map (map_core_trait_bound (open_bound_ty _UU03c3_)) bounds

(** val infer_mixed_forall_call_env :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    outlives_ctx -> Big_int_Z.big_int -> ty core_trait_bound list -> ty -> ty
    list -> ty infer_result **)

let infer_mixed_forall_call_env env _UU03a9_ n m lt_bounds type_params type_bounds body arg_tys =
  match ty_core body with
  | TFn (param_tys, ret) ->
    (match infer_type_forall_args type_params param_tys arg_tys with
     | Some type_args ->
       let param_tys_t = map (subst_type_params_ty type_args) param_tys in
       (match build_bound_sigma (repeat None m) arg_tys param_tys_t with
        | Some _UU03c3_0 ->
          let _UU03c3_ = complete_bound_sigma_with_vars n _UU03c3_0 in
          let param_tys_open = map (open_bound_ty _UU03c3_) param_tys_t in
          (match check_arg_tys _UU03a9_ arg_tys param_tys_open with
           | Some err -> Infer_err err
           | None ->
             let ret_open =
               open_bound_ty _UU03c3_ (subst_type_params_ty type_args ret)
             in
             let lt_bounds_open = open_bound_outlives _UU03c3_ lt_bounds in
             let type_bounds_open =
               open_core_trait_bounds _UU03c3_ type_bounds
             in
             if (||)
                  ((||) (contains_lbound_ty ret_open)
                    (contains_lbound_outlives lt_bounds_open))
                  (existsb (fun b ->
                    existsb (fun tr ->
                      existsb contains_lbound_ty tr.core_trait_ref_args)
                      b.core_bound_traits)
                    type_bounds_open)
             then Infer_err ErrHrtUnresolvedBound
             else if outlives_constraints_hold_b _UU03a9_ lt_bounds_open
                  then (match check_type_forall_bounds env type_bounds_open
                                type_args with
                        | Some err -> Infer_err err
                        | None -> Infer_ok ret_open)
                  else Infer_err ErrHrtBoundUnsatisfied)
        | None -> Infer_err ErrLifetimeConflict)
     | None -> Infer_err ErrTypeArgInferenceFailed)
  | x -> Infer_err (ErrMalformedHrtBody x)

(** val infer_mixed_forall_call_env_elab :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    outlives_ctx -> Big_int_Z.big_int -> ty core_trait_bound list -> ty -> ty
    list -> (ty list * ty) infer_result **)

let infer_mixed_forall_call_env_elab env _UU03a9_ n m lt_bounds type_params type_bounds body arg_tys =
  match ty_core body with
  | TFn (param_tys, ret) ->
    (match infer_type_forall_args type_params param_tys arg_tys with
     | Some type_args ->
       let param_tys_t = map (subst_type_params_ty type_args) param_tys in
       (match build_bound_sigma (repeat None m) arg_tys param_tys_t with
        | Some _UU03c3_0 ->
          let _UU03c3_ = complete_bound_sigma_with_vars n _UU03c3_0 in
          let param_tys_open = map (open_bound_ty _UU03c3_) param_tys_t in
          (match check_arg_tys _UU03a9_ arg_tys param_tys_open with
           | Some err -> Infer_err err
           | None ->
             let ret_open =
               open_bound_ty _UU03c3_ (subst_type_params_ty type_args ret)
             in
             let lt_bounds_open = open_bound_outlives _UU03c3_ lt_bounds in
             let type_bounds_open =
               open_core_trait_bounds _UU03c3_ type_bounds
             in
             if (||)
                  ((||) (contains_lbound_ty ret_open)
                    (contains_lbound_outlives lt_bounds_open))
                  (existsb (fun b ->
                    existsb (fun tr ->
                      existsb contains_lbound_ty tr.core_trait_ref_args)
                      b.core_bound_traits)
                    type_bounds_open)
             then Infer_err ErrHrtUnresolvedBound
             else if outlives_constraints_hold_b _UU03a9_ lt_bounds_open
                  then (match check_type_forall_bounds env type_bounds_open
                                type_args with
                        | Some err -> Infer_err err
                        | None -> Infer_ok (type_args, ret_open))
                  else Infer_err ErrHrtBoundUnsatisfied)
        | None -> Infer_err ErrLifetimeConflict)
     | None -> Infer_err ErrTypeArgInferenceFailed)
  | x -> Infer_err (ErrMalformedHrtBody x)

type sctx_entry = ctx_entry

type sctx = ctx

(** val sctx_of_ctx : ctx -> sctx **)

let sctx_of_ctx _UU0393_ =
  _UU0393_

(** val ctx_of_sctx : sctx -> ctx **)

let ctx_of_sctx _UU03a3_ =
  _UU03a3_

(** val mutability_eqb : mutability -> mutability -> bool **)

let mutability_eqb m1 m2 =
  match m1 with
  | MImmutable -> (match m2 with
                   | MImmutable -> true
                   | MMutable -> false)
  | MMutable -> (match m2 with
                 | MImmutable -> false
                 | MMutable -> true)

(** val field_path_eqb : field_path -> field_path -> bool **)

let rec field_path_eqb p q =
  match p with
  | [] -> (match q with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs ->
    (match q with
     | [] -> false
     | y :: ys -> (&&) ((=) x y) (field_path_eqb xs ys))

(** val field_paths_eqb : field_path list -> field_path list -> bool **)

let rec field_paths_eqb ps qs =
  match ps with
  | [] -> (match qs with
           | [] -> true
           | _ :: _ -> false)
  | p :: ps' ->
    (match qs with
     | [] -> false
     | q :: qs' -> (&&) (field_path_eqb p q) (field_paths_eqb ps' qs'))

(** val binding_state_eqb : binding_state -> binding_state -> bool **)

let binding_state_eqb st1 st2 =
  (&&) (eqb0 st1.st_consumed st2.st_consumed)
    (field_paths_eqb st1.st_moved_paths st2.st_moved_paths)

(** val sctx_entry_eqb : sctx_entry -> sctx_entry -> bool **)

let sctx_entry_eqb ce1 ce2 =
  let (p, m1) = ce1 in
  let (p0, st1) = p in
  let (x1, t1) = p0 in
  let (p1, m2) = ce2 in
  let (p2, st2) = p1 in
  let (x2, t2) = p2 in
  (&&)
    ((&&) ((&&) (ident_eqb x1 x2) (ty_eqb t1 t2)) (binding_state_eqb st1 st2))
    (mutability_eqb m1 m2)

(** val sctx_eqb : sctx -> sctx -> bool **)

let rec sctx_eqb _UU03a3_1 _UU03a3_2 =
  match _UU03a3_1 with
  | [] -> (match _UU03a3_2 with
           | [] -> true
           | _ :: _ -> false)
  | ce1 :: rest1 ->
    (match _UU03a3_2 with
     | [] -> false
     | ce2 :: rest2 -> (&&) (sctx_entry_eqb ce1 ce2) (sctx_eqb rest1 rest2))

(** val sctx_lookup : ident -> sctx -> (ty * binding_state) option **)

let sctx_lookup =
  ctx_lookup_state

(** val sctx_lookup_mut : ident -> sctx -> mutability option **)

let sctx_lookup_mut =
  ctx_lookup_mut

(** val check_make_closure_captures_sctx_base :
    global_env -> outlives_ctx -> sctx -> ident list -> param list -> ty list
    infer_result **)

let rec check_make_closure_captures_sctx_base env _UU03a9_ _UU03a3_ captures params =
  match captures with
  | [] ->
    (match params with
     | [] -> Infer_ok []
     | _ :: _ -> Infer_err ErrArityMismatch)
  | x :: captures' ->
    (match params with
     | [] -> Infer_err ErrArityMismatch
     | cap :: params' ->
       (match sctx_lookup x _UU03a3_ with
        | Some p ->
          let (t, st) = p in
          if negb (binding_available_b st [])
          then Infer_err (ErrAlreadyConsumed x)
          else (match sctx_lookup_mut x _UU03a3_ with
                | Some m ->
                  (match m with
                   | MImmutable ->
                     if usage_eqb (ty_usage t) UUnrestricted
                     then if ty_compatible_b _UU03a9_ t cap.param_ty
                          then (match check_make_closure_captures_sctx_base
                                        env _UU03a9_ _UU03a3_ captures'
                                        params' with
                                | Infer_ok captured_tys ->
                                  Infer_ok (t :: captured_tys)
                                | Infer_err err -> Infer_err err)
                          else Infer_err (compatible_error t cap.param_ty)
                     else Infer_err (ErrUsageMismatch ((ty_usage t),
                            UUnrestricted))
                   | MMutable -> Infer_err (ErrNotMutable x))
                | None -> Infer_err (ErrUnknownVar x))
        | None -> Infer_err (ErrUnknownVar x)))

(** val check_make_closure_captures_sctx_with_env :
    global_env -> outlives_ctx -> sctx -> ident list -> param list ->
    (lifetime * ty list) infer_result **)

let check_make_closure_captures_sctx_with_env env _UU03a9_ _UU03a3_ captures params =
  match check_make_closure_captures_sctx_base env _UU03a9_ _UU03a3_ captures
          params with
  | Infer_ok captured_tys ->
    (match infer_closure_env_lifetime _UU03a9_ captured_tys with
     | Infer_ok env_lt ->
       if closure_captures_allowed_b env _UU03a9_ env_lt captured_tys
       then Infer_ok (env_lt, captured_tys)
       else Infer_err (ErrNotAReference TUnits)
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val check_make_closure_captures_exact_sctx_with_env_base :
    global_env -> outlives_ctx -> sctx -> ident list -> param list -> ty list
    infer_result **)

let rec check_make_closure_captures_exact_sctx_with_env_base env _UU03a9_ _UU03a3_ captures params =
  match captures with
  | [] ->
    (match params with
     | [] -> Infer_ok []
     | _ :: _ -> Infer_err ErrArityMismatch)
  | x :: captures' ->
    (match params with
     | [] -> Infer_err ErrArityMismatch
     | cap :: params' ->
       (match cap.param_mutability with
        | MImmutable ->
          (match sctx_lookup cap.param_name _UU03a3_ with
           | Some _ -> Infer_err ErrContextCheckFailed
           | None ->
             (match sctx_lookup x _UU03a3_ with
              | Some p ->
                let (t, st) = p in
                if st.st_consumed
                then Infer_err ErrContextCheckFailed
                else (match st.st_moved_paths with
                      | [] ->
                        (match sctx_lookup_mut x _UU03a3_ with
                         | Some m ->
                           (match m with
                            | MImmutable ->
                              if usage_eqb (ty_usage t) UUnrestricted
                              then if (&&) (ty_eqb t cap.param_ty)
                                        (ty_compatible_b _UU03a9_ t
                                          cap.param_ty)
                                   then (match check_make_closure_captures_exact_sctx_with_env_base
                                                 env _UU03a9_ _UU03a3_
                                                 captures' params' with
                                         | Infer_ok rest_tys ->
                                           Infer_ok (t :: rest_tys)
                                         | Infer_err err -> Infer_err err)
                                   else Infer_err
                                          (compatible_error t cap.param_ty)
                              else Infer_err (ErrUsageMismatch ((ty_usage t),
                                     UUnrestricted))
                            | MMutable -> Infer_err (ErrNotMutable x))
                         | None -> Infer_err (ErrUnknownVar x))
                      | _ :: _ -> Infer_err ErrContextCheckFailed)
              | None -> Infer_err (ErrUnknownVar x)))
        | MMutable -> Infer_err ErrContextCheckFailed))

(** val check_make_closure_captures_exact_sctx_with_env :
    global_env -> outlives_ctx -> sctx -> ident list -> param list ->
    (lifetime * ty list) infer_result **)

let check_make_closure_captures_exact_sctx_with_env env _UU03a9_ _UU03a3_ captures params =
  match check_make_closure_captures_exact_sctx_with_env_base env _UU03a9_
          _UU03a3_ captures params with
  | Infer_ok captured_tys ->
    (match infer_closure_env_lifetime _UU03a9_ captured_tys with
     | Infer_ok env_lt ->
       if closure_captures_allowed_b env _UU03a9_ env_lt captured_tys
       then Infer_ok (env_lt, captured_tys)
       else Infer_err (ErrNotAReference TUnits)
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

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

(** val sctx_add_params : param list -> sctx -> sctx **)

let sctx_add_params =
  ctx_add_params

(** val sctx_remove_params : param list -> sctx -> sctx **)

let sctx_remove_params =
  ctx_remove_params

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

(** val place_resolved_write_writable_chain_b :
    global_env -> root_env -> sctx -> place -> bool **)

let rec place_resolved_write_writable_chain_b env r _UU03a3_ p =
  if place_resolved_write_direct_parent_b p
  then true
  else (match p with
        | PDeref q ->
          (&&)
            ((&&) (place_resolved_write_writable_chain_b env r _UU03a3_ q)
              (writable_place_b env _UU03a3_ q))
            (match place_resolved_write_target r q with
             | Some x ->
               (match sctx_lookup_mut x _UU03a3_ with
                | Some m ->
                  (match m with
                   | MImmutable -> false
                   | MMutable -> true)
                | None -> false)
             | None -> false)
        | _ -> false)

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

(** val auto_drop_paths_for_ty_fuel :
    Big_int_Z.big_int -> global_env -> ty -> field_path -> field_path list **)

let rec auto_drop_paths_for_ty_fuel fuel env t prefix =
  match ty_usage t with
  | UAffine ->
    (match ty_core t with
     | TStruct (sname, lts, args) ->
       ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
          (fun _ -> prefix :: [])
          (fun fuel' ->
          match lookup_struct sname env with
          | Some s ->
            let rec go = function
            | [] -> []
            | f :: rest ->
              app
                (auto_drop_paths_for_ty_fuel fuel' env
                  (instantiate_struct_field_ty lts args f)
                  (app prefix (f.field_name :: [])))
                (go rest)
            in go s.struct_fields
          | None -> prefix :: [])
          fuel)
     | _ -> prefix :: [])
  | _ -> []

(** val auto_drop_paths_for_ty : global_env -> ty -> field_path list **)

let auto_drop_paths_for_ty env t =
  auto_drop_paths_for_ty_fuel (Big_int_Z.succ_big_int
    (add (length env.env_structs) (ty_depth t))) env t []

(** val filter_live_drop_paths :
    binding_state -> field_path list -> field_path list **)

let rec filter_live_drop_paths st = function
| [] -> []
| p :: rest ->
  if binding_available_b st p
  then p :: (filter_live_drop_paths st rest)
  else filter_live_drop_paths st rest

(** val auto_drop_live_paths :
    global_env -> ident -> ty -> sctx -> field_path list **)

let auto_drop_live_paths env x t _UU03a3_ =
  match sctx_lookup x _UU03a3_ with
  | Some p ->
    let (_, st) = p in
    filter_live_drop_paths st (auto_drop_paths_for_ty env t)
  | None -> []

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
       | Some fdef ->
         if no_captures_b fdef
         then Infer_ok ((fn_value_ty fdef), _UU03a3_)
         else Infer_err ErrNotImplemented
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EMakeClosure (fname, captures) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         (match check_make_closure_captures_sctx_with_env env _UU03a9_
                  _UU03a3_ captures fdef.fn_captures with
          | Infer_ok p ->
            let (env_lt, captured_tys) = p in
            Infer_ok ((closure_value_ty_at env_lt fdef captured_tys),
            _UU03a3_)
          | Infer_err err -> Infer_err err)
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
         if (&&) (no_captures_b fdef)
              (Nat.eqb fdef.fn_type_params Big_int_Z.zero_big_int)
         then let m = fdef.fn_lifetimes in
              let collect =
                let rec collect _UU03a3_0 = function
                | [] -> Infer_ok ([], _UU03a3_0)
                | e' :: es ->
                  (match infer_core_env_state_fuel fuel' env _UU03a9_ n
                           _UU03a3_0 e' with
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
                            if outlives_constraints_hold_b _UU03a9_
                                 _UU03a9__subst
                            then Infer_ok
                                   ((apply_lt_ty _UU03c3_ fdef.fn_ret),
                                   _UU03a3_')
                            else Infer_err ErrHrtBoundUnsatisfied
                       else Infer_err ErrLifetimeLeak)
                  | None -> Infer_err ErrLifetimeConflict)
               | Infer_err err -> Infer_err err)
         else Infer_err ErrNotImplemented
       | None -> Infer_err (ErrFunctionNotFound fname))
    | ECallGeneric (fname, type_args, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if (&&) (no_captures_b fdef)
              (Nat.eqb (length type_args) fdef.fn_type_params)
         then (match check_struct_bounds env fdef.fn_bounds type_args with
               | Some err -> Infer_err err
               | None ->
                 let m = fdef.fn_lifetimes in
                 let params_typed = apply_type_params type_args fdef.fn_params
                 in
                 let collect =
                   let rec collect _UU03a3_0 = function
                   | [] -> Infer_ok ([], _UU03a3_0)
                   | e' :: es ->
                     (match infer_core_env_state_fuel fuel' env _UU03a9_ n
                              _UU03a3_0 e' with
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
                    (match build_sigma m (repeat None m) arg_tys params_typed with
                     | Some _UU03c3__acc ->
                       let _UU03c3_ = finalize_subst _UU03c3__acc in
                       let ps_subst = apply_lt_params _UU03c3_ params_typed in
                       (match check_args _UU03a9_ arg_tys ps_subst with
                        | Some err -> Infer_err err
                        | None ->
                          if forallb (wf_lifetime_b (mk_region_ctx n))
                               _UU03c3_
                          then let _UU03a9__subst =
                                 apply_lt_outlives _UU03c3_ fdef.fn_outlives
                               in
                               if outlives_constraints_hold_b _UU03a9_
                                    _UU03a9__subst
                               then Infer_ok
                                      ((apply_lt_ty _UU03c3_
                                         (subst_type_params_ty type_args
                                           fdef.fn_ret)),
                                      _UU03a3_')
                               else Infer_err ErrHrtBoundUnsatisfied
                          else Infer_err ErrLifetimeLeak)
                     | None -> Infer_err ErrLifetimeConflict)
                  | Infer_err err -> Infer_err err))
         else Infer_err ErrArityMismatch
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
             | TClosure (_, param_tys, ret) ->
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
                | TClosure (env_lt, param_tys, ret) ->
                  (match build_bound_sigma (repeat None m) arg_tys param_tys with
                   | Some _UU03c3_0 ->
                     let _UU03c3_ = complete_bound_sigma_with_vars n _UU03c3_0
                     in
                     let param_tys_open =
                       map (open_bound_ty _UU03c3_) param_tys
                     in
                     (match check_arg_tys _UU03a9_ arg_tys param_tys_open with
                      | Some err -> Infer_err err
                      | None ->
                        let env_open = open_bound_lifetime _UU03c3_ env_lt in
                        let ret_open = open_bound_ty _UU03c3_ ret in
                        let bounds_open = open_bound_outlives _UU03c3_ bounds
                        in
                        if (||)
                             ((||) (contains_lbound_lifetime env_open)
                               (contains_lbound_ty ret_open))
                             (contains_lbound_outlives bounds_open)
                        then Infer_err ErrHrtUnresolvedBound
                        else if outlives_constraints_hold_b _UU03a9_
                                  bounds_open
                             then Infer_ok (ret_open, _UU03a3_')
                             else Infer_err ErrHrtBoundUnsatisfied)
                   | None -> Infer_err ErrLifetimeConflict)
                | TTypeForall (type_params, type_bounds, type_body) ->
                  (match infer_mixed_forall_call_env env _UU03a9_ n m bounds
                           type_params type_bounds type_body arg_tys with
                   | Infer_ok ret -> Infer_ok (ret, _UU03a3_')
                   | Infer_err err -> Infer_err err)
                | x -> Infer_err (ErrMalformedHrtBody x))
             | TTypeForall (type_params, bounds, body) ->
               (match infer_type_forall_call_env env _UU03a9_ type_params
                        bounds body arg_tys with
                | Infer_ok ret -> Infer_ok (ret, _UU03a3_')
                | Infer_err err -> Infer_err err)
             | x -> Infer_err (ErrNotAFunction x))
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | ECallExprGeneric (_, _, _) -> Infer_err ErrNotImplemented
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
    | EEnum (enum_name0, variant_name, lts, variant_lts, args, payloads) ->
      (match lookup_enum enum_name0 env with
       | Some edef ->
         if negb (Nat.eqb (length lts) edef.enum_lifetimes)
         then Infer_err ErrArityMismatch
         else if negb (Nat.eqb (length args) edef.enum_type_params)
              then Infer_err ErrArityMismatch
              else (match check_struct_bounds env edef.enum_bounds args with
                    | Some err -> Infer_err err
                    | None ->
                      if negb (enum_outlives_hold_b _UU03a9_ edef lts)
                      then Infer_err ErrLifetimeConflict
                      else (match lookup_enum_variant variant_name
                                    edef.enum_variants with
                            | Some vdef ->
                              if negb
                                   (Nat.eqb (length variant_lts)
                                     vdef.enum_variant_lifetimes)
                              then Infer_err ErrArityMismatch
                              else let go =
                                     let rec go _UU03a3_0 fields es =
                                       match fields with
                                       | [] ->
                                         (match es with
                                          | [] -> Infer_ok _UU03a3_0
                                          | _ :: _ ->
                                            Infer_err ErrArityMismatch)
                                       | t_field :: fields' ->
                                         (match es with
                                          | [] -> Infer_err ErrArityMismatch
                                          | e_payload :: es' ->
                                            (match infer_core_env_state_fuel
                                                     fuel' env _UU03a9_ n
                                                     _UU03a3_0 e_payload with
                                             | Infer_ok p ->
                                               let (t_payload, _UU03a3_1) = p
                                               in
                                               let t_expected =
                                                 instantiate_enum_variant_field_ty
                                                   lts variant_lts args
                                                   t_field
                                               in
                                               if ty_compatible_b _UU03a9_
                                                    t_payload t_expected
                                               then go _UU03a3_1 fields' es'
                                               else Infer_err
                                                      (compatible_error
                                                        t_payload t_expected)
                                             | Infer_err err -> Infer_err err))
                                     in go
                                   in
                                   (match go _UU03a3_
                                            vdef.enum_variant_fields payloads with
                                    | Infer_ok _UU03a3_' ->
                                      Infer_ok
                                        ((instantiate_enum_ty edef lts args),
                                        _UU03a3_')
                                    | Infer_err err -> Infer_err err)
                            | None ->
                              Infer_err (ErrVariantNotFound variant_name)))
       | None -> Infer_err (ErrEnumNotFound enum_name0))
    | EMatch (scrut, branches) ->
      (match infer_core_env_state_fuel fuel' env _UU03a9_ n _UU03a3_ scrut with
       | Infer_ok p ->
         let (t_scrut, _UU03a3_1) = p in
         (match ty_core t_scrut with
          | TEnum (enum_name0, lts, args) ->
            (match lookup_enum enum_name0 env with
             | Some edef ->
               if negb (Nat.eqb (length lts) edef.enum_lifetimes)
               then Infer_err ErrArityMismatch
               else if negb (Nat.eqb (length args) edef.enum_type_params)
                    then Infer_err ErrArityMismatch
                    else (match check_struct_bounds env edef.enum_bounds args with
                          | Some err -> Infer_err err
                          | None ->
                            if negb (enum_outlives_hold_b _UU03a9_ edef lts)
                            then Infer_err ErrLifetimeConflict
                            else (match first_duplicate_branch branches with
                                  | Some name ->
                                    Infer_err (ErrDuplicateVariant name)
                                  | None ->
                                    (match first_unknown_variant_branch
                                             branches edef.enum_variants with
                                     | Some name ->
                                       Infer_err (ErrVariantNotFound name)
                                     | None ->
                                       (match first_unsupported_match_payload
                                                branches edef.enum_variants with
                                        | Some name ->
                                          Infer_err
                                            (ErrMatchPayloadUnsupported name)
                                        | None ->
                                          (match first_missing_variant_branch
                                                   edef.enum_variants branches with
                                           | Some name ->
                                             Infer_err (ErrMissingVariant
                                               name)
                                           | None ->
                                             let infer_first = fun defs ->
                                               match defs with
                                               | [] ->
                                                 Infer_err (ErrMissingVariant
                                                   "")
                                               | v :: rest ->
                                                 let infer_branch = fun v0 ->
                                                   match lookup_expr_branch_binders
                                                           v0.enum_variant_name
                                                           branches with
                                                   | Some binders ->
                                                     (match lookup_branch_b
                                                              v0.enum_variant_name
                                                              branches with
                                                      | Some e_branch ->
                                                        (match match_payload_params
                                                                 binders lts
                                                                 args v0 with
                                                         | Infer_ok ps ->
                                                           if (&&)
                                                                (params_names_nodup_b
                                                                  ps)
                                                                (ctx_lookup_params_none_b
                                                                  ps
                                                                  _UU03a3_1)
                                                           then (match 
                                                                 infer_core_env_state_fuel
                                                                   fuel' env
                                                                   _UU03a9_ n
                                                                   (sctx_add_params
                                                                    ps
                                                                    _UU03a3_1)
                                                                   e_branch with
                                                                 | Infer_ok p0 ->
                                                                   let (
                                                                    t_branch,
                                                                    _UU03a3__branch_payload) =
                                                                    p0
                                                                   in
                                                                   if 
                                                                    contains_lbound_ty
                                                                    t_branch
                                                                   then 
                                                                    Infer_err
                                                                    ErrLifetimeLeak
                                                                   else 
                                                                    if 
                                                                    params_ok_sctx_b
                                                                    env ps
                                                                    _UU03a3__branch_payload
                                                                    then 
                                                                    Infer_ok
                                                                    (t_branch,
                                                                    (sctx_remove_params
                                                                    ps
                                                                    _UU03a3__branch_payload))
                                                                    else 
                                                                    Infer_err
                                                                    ErrContextCheckFailed
                                                                 | Infer_err err ->
                                                                   Infer_err
                                                                    err)
                                                           else Infer_err
                                                                  ErrContextCheckFailed
                                                         | Infer_err err ->
                                                           Infer_err err)
                                                      | None ->
                                                        Infer_err
                                                          (ErrMissingVariant
                                                          v0.enum_variant_name))
                                                   | None ->
                                                     Infer_err
                                                       (ErrMissingVariant
                                                       v0.enum_variant_name)
                                                 in
                                                 (match infer_branch v with
                                                  | Infer_ok p0 ->
                                                    let (t_branch,
                                                         _UU03a3__branch) =
                                                      p0
                                                    in
                                                    let infer_rest =
                                                      let rec infer_rest t_head = function
                                                      | [] ->
                                                        Infer_ok ([], [])
                                                      | v0 :: rest0 ->
                                                        (match infer_branch v0 with
                                                         | Infer_ok p1 ->
                                                           let (t0, _UU03a3_0) =
                                                             p1
                                                           in
                                                           if ty_core_eqb
                                                                (ty_core t0)
                                                                (ty_core
                                                                  t_head)
                                                           then let rest_result =
                                                                  infer_rest
                                                                    t_head
                                                                    rest0
                                                                in
                                                                (match rest_result with
                                                                 | Infer_ok p2 ->
                                                                   let (
                                                                    _UU03a3_s,
                                                                    ts) = p2
                                                                   in
                                                                   Infer_ok
                                                                   ((_UU03a3_0 :: _UU03a3_s),
                                                                   (t0 :: ts))
                                                                 | Infer_err err ->
                                                                   Infer_err
                                                                    err)
                                                           else Infer_err
                                                                  (ErrTypeMismatch
                                                                  ((ty_core
                                                                    t0),
                                                                  (ty_core
                                                                    t_head)))
                                                         | Infer_err err ->
                                                           Infer_err err)
                                                      in infer_rest
                                                    in
                                                    (match infer_rest
                                                             t_branch rest with
                                                     | Infer_ok p1 ->
                                                       let (_UU03a3_s, ts) =
                                                         p1
                                                       in
                                                       Infer_ok ((t_branch,
                                                       (_UU03a3__branch :: _UU03a3_s)),
                                                       ts)
                                                     | Infer_err err ->
                                                       Infer_err err)
                                                  | Infer_err err ->
                                                    Infer_err err)
                                             in
                                             (match infer_first
                                                      edef.enum_variants with
                                              | Infer_ok p0 ->
                                                let (p1, ts_tail) = p0 in
                                                let (t_head, l) = p1 in
                                                (match l with
                                                 | [] ->
                                                   Infer_err
                                                     ErrContextCheckFailed
                                                 | _UU03a3__head :: _UU03a3__tail ->
                                                   (match ctx_merge_many
                                                            (ctx_of_sctx
                                                              _UU03a3__head)
                                                            (map ctx_of_sctx
                                                              _UU03a3__tail) with
                                                    | Some _UU0393__out ->
                                                      Infer_ok ((MkTy
                                                        ((usage_max_tys_nonempty
                                                           t_head ts_tail),
                                                        (ty_core t_head))),
                                                        (sctx_of_ctx
                                                          _UU0393__out))
                                                    | None ->
                                                      Infer_err
                                                        ErrContextCheckFailed))
                                              | Infer_err err -> Infer_err err))))))
             | None -> Infer_err (ErrEnumNotFound enum_name0))
          | x -> Infer_err (ErrNotAnEnum x))
       | Infer_err err -> Infer_err err)
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

(** val param_name_in_b : ident -> param list -> bool **)

let rec param_name_in_b x = function
| [] -> false
| p :: ps' -> (||) (ident_eqb x p.param_name) (param_name_in_b x ps')

(** val param_vars_exact_b : param list -> expr list -> bool **)

let rec param_vars_exact_b ps args =
  match ps with
  | [] -> (match args with
           | [] -> true
           | _ :: _ -> false)
  | p :: ps' ->
    (match args with
     | [] -> false
     | e :: args' ->
       (match e with
        | EVar x ->
          (&&) (ident_eqb x p.param_name) (param_vars_exact_b ps' args')
        | _ -> false))

(** val lookup_call_arg_for_param :
    ident -> param list -> expr list -> expr option **)

let rec lookup_call_arg_for_param x ps args =
  match ps with
  | [] -> None
  | p :: ps' ->
    (match args with
     | [] -> None
     | arg :: args' ->
       if ident_eqb x p.param_name
       then Some arg
       else lookup_call_arg_for_param x ps' args')

(** val adapter_call_uses_bound_fn_only :
    ident -> ident -> param list -> expr list -> bool **)

let rec adapter_call_uses_bound_fn_only x fparam ps args =
  match ps with
  | [] -> (match args with
           | [] -> true
           | _ :: _ -> false)
  | p :: ps' ->
    (match args with
     | [] -> false
     | arg :: args' ->
       if ident_eqb p.param_name fparam
       then (match arg with
             | EVar y ->
               (&&) (ident_eqb x y)
                 (adapter_call_uses_bound_fn_only x fparam ps' args')
             | _ -> false)
       else (&&)
              ((&&) (negb (ident_in_b x (free_vars_expr arg)))
                (negb (ident_in_b x (args_local_store_names (arg :: [])))))
              (adapter_call_uses_bound_fn_only x fparam ps' args'))

(** val adapter_body_actual_args :
    ident -> param list -> expr list -> expr list -> expr list option **)

let rec adapter_body_actual_args fparam ps call_args = function
| [] -> Some []
| e :: rest ->
  (match e with
   | EVar y ->
     if ident_eqb y fparam
     then None
     else (match lookup_call_arg_for_param y ps call_args with
           | Some actual ->
             (match adapter_body_actual_args fparam ps call_args rest with
              | Some actuals -> Some (actual :: actuals)
              | None -> None)
           | None -> None)
   | _ -> None)

(** val generic_fn_wrapper_target : fn_def -> (ident * ty list) option **)

let generic_fn_wrapper_target fdef =
  if (&&)
       ((&&) (no_captures_b fdef)
         (Nat.eqb fdef.fn_lifetimes Big_int_Z.zero_big_int))
       (Nat.eqb fdef.fn_type_params Big_int_Z.zero_big_int)
  then (match fdef.fn_body with
        | ECallGeneric (target, type_args, args) ->
          if param_vars_exact_b fdef.fn_params args
          then Some (target, type_args)
          else None
        | _ -> None)
  else None

(** val adapter_call_target : fn_def -> (ident * expr list) option **)

let adapter_call_target fdef =
  if params_names_nodup_b fdef.fn_params
  then (match fdef.fn_body with
        | ECallExpr (e, body_args) ->
          (match e with
           | EVar fparam ->
             if param_name_in_b fparam fdef.fn_params
             then Some (fparam, body_args)
             else None
           | _ -> None)
        | _ -> None)
  else None

(** val direct_generic_call_for_let_wrapper_adapter :
    global_env -> ident -> ident -> ident -> expr list -> expr option **)

let direct_generic_call_for_let_wrapper_adapter env x wrapper_name adapter_name call_args =
  match lookup_fn_b wrapper_name env.env_fns with
  | Some wrapper ->
    (match lookup_fn_b adapter_name env.env_fns with
     | Some adapter ->
       (match generic_fn_wrapper_target wrapper with
        | Some p ->
          let (target, type_args) = p in
          (match adapter_call_target adapter with
           | Some p0 ->
             let (fparam, adapter_body_args) = p0 in
             if adapter_call_uses_bound_fn_only x fparam adapter.fn_params
                  call_args
             then (match adapter_body_actual_args fparam adapter.fn_params
                           call_args adapter_body_args with
                   | Some actual_args ->
                     Some (ECallGeneric (target, type_args, actual_args))
                   | None -> None)
             else None
           | None -> None)
        | None -> None)
     | None -> None)
  | None -> None

(** val infer_core_env_state_fuel_elab :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    sctx -> expr -> ((ty * sctx) * expr) infer_result **)

let rec infer_core_env_state_fuel_elab fuel env _UU03a9_ n _UU03a3_ e =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> Infer_err ErrNotImplemented)
    (fun fuel' ->
    match e with
    | EUnit -> Infer_ok (((MkTy (UUnrestricted, TUnits)), _UU03a3_), e)
    | ELit l ->
      (match l with
       | LInt _ -> Infer_ok (((MkTy (UUnrestricted, TIntegers)), _UU03a3_), e)
       | LFloat _ -> Infer_ok (((MkTy (UUnrestricted, TFloats)), _UU03a3_), e)
       | LBool _ ->
         Infer_ok (((MkTy (UUnrestricted, TBooleans)), _UU03a3_), e))
    | EVar x ->
      (match infer_place_sctx env _UU03a3_ (PVar x) with
       | Infer_ok t ->
         (match consume_place_value env _UU03a3_ (PVar x) t with
          | Infer_ok _UU03a3_' -> Infer_ok ((t, _UU03a3_'), e)
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | ELet (m, x, t, e1, e2) ->
      (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n _UU03a3_ e1 with
       | Infer_ok p ->
         let (p0, e1') = p in
         let (t1, _UU03a3_1) = p0 in
         if ty_compatible_b _UU03a9_ t1 t
         then (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n
                       (sctx_add x t m _UU03a3_1) e2 with
               | Infer_ok p1 ->
                 let (p2, e2') = p1 in
                 let (t2, _UU03a3_2) = p2 in
                 if sctx_check_ok env x t _UU03a3_2
                 then (match e1' with
                       | EFn wrapper_name ->
                         (match e2' with
                          | ECall (adapter_name, call_args) ->
                            if usage_eqb (ty_usage t) UUnrestricted
                            then (match direct_generic_call_for_let_wrapper_adapter
                                          env x wrapper_name adapter_name
                                          call_args with
                                  | Some direct_call ->
                                    (match infer_core_env_state_fuel_elab
                                             fuel' env _UU03a9_ n _UU03a3_
                                             direct_call with
                                     | Infer_ok direct -> Infer_ok direct
                                     | Infer_err _ ->
                                       Infer_ok ((t2,
                                         (sctx_remove x _UU03a3_2)), (ELet
                                         (m, x, t, e1', e2'))))
                                  | None ->
                                    Infer_ok ((t2,
                                      (sctx_remove x _UU03a3_2)), (ELet (m,
                                      x, t, e1', e2'))))
                            else Infer_ok ((t2, (sctx_remove x _UU03a3_2)),
                                   (ELet (m, x, t, e1', e2')))
                          | ECallExprGeneric (e0, type_args, args') ->
                            (match e0 with
                             | EVar y ->
                               if (&&)
                                    ((&&) (ident_eqb x y)
                                      (negb
                                        (existsb (fun arg ->
                                          ident_in_b x (free_vars_expr arg))
                                          args')))
                                    (negb
                                      (ident_in_b x
                                        (args_local_store_names args')))
                               then (match infer_core_env_state_fuel_elab
                                             fuel' env _UU03a9_ n _UU03a3_
                                             (ECallGeneric (wrapper_name,
                                             type_args, args')) with
                                     | Infer_ok direct -> Infer_ok direct
                                     | Infer_err _ ->
                                       Infer_ok ((t2,
                                         (sctx_remove x _UU03a3_2)), (ELet
                                         (m, x, t, e1', e2'))))
                               else Infer_ok ((t2,
                                      (sctx_remove x _UU03a3_2)), (ELet (m,
                                      x, t, e1', e2')))
                             | _ ->
                               Infer_ok ((t2, (sctx_remove x _UU03a3_2)),
                                 (ELet (m, x, t, e1', e2'))))
                          | _ ->
                            Infer_ok ((t2, (sctx_remove x _UU03a3_2)), (ELet
                              (m, x, t, e1', e2'))))
                       | _ ->
                         Infer_ok ((t2, (sctx_remove x _UU03a3_2)), (ELet (m,
                           x, t, e1', e2'))))
                 else Infer_err ErrContextCheckFailed
               | Infer_err err -> Infer_err err)
         else Infer_err (compatible_error t1 t)
       | Infer_err err -> Infer_err err)
    | ELetInfer (m, x, e1, e2) ->
      (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n _UU03a3_ e1 with
       | Infer_ok p ->
         let (p0, e1') = p in
         let (t1, _UU03a3_1) = p0 in
         (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n
                  (sctx_add x t1 m _UU03a3_1) e2 with
          | Infer_ok p1 ->
            let (p2, e2') = p1 in
            let (t2, _UU03a3_2) = p2 in
            if sctx_check_ok env x t1 _UU03a3_2
            then Infer_ok ((t2, (sctx_remove x _UU03a3_2)), (ELet (m, x, t1,
                   e1', e2')))
            else Infer_err ErrContextCheckFailed
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | EFn fname ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if no_captures_b fdef
         then Infer_ok (((fn_value_ty fdef), _UU03a3_), e)
         else Infer_err ErrNotImplemented
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EMakeClosure (fname, captures) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         (match check_make_closure_captures_sctx_with_env env _UU03a9_
                  _UU03a3_ captures fdef.fn_captures with
          | Infer_ok p ->
            let (env_lt, captured_tys) = p in
            Infer_ok (((closure_value_ty_at env_lt fdef captured_tys),
            _UU03a3_), (EMakeClosure (fname, captures)))
          | Infer_err err -> Infer_err err)
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EPlace p ->
      (match infer_place_sctx env _UU03a3_ p with
       | Infer_ok t ->
         (match consume_place_value env _UU03a3_ p t with
          | Infer_ok _UU03a3_' -> Infer_ok ((t, _UU03a3_'), e)
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | ECall (fname, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if (&&) (no_captures_b fdef)
              (Nat.eqb fdef.fn_type_params Big_int_Z.zero_big_int)
         then let m = fdef.fn_lifetimes in
              let collect =
                let rec collect _UU03a3_0 = function
                | [] -> Infer_ok (([], _UU03a3_0), [])
                | e' :: es ->
                  (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n
                           _UU03a3_0 e' with
                   | Infer_ok p ->
                     let (p0, e_elab) = p in
                     let (t_e, _UU03a3_1) = p0 in
                     (match collect _UU03a3_1 es with
                      | Infer_ok p1 ->
                        let (p2, es_elab) = p1 in
                        let (tys, _UU03a3_2) = p2 in
                        Infer_ok (((t_e :: tys), _UU03a3_2),
                        (e_elab :: es_elab))
                      | Infer_err err -> Infer_err err)
                   | Infer_err err -> Infer_err err)
                in collect
              in
              (match collect _UU03a3_ args with
               | Infer_ok p ->
                 let (p0, args') = p in
                 let (arg_tys, _UU03a3_') = p0 in
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
                            if outlives_constraints_hold_b _UU03a9_
                                 _UU03a9__subst
                            then Infer_ok
                                   (((apply_lt_ty _UU03c3_ fdef.fn_ret),
                                   _UU03a3_'), (ECall (fname, args')))
                            else Infer_err ErrHrtBoundUnsatisfied
                       else Infer_err ErrLifetimeLeak)
                  | None -> Infer_err ErrLifetimeConflict)
               | Infer_err err -> Infer_err err)
         else Infer_err ErrNotImplemented
       | None -> Infer_err (ErrFunctionNotFound fname))
    | ECallGeneric (fname, type_args, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if (&&) (no_captures_b fdef)
              (Nat.eqb (length type_args) fdef.fn_type_params)
         then (match check_struct_bounds env fdef.fn_bounds type_args with
               | Some err -> Infer_err err
               | None ->
                 let m = fdef.fn_lifetimes in
                 let params_typed = apply_type_params type_args fdef.fn_params
                 in
                 let collect =
                   let rec collect _UU03a3_0 = function
                   | [] -> Infer_ok (([], _UU03a3_0), [])
                   | e' :: es ->
                     (match infer_core_env_state_fuel_elab fuel' env _UU03a9_
                              n _UU03a3_0 e' with
                      | Infer_ok p ->
                        let (p0, e_elab) = p in
                        let (t_e, _UU03a3_1) = p0 in
                        (match collect _UU03a3_1 es with
                         | Infer_ok p1 ->
                           let (p2, es_elab) = p1 in
                           let (tys, _UU03a3_2) = p2 in
                           Infer_ok (((t_e :: tys), _UU03a3_2),
                           (e_elab :: es_elab))
                         | Infer_err err -> Infer_err err)
                      | Infer_err err -> Infer_err err)
                   in collect
                 in
                 (match collect _UU03a3_ args with
                  | Infer_ok p ->
                    let (p0, args') = p in
                    let (arg_tys, _UU03a3_') = p0 in
                    (match build_sigma m (repeat None m) arg_tys params_typed with
                     | Some _UU03c3__acc ->
                       let _UU03c3_ = finalize_subst _UU03c3__acc in
                       let ps_subst = apply_lt_params _UU03c3_ params_typed in
                       (match check_args _UU03a9_ arg_tys ps_subst with
                        | Some err -> Infer_err err
                        | None ->
                          if forallb (wf_lifetime_b (mk_region_ctx n))
                               _UU03c3_
                          then let _UU03a9__subst =
                                 apply_lt_outlives _UU03c3_ fdef.fn_outlives
                               in
                               if outlives_constraints_hold_b _UU03a9_
                                    _UU03a9__subst
                               then Infer_ok
                                      (((apply_lt_ty _UU03c3_
                                          (subst_type_params_ty type_args
                                            fdef.fn_ret)),
                                      _UU03a3_'), (ECallGeneric (fname,
                                      type_args, args')))
                               else Infer_err ErrHrtBoundUnsatisfied
                          else Infer_err ErrLifetimeLeak)
                     | None -> Infer_err ErrLifetimeConflict)
                  | Infer_err err -> Infer_err err))
         else Infer_err ErrArityMismatch
       | None -> Infer_err (ErrFunctionNotFound fname))
    | ECallExpr (callee, args) ->
      (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n _UU03a3_
               callee with
       | Infer_ok p ->
         let (p0, callee') = p in
         let (t_callee, _UU03a3_c) = p0 in
         let collect =
           let rec collect _UU03a3_0 = function
           | [] -> Infer_ok (([], _UU03a3_0), [])
           | e' :: es ->
             (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n
                      _UU03a3_0 e' with
              | Infer_ok p1 ->
                let (p2, e_elab) = p1 in
                let (t_e, _UU03a3_1) = p2 in
                (match collect _UU03a3_1 es with
                 | Infer_ok p3 ->
                   let (p4, es_elab) = p3 in
                   let (tys, _UU03a3_2) = p4 in
                   Infer_ok (((t_e :: tys), _UU03a3_2), (e_elab :: es_elab))
                 | Infer_err err -> Infer_err err)
              | Infer_err err -> Infer_err err)
           in collect
         in
         (match collect _UU03a3_c args with
          | Infer_ok p1 ->
            let (p2, args') = p1 in
            let (arg_tys, _UU03a3_') = p2 in
            (match ty_core t_callee with
             | TFn (param_tys, ret) ->
               (match check_arg_tys _UU03a9_ arg_tys param_tys with
                | Some err -> Infer_err err
                | None ->
                  Infer_ok ((ret, _UU03a3_'), (ECallExpr (callee', args'))))
             | TClosure (_, param_tys, ret) ->
               (match check_arg_tys _UU03a9_ arg_tys param_tys with
                | Some err -> Infer_err err
                | None ->
                  Infer_ok ((ret, _UU03a3_'), (ECallExpr (callee', args'))))
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
                             then Infer_ok ((ret_open, _UU03a3_'), (ECallExpr
                                    (callee', args')))
                             else Infer_err ErrHrtBoundUnsatisfied)
                   | None -> Infer_err ErrLifetimeConflict)
                | TClosure (env_lt, param_tys, ret) ->
                  (match build_bound_sigma (repeat None m) arg_tys param_tys with
                   | Some _UU03c3_0 ->
                     let _UU03c3_ = complete_bound_sigma_with_vars n _UU03c3_0
                     in
                     let param_tys_open =
                       map (open_bound_ty _UU03c3_) param_tys
                     in
                     (match check_arg_tys _UU03a9_ arg_tys param_tys_open with
                      | Some err -> Infer_err err
                      | None ->
                        let env_open = open_bound_lifetime _UU03c3_ env_lt in
                        let ret_open = open_bound_ty _UU03c3_ ret in
                        let bounds_open = open_bound_outlives _UU03c3_ bounds
                        in
                        if (||)
                             ((||) (contains_lbound_lifetime env_open)
                               (contains_lbound_ty ret_open))
                             (contains_lbound_outlives bounds_open)
                        then Infer_err ErrHrtUnresolvedBound
                        else if outlives_constraints_hold_b _UU03a9_
                                  bounds_open
                             then Infer_ok ((ret_open, _UU03a3_'), (ECallExpr
                                    (callee', args')))
                             else Infer_err ErrHrtBoundUnsatisfied)
                   | None -> Infer_err ErrLifetimeConflict)
                | TTypeForall (type_params, type_bounds, type_body) ->
                  (match infer_mixed_forall_call_env_elab env _UU03a9_ n m
                           bounds type_params type_bounds type_body arg_tys with
                   | Infer_ok p3 ->
                     let (type_args, ret) = p3 in
                     Infer_ok ((ret, _UU03a3_'), (ECallExprGeneric (callee',
                     type_args, args')))
                   | Infer_err err -> Infer_err err)
                | x -> Infer_err (ErrMalformedHrtBody x))
             | TTypeForall (type_params, bounds, body) ->
               (match infer_type_forall_call_env_elab env _UU03a9_
                        type_params bounds body arg_tys with
                | Infer_ok p3 ->
                  let (type_args, ret) = p3 in
                  Infer_ok ((ret, _UU03a3_'), (ECallExprGeneric (callee',
                  type_args, args')))
                | Infer_err err -> Infer_err err)
             | x -> Infer_err (ErrNotAFunction x))
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    | ECallExprGeneric (_, _, _) -> Infer_err ErrNotImplemented
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
                                 | [] -> Infer_ok (_UU03a3_0, [])
                                 | f :: rest ->
                                   (match lookup_field_b f.field_name fields with
                                    | Some e_field ->
                                      (match infer_core_env_state_fuel_elab
                                               fuel' env _UU03a9_ n _UU03a3_0
                                               e_field with
                                       | Infer_ok p ->
                                         let (p0, e_field') = p in
                                         let (t_field, _UU03a3_1) = p0 in
                                         let t_expected =
                                           instantiate_struct_field_ty lts
                                             args f
                                         in
                                         if ty_compatible_b _UU03a9_ t_field
                                              t_expected
                                         then (match go _UU03a3_1 rest with
                                               | Infer_ok p1 ->
                                                 let (_UU03a3_2, fields') = p1
                                                 in
                                                 Infer_ok (_UU03a3_2,
                                                 ((f.field_name,
                                                 e_field') :: fields'))
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
                               (match go _UU03a3_ s.struct_fields with
                                | Infer_ok p ->
                                  let (_UU03a3_', fields') = p in
                                  Infer_ok
                                  (((instantiate_struct_instance_ty s lts
                                      args),
                                  _UU03a3_'), (EStruct (sname, lts, args,
                                  fields')))
                                | Infer_err err -> Infer_err err)))))
       | None -> Infer_err (ErrStructNotFound sname))
    | EEnum (enum_name0, variant_name, lts, variant_lts, args, payloads) ->
      (match lookup_enum enum_name0 env with
       | Some edef ->
         if negb (Nat.eqb (length lts) edef.enum_lifetimes)
         then Infer_err ErrArityMismatch
         else if negb (Nat.eqb (length args) edef.enum_type_params)
              then Infer_err ErrArityMismatch
              else (match check_struct_bounds env edef.enum_bounds args with
                    | Some err -> Infer_err err
                    | None ->
                      if negb (enum_outlives_hold_b _UU03a9_ edef lts)
                      then Infer_err ErrLifetimeConflict
                      else (match lookup_enum_variant variant_name
                                    edef.enum_variants with
                            | Some vdef ->
                              if negb
                                   (Nat.eqb (length variant_lts)
                                     vdef.enum_variant_lifetimes)
                              then Infer_err ErrArityMismatch
                              else let go =
                                     let rec go _UU03a3_0 fields es =
                                       match fields with
                                       | [] ->
                                         (match es with
                                          | [] -> Infer_ok (_UU03a3_0, [])
                                          | _ :: _ ->
                                            Infer_err ErrArityMismatch)
                                       | t_field :: fields' ->
                                         (match es with
                                          | [] -> Infer_err ErrArityMismatch
                                          | e_payload :: es' ->
                                            (match infer_core_env_state_fuel_elab
                                                     fuel' env _UU03a9_ n
                                                     _UU03a3_0 e_payload with
                                             | Infer_ok p ->
                                               let (p0, e_payload') = p in
                                               let (t_payload, _UU03a3_1) = p0
                                               in
                                               let t_expected =
                                                 instantiate_enum_variant_field_ty
                                                   lts variant_lts args
                                                   t_field
                                               in
                                               if ty_compatible_b _UU03a9_
                                                    t_payload t_expected
                                               then (match go _UU03a3_1
                                                             fields' es' with
                                                     | Infer_ok p1 ->
                                                       let (_UU03a3_2,
                                                            payloads') =
                                                         p1
                                                       in
                                                       Infer_ok (_UU03a3_2,
                                                       (e_payload' :: payloads'))
                                                     | Infer_err err ->
                                                       Infer_err err)
                                               else Infer_err
                                                      (compatible_error
                                                        t_payload t_expected)
                                             | Infer_err err -> Infer_err err))
                                     in go
                                   in
                                   (match go _UU03a3_
                                            vdef.enum_variant_fields payloads with
                                    | Infer_ok p ->
                                      let (_UU03a3_', payloads') = p in
                                      Infer_ok
                                      (((instantiate_enum_ty edef lts args),
                                      _UU03a3_'), (EEnum (enum_name0,
                                      variant_name, lts, variant_lts, args,
                                      payloads')))
                                    | Infer_err err -> Infer_err err)
                            | None ->
                              Infer_err (ErrVariantNotFound variant_name)))
       | None -> Infer_err (ErrEnumNotFound enum_name0))
    | EMatch (scrut, branches) ->
      (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n _UU03a3_
               scrut with
       | Infer_ok p ->
         let (p0, scrut') = p in
         let (t_scrut, _UU03a3_1) = p0 in
         (match ty_core t_scrut with
          | TEnum (enum_name0, lts, args) ->
            (match lookup_enum enum_name0 env with
             | Some edef ->
               (match first_duplicate_branch branches with
                | Some name -> Infer_err (ErrDuplicateVariant name)
                | None ->
                  (match first_unknown_variant_branch branches
                           edef.enum_variants with
                   | Some name -> Infer_err (ErrVariantNotFound name)
                   | None ->
                     (match first_missing_variant_branch edef.enum_variants
                              branches with
                      | Some name -> Infer_err (ErrMissingVariant name)
                      | None ->
                        let infer_first = fun defs ->
                          match defs with
                          | [] -> Infer_err (ErrMissingVariant "")
                          | v :: rest ->
                            let infer_branch = fun v0 ->
                              match lookup_expr_branch_binders
                                      v0.enum_variant_name branches with
                              | Some binders ->
                                (match lookup_branch_b v0.enum_variant_name
                                         branches with
                                 | Some e_branch ->
                                   (match match_payload_params binders lts
                                            args v0 with
                                    | Infer_ok ps ->
                                      if (&&) (params_names_nodup_b ps)
                                           (ctx_lookup_params_none_b ps
                                             _UU03a3_1)
                                      then (match infer_core_env_state_fuel_elab
                                                    fuel' env _UU03a9_ n
                                                    (sctx_add_params ps
                                                      _UU03a3_1)
                                                    e_branch with
                                            | Infer_ok p1 ->
                                              let (p2, e_branch') = p1 in
                                              let (t_branch,
                                                   _UU03a3__branch_payload) =
                                                p2
                                              in
                                              if contains_lbound_ty t_branch
                                              then Infer_err ErrLifetimeLeak
                                              else if params_ok_sctx_b env ps
                                                        _UU03a3__branch_payload
                                                   then Infer_ok (((t_branch,
                                                          (sctx_remove_params
                                                            ps
                                                            _UU03a3__branch_payload)),
                                                          e_branch'), binders)
                                                   else Infer_err
                                                          ErrContextCheckFailed
                                            | Infer_err err -> Infer_err err)
                                      else Infer_err ErrContextCheckFailed
                                    | Infer_err err -> Infer_err err)
                                 | None ->
                                   Infer_err (ErrMissingVariant
                                     v0.enum_variant_name))
                              | None ->
                                Infer_err (ErrMissingVariant
                                  v0.enum_variant_name)
                            in
                            (match infer_branch v with
                             | Infer_ok p1 ->
                               let (p2, binders) = p1 in
                               let (p3, e_branch') = p2 in
                               let (t_branch, _UU03a3__branch) = p3 in
                               let infer_rest =
                                 let rec infer_rest t_head = function
                                 | [] -> Infer_ok (([], []), [])
                                 | v0 :: rest0 ->
                                   (match infer_branch v0 with
                                    | Infer_ok p4 ->
                                      let (p5, binders0) = p4 in
                                      let (p6, e0') = p5 in
                                      let (t0, _UU03a3_0) = p6 in
                                      if ty_core_eqb (ty_core t0)
                                           (ty_core t_head)
                                      then let rest_result =
                                             infer_rest t_head rest0
                                           in
                                           (match rest_result with
                                            | Infer_ok p7 ->
                                              let (p8, bs) = p7 in
                                              let (_UU03a3_s, ts) = p8 in
                                              Infer_ok
                                              (((_UU03a3_0 :: _UU03a3_s),
                                              (t0 :: ts)),
                                              (((v0.enum_variant_name,
                                              binders0), e0') :: bs))
                                            | Infer_err err -> Infer_err err)
                                      else Infer_err (ErrTypeMismatch
                                             ((ty_core t0), (ty_core t_head)))
                                    | Infer_err err -> Infer_err err)
                                 in infer_rest
                               in
                               (match infer_rest t_branch rest with
                                | Infer_ok p4 ->
                                  let (p5, bs) = p4 in
                                  let (_UU03a3_s, ts) = p5 in
                                  Infer_ok (((t_branch,
                                  (_UU03a3__branch :: _UU03a3_s)), ts),
                                  (((v.enum_variant_name, binders),
                                  e_branch') :: bs))
                                | Infer_err err -> Infer_err err)
                             | Infer_err err -> Infer_err err)
                        in
                        (match infer_first edef.enum_variants with
                         | Infer_ok p1 ->
                           let (p2, branches') = p1 in
                           let (p3, ts_tail) = p2 in
                           let (t_head, l) = p3 in
                           (match l with
                            | [] -> Infer_err ErrContextCheckFailed
                            | _UU03a3__head :: _UU03a3__tail ->
                              (match ctx_merge_many
                                       (ctx_of_sctx _UU03a3__head)
                                       (map ctx_of_sctx _UU03a3__tail) with
                               | Some _UU0393__out ->
                                 Infer_ok (((MkTy
                                   ((usage_max_tys_nonempty t_head ts_tail),
                                   (ty_core t_head))),
                                   (sctx_of_ctx _UU0393__out)), (EMatch
                                   (scrut', branches')))
                               | None -> Infer_err ErrContextCheckFailed))
                         | Infer_err err -> Infer_err err))))
             | None -> Infer_err (ErrEnumNotFound enum_name0))
          | x -> Infer_err (ErrNotAnEnum x))
       | Infer_err err -> Infer_err err)
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
                  then (match infer_core_env_state_fuel_elab fuel' env
                                _UU03a9_ n _UU03a3_ e_new with
                        | Infer_ok p1 ->
                          let (p2, e_new') = p1 in
                          let (t_new, _UU03a3_1) = p2 in
                          if ty_compatible_b _UU03a9_ t_new t_old
                          then (match sctx_path_available _UU03a3_1 x path with
                                | Infer_ok _ ->
                                  (match sctx_restore_path _UU03a3_1 x path with
                                   | Infer_ok _UU03a3_2 ->
                                     Infer_ok ((t_old, _UU03a3_2), (EReplace
                                       (p, e_new')))
                                   | Infer_err err -> Infer_err err)
                                | Infer_err err -> Infer_err err)
                          else Infer_err (compatible_error t_new t_old)
                        | Infer_err err -> Infer_err err)
                  else Infer_err (ErrNotMutable x))
             | None -> Infer_err (ErrUnknownVar x))
          | None ->
            if writable_place_b env _UU03a3_ p
            then (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n
                          _UU03a3_ e_new with
                  | Infer_ok p0 ->
                    let (p1, e_new') = p0 in
                    let (t_new, _UU03a3_1) = p1 in
                    if ty_compatible_b _UU03a9_ t_new t_old
                    then Infer_ok ((t_old, _UU03a3_1), (EReplace (p, e_new')))
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
                       then (match infer_core_env_state_fuel_elab fuel' env
                                     _UU03a9_ n _UU03a3_ e_new with
                             | Infer_ok p1 ->
                               let (p2, e_new') = p1 in
                               let (t_new, _UU03a3_1) = p2 in
                               if ty_compatible_b _UU03a9_ t_new t_old
                               then (match sctx_path_available _UU03a3_1 x
                                             path with
                                     | Infer_ok _ ->
                                       Infer_ok (((MkTy (UUnrestricted,
                                         TUnits)), _UU03a3_1), (EAssign (p,
                                         e_new')))
                                     | Infer_err err -> Infer_err err)
                               else Infer_err (compatible_error t_new t_old)
                             | Infer_err err -> Infer_err err)
                       else Infer_err (ErrNotMutable x))
                  | None -> Infer_err (ErrUnknownVar x))
               | None ->
                 if writable_place_b env _UU03a3_ p
                 then (match infer_core_env_state_fuel_elab fuel' env
                               _UU03a9_ n _UU03a3_ e_new with
                       | Infer_ok p0 ->
                         let (p1, e_new') = p0 in
                         let (t_new, _UU03a3_1) = p1 in
                         if ty_compatible_b _UU03a9_ t_new t_old
                         then Infer_ok (((MkTy (UUnrestricted, TUnits)),
                                _UU03a3_1), (EAssign (p, e_new')))
                         else Infer_err (compatible_error t_new t_old)
                       | Infer_err err -> Infer_err err)
                 else Infer_err (ErrNotMutable root))
       | Infer_err err -> Infer_err err)
    | EBorrow (rk, p) ->
      (match infer_place_sctx env _UU03a3_ p with
       | Infer_ok t_p ->
         (match rk with
          | RShared ->
            Infer_ok (((MkTy (UUnrestricted, (TRef ((LVar n), RShared,
              t_p)))), _UU03a3_), e)
          | RUnique ->
            (match place_path p with
             | Some p0 ->
               let (x, _) = p0 in
               (match sctx_lookup_mut x _UU03a3_ with
                | Some m ->
                  (match m with
                   | MImmutable -> Infer_err (ErrImmutableBorrow x)
                   | MMutable ->
                     Infer_ok (((MkTy (UAffine, (TRef ((LVar n), RUnique,
                       t_p)))), _UU03a3_), e))
                | None -> Infer_err (ErrUnknownVar x))
             | None ->
               if place_under_unique_ref_b env _UU03a3_ p
               then Infer_ok (((MkTy (UAffine, (TRef ((LVar n), RUnique,
                      t_p)))), _UU03a3_), e)
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
               then Infer_ok ((t_inner, _UU03a3_), (EDeref r))
               else Infer_err (ErrUsageMismatch ((ty_usage t_inner),
                      UUnrestricted))
             | x -> Infer_err (ErrNotAReference x))
          | Infer_err err -> Infer_err err)
       | None ->
         (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n _UU03a3_ r with
          | Infer_ok p ->
            let (p0, r') = p in
            let (t_r, _UU03a3_') = p0 in
            (match ty_core t_r with
             | TRef (_, _, t_inner) ->
               if usage_eqb (ty_usage t_inner) UUnrestricted
               then Infer_ok ((t_inner, _UU03a3_'), (EDeref r'))
               else Infer_err (ErrUsageMismatch ((ty_usage t_inner),
                      UUnrestricted))
             | x -> Infer_err (ErrNotAReference x))
          | Infer_err err -> Infer_err err))
    | EDrop e1 ->
      (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n _UU03a3_ e1 with
       | Infer_ok p ->
         let (p0, e1') = p in
         let (_, _UU03a3_') = p0 in
         Infer_ok (((MkTy (UUnrestricted, TUnits)), _UU03a3_'), (EDrop e1'))
       | Infer_err err -> Infer_err err)
    | EIf (e1, e2, e3) ->
      (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n _UU03a3_ e1 with
       | Infer_ok p ->
         let (p0, e1') = p in
         let (t_cond, _UU03a3_1) = p0 in
         if ty_core_eqb (ty_core t_cond) TBooleans
         then (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n
                       _UU03a3_1 e2 with
               | Infer_ok p1 ->
                 let (p2, e2') = p1 in
                 let (t2, _UU03a3_2) = p2 in
                 (match infer_core_env_state_fuel_elab fuel' env _UU03a9_ n
                          _UU03a3_1 e3 with
                  | Infer_ok p3 ->
                    let (p4, e3') = p3 in
                    let (t3, _UU03a3_3) = p4 in
                    if ty_core_eqb (ty_core t2) (ty_core t3)
                    then (match ctx_merge (ctx_of_sctx _UU03a3_2)
                                  (ctx_of_sctx _UU03a3_3) with
                          | Some _UU0393_4 ->
                            Infer_ok (((MkTy
                              ((usage_max (ty_usage t2) (ty_usage t3)),
                              (ty_core t2))), (sctx_of_ctx _UU0393_4)), (EIf
                              (e1', e2', e3')))
                          | None -> Infer_err ErrContextCheckFailed)
                    else Infer_err (ErrTypeMismatch ((ty_core t2),
                           (ty_core t3)))
                  | Infer_err err -> Infer_err err)
               | Infer_err err -> Infer_err err)
         else Infer_err (ErrTypeMismatch ((ty_core t_cond), TBooleans))
       | Infer_err err -> Infer_err err))
    fuel

(** val infer_core_env_elab :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> ctx -> expr ->
    ((ty * ctx) * expr) infer_result **)

let infer_core_env_elab env _UU03a9_ n _UU0393_ e =
  match infer_core_env_state_fuel_elab
          (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) env
          _UU03a9_ n (sctx_of_ctx _UU0393_) e with
  | Infer_ok p ->
    let (p0, e') = p in
    let (t, _UU03a3_) = p0 in Infer_ok ((t, (ctx_of_sctx _UU03a3_)), e')
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
     | y :: ys -> (&&) (root_atom_eqb x y) (root_set_eqb xs ys))

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
  negb (existsb (root_atom_eqb (RStore x)) roots)

(** val roots_for_checked_result :
    global_env -> ty -> root_set -> root_set **)

let roots_for_checked_result env t roots =
  if capture_ref_free_ty_b env t then [] else roots

(** val root_env_excludes_b : ident -> root_env -> bool **)

let rec root_env_excludes_b x = function
| [] -> true
| p :: rest ->
  let (y, roots) = p in
  (&&) (if ident_eqb x y then true else roots_exclude_b x roots)
    (root_env_excludes_b x rest)

(** val roots_exclude_params_b : param list -> root_set -> bool **)

let rec roots_exclude_params_b ps roots =
  match ps with
  | [] -> true
  | p :: rest ->
    (&&) (roots_exclude_b p.param_name roots)
      (roots_exclude_params_b rest roots)

(** val root_env_excludes_params_b : param list -> root_env -> bool **)

let rec root_env_excludes_params_b ps r =
  match ps with
  | [] -> true
  | p :: rest ->
    (&&) (root_env_excludes_b p.param_name r)
      (root_env_excludes_params_b rest r)

(** val root_env_add_params_roots_same :
    param list -> root_set -> root_env -> root_env **)

let rec root_env_add_params_roots_same ps roots r =
  match ps with
  | [] -> r
  | p :: rest ->
    root_env_add p.param_name roots
      (root_env_add_params_roots_same rest roots r)

(** val root_env_remove_match_params : param list -> root_env -> root_env **)

let rec root_env_remove_match_params ps r =
  match ps with
  | [] -> r
  | p :: rest ->
    root_env_remove_match_params rest (root_env_remove p.param_name r)

(** val root_env_lookup_params_none_b : param list -> root_env -> bool **)

let rec root_env_lookup_params_none_b ps r =
  match ps with
  | [] -> true
  | p :: rest ->
    (match root_env_lookup p.param_name r with
     | Some _ -> false
     | None -> root_env_lookup_params_none_b rest r)

(** val preservation_ready_expr_b : expr -> bool **)

let rec preservation_ready_expr_b = function
| EUnit -> true
| ELit _ -> true
| EVar _ -> true
| EFn _ -> true
| EPlace p -> (match place_path p with
               | Some _ -> true
               | None -> false)
| EStruct (_, _, _, fields) ->
  let rec go = function
  | [] -> true
  | p :: rest ->
    let (_, e_field) = p in (&&) (preservation_ready_expr_b e_field) (go rest)
  in go fields
| EEnum (_, _, _, _, _, payloads) ->
  forallb preservation_ready_expr_b payloads
| EMatch (scrut, branches) ->
  (&&) (preservation_ready_expr_b scrut)
    (let rec go = function
     | [] -> true
     | p :: rest ->
       let (p0, e_branch) = p in
       let (_, binders) = p0 in
       (match binders with
        | [] -> (&&) (preservation_ready_expr_b e_branch) (go rest)
        | _ :: _ -> false)
     in go branches)
| EReplace (p, e_new) ->
  (match place_path p with
   | Some _ -> preservation_ready_expr_b e_new
   | None -> false)
| EAssign (p, e_new) ->
  (match place_path p with
   | Some _ -> preservation_ready_expr_b e_new
   | None -> false)
| EBorrow (_, p) -> (match place_path p with
                     | Some _ -> true
                     | None -> false)
| EDrop e1 -> preservation_ready_expr_b e1
| EIf (e1, e2, e3) ->
  (&&) ((&&) (preservation_ready_expr_b e1) (preservation_ready_expr_b e2))
    (preservation_ready_expr_b e3)
| _ -> false

(** val preservation_ready_args_b : expr list -> bool **)

let preservation_ready_args_b args =
  forallb preservation_ready_expr_b args

(** val preservation_ready_fields_b : (string * expr) list -> bool **)

let rec preservation_ready_fields_b = function
| [] -> true
| p :: rest ->
  let (_, e) = p in
  (&&) (preservation_ready_expr_b e) (preservation_ready_fields_b rest)

(** val provenance_ready_expr_b : expr -> bool **)

let rec provenance_ready_expr_b = function
| EUnit -> true
| ELit _ -> true
| EVar _ -> true
| ELet (_, _, _, e1, e2) ->
  (&&) (provenance_ready_expr_b e1) (provenance_ready_expr_b e2)
| ELetInfer (_, _, e1, e2) ->
  (&&) (provenance_ready_expr_b e1) (provenance_ready_expr_b e2)
| EFn _ -> true
| EPlace p -> (match place_path p with
               | Some _ -> true
               | None -> false)
| EStruct (_, _, _, fields) ->
  let rec go = function
  | [] -> true
  | p :: rest ->
    let (_, e_field) = p in (&&) (provenance_ready_expr_b e_field) (go rest)
  in go fields
| EEnum (_, _, _, _, _, payloads) -> forallb provenance_ready_expr_b payloads
| EMatch (scrut, branches) ->
  (&&) (provenance_ready_expr_b scrut)
    (let rec go = function
     | [] -> true
     | p :: rest ->
       let (_, e_branch) = p in
       (&&) (provenance_ready_expr_b e_branch) (go rest)
     in go branches)
| EReplace (_, e_new) -> provenance_ready_expr_b e_new
| EAssign (_, e_new) -> provenance_ready_expr_b e_new
| EBorrow (_, p) -> (match place_path p with
                     | Some _ -> true
                     | None -> false)
| EDeref e0 ->
  (match e0 with
   | EBorrow (_, p) ->
     (match place_path p with
      | Some _ -> true
      | None -> false)
   | _ -> false)
| EDrop e1 -> provenance_ready_expr_b e1
| EIf (e1, e2, e3) ->
  (&&) ((&&) (provenance_ready_expr_b e1) (provenance_ready_expr_b e2))
    (provenance_ready_expr_b e3)
| _ -> false

(** val provenance_ready_args_b : expr list -> bool **)

let provenance_ready_args_b args =
  forallb provenance_ready_expr_b args

(** val provenance_ready_fields_b : (string * expr) list -> bool **)

let rec provenance_ready_fields_b = function
| [] -> true
| p :: rest ->
  let (_, e) = p in
  (&&) (provenance_ready_expr_b e) (provenance_ready_fields_b rest)

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
       | Some fdef ->
         if no_captures_b fdef
         then Infer_ok ((((fn_value_ty fdef), _UU03a3_), r), [])
         else Infer_err ErrNotImplemented
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EMakeClosure (fname, captures) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         (match check_make_closure_captures_sctx_with_env env _UU03a9_
                  _UU03a3_ captures fdef.fn_captures with
          | Infer_ok p ->
            let (env_lt, captured_tys) = p in
            Infer_ok ((((closure_value_ty_at env_lt fdef captured_tys),
            _UU03a3_), r), [])
          | Infer_err err -> Infer_err err)
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EPlace p ->
      (match consume_direct_place_value_roots env _UU03a3_ r p with
       | Infer_ok p0 -> let (p1, roots) = p0 in Infer_ok ((p1, r), roots)
       | Infer_err err -> Infer_err err)
    | ECall (fname, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if (&&) (no_captures_b fdef)
              (Nat.eqb fdef.fn_type_params Big_int_Z.zero_big_int)
         then let m = fdef.fn_lifetimes in
              let collect =
                let rec collect _UU03a3_0 r0 = function
                | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
                | e' :: es ->
                  (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                           r0 _UU03a3_0 e' with
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
                            if outlives_constraints_hold_b _UU03a9_
                                 _UU03a9__subst
                            then Infer_ok
                                   ((((apply_lt_ty _UU03c3_ fdef.fn_ret),
                                   _UU03a3_'), r'),
                                   (root_sets_union arg_roots))
                            else Infer_err ErrHrtBoundUnsatisfied
                       else Infer_err ErrLifetimeLeak)
                  | None -> Infer_err ErrLifetimeConflict)
               | Infer_err err -> Infer_err err)
         else Infer_err ErrNotImplemented
       | None -> Infer_err (ErrFunctionNotFound fname))
    | ECallGeneric (fname, type_args, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if (&&) (no_captures_b fdef)
              (Nat.eqb (length type_args) fdef.fn_type_params)
         then (match check_struct_bounds env fdef.fn_bounds type_args with
               | Some err -> Infer_err err
               | None ->
                 let m = fdef.fn_lifetimes in
                 let params_typed = apply_type_params type_args fdef.fn_params
                 in
                 let collect =
                   let rec collect _UU03a3_0 r0 = function
                   | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
                   | e' :: es ->
                     (match infer_core_env_state_fuel_roots fuel' env
                              _UU03a9_ n r0 _UU03a3_0 e' with
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
                    (match build_sigma m (repeat None m) arg_tys params_typed with
                     | Some _UU03c3__acc ->
                       let _UU03c3_ = finalize_subst _UU03c3__acc in
                       let ps_subst = apply_lt_params _UU03c3_ params_typed in
                       (match check_args _UU03a9_ arg_tys ps_subst with
                        | Some err -> Infer_err err
                        | None ->
                          if forallb (wf_lifetime_b (mk_region_ctx n))
                               _UU03c3_
                          then let _UU03a9__subst =
                                 apply_lt_outlives _UU03c3_ fdef.fn_outlives
                               in
                               if outlives_constraints_hold_b _UU03a9_
                                    _UU03a9__subst
                               then Infer_ok
                                      ((((apply_lt_ty _UU03c3_
                                           (subst_type_params_ty type_args
                                             fdef.fn_ret)),
                                      _UU03a3_'), r'),
                                      (root_sets_union arg_roots))
                               else Infer_err ErrHrtBoundUnsatisfied
                          else Infer_err ErrLifetimeLeak)
                     | None -> Infer_err ErrLifetimeConflict)
                  | Infer_err err -> Infer_err err))
         else Infer_err ErrArityMismatch
       | None -> Infer_err (ErrFunctionNotFound fname))
    | ECallExpr (callee, args) ->
      (match callee with
       | EUnit ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ELit _ ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EVar _ ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ELet (_, _, _, _, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ELetInfer (_, _, _, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EFn _ ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EMakeClosure (fname, captures) ->
         (match lookup_fn_b fname env.env_fns with
          | Some fdef ->
            (match check_make_closure_captures_sctx_with_env env _UU03a9_
                     _UU03a3_ captures fdef.fn_captures with
             | Infer_ok _ ->
               let collect =
                 let rec collect _UU03a3_0 r0 = function
                 | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
                 | e' :: es ->
                   (match infer_core_env_state_fuel_roots fuel' env _UU03a9_
                            n r0 _UU03a3_0 e' with
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
                  (match build_sigma fdef.fn_lifetimes
                           (repeat None fdef.fn_lifetimes) arg_tys
                           fdef.fn_params with
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
                             if outlives_constraints_hold_b _UU03a9_
                                  _UU03a9__subst
                             then Infer_ok
                                    ((((apply_lt_ty _UU03c3_ fdef.fn_ret),
                                    _UU03a3_'), r'),
                                    (root_sets_union arg_roots))
                             else Infer_err ErrHrtBoundUnsatisfied
                        else Infer_err ErrLifetimeLeak)
                   | None -> Infer_err ErrLifetimeConflict)
                | Infer_err err -> Infer_err err)
             | Infer_err err -> Infer_err err)
          | None -> Infer_err (ErrFunctionNotFound fname))
       | EPlace _ ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ECall (_, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ECallGeneric (_, _, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ECallExpr (_, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ECallExprGeneric (_, _, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EStruct (_, _, _, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EEnum (_, _, _, _, _, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EMatch (_, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EReplace (_, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EAssign (_, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EBorrow (_, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EDeref _ ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EDrop _ ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EIf (_, _, _) ->
         (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r
                  _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n
                         r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err))
    | ECallExprGeneric (callee, type_args, args) ->
      (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r _UU03a3_
               callee with
       | Infer_ok p ->
         let (p0, roots_callee) = p in
         let (p1, r1) = p0 in
         let (t_callee, _UU03a3_1) = p1 in
         let collect =
           let rec collect _UU03a3_0 r0 = function
           | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
           | e' :: es ->
             (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r0
                      _UU03a3_0 e' with
              | Infer_ok p2 ->
                let (p3, roots_e) = p2 in
                let (p4, r2) = p3 in
                let (t_e, _UU03a3_2) = p4 in
                (match collect _UU03a3_2 r2 es with
                 | Infer_ok p5 ->
                   let (p6, roots_es) = p5 in
                   let (p7, r3) = p6 in
                   let (tys, _UU03a3_3) = p7 in
                   Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                   (roots_e :: roots_es))
                 | Infer_err err -> Infer_err err)
              | Infer_err err -> Infer_err err)
           in collect
         in
         (match collect _UU03a3_1 r1 args with
          | Infer_ok p2 ->
            let (p3, arg_roots) = p2 in
            let (p4, r') = p3 in
            let (arg_tys, _UU03a3_') = p4 in
            (match ty_core t_callee with
             | TTypeForall (_, bounds, body) ->
               (match ty_core body with
                | TFn (param_tys, ret) ->
                  (match check_type_forall_bounds env bounds type_args with
                   | Some err -> Infer_err err
                   | None ->
                     (match check_arg_tys _UU03a9_ arg_tys
                              (map (subst_type_params_ty type_args) param_tys) with
                      | Some err -> Infer_err err
                      | None ->
                        Infer_ok ((((subst_type_params_ty type_args ret),
                          _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))))
                | x -> Infer_err (ErrMalformedHrtBody x))
             | _ -> Infer_err ErrNotImplemented)
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
    | EEnum (enum_name0, variant_name, lts, variant_lts, args, payloads) ->
      (match lookup_enum enum_name0 env with
       | Some edef ->
         if negb (Nat.eqb (length lts) edef.enum_lifetimes)
         then Infer_err ErrArityMismatch
         else if negb (Nat.eqb (length args) edef.enum_type_params)
              then Infer_err ErrArityMismatch
              else (match check_struct_bounds env edef.enum_bounds args with
                    | Some err -> Infer_err err
                    | None ->
                      if negb (enum_outlives_hold_b _UU03a9_ edef lts)
                      then Infer_err ErrLifetimeConflict
                      else (match lookup_enum_variant variant_name
                                    edef.enum_variants with
                            | Some vdef ->
                              if negb
                                   (Nat.eqb (length variant_lts)
                                     vdef.enum_variant_lifetimes)
                              then Infer_err ErrArityMismatch
                              else let go =
                                     let rec go _UU03a3_0 r0 fields es =
                                       match fields with
                                       | [] ->
                                         (match es with
                                          | [] ->
                                            Infer_ok ((_UU03a3_0, r0), [])
                                          | _ :: _ ->
                                            Infer_err ErrArityMismatch)
                                       | t_field :: fields' ->
                                         (match es with
                                          | [] -> Infer_err ErrArityMismatch
                                          | e_payload :: es' ->
                                            (match infer_core_env_state_fuel_roots
                                                     fuel' env _UU03a9_ n r0
                                                     _UU03a3_0 e_payload with
                                             | Infer_ok p ->
                                               let (p0, roots_payload) = p in
                                               let (p1, r1) = p0 in
                                               let (t_payload, _UU03a3_1) = p1
                                               in
                                               let t_expected =
                                                 instantiate_enum_variant_field_ty
                                                   lts variant_lts args
                                                   t_field
                                               in
                                               if ty_compatible_b _UU03a9_
                                                    t_payload t_expected
                                               then (match go _UU03a3_1 r1
                                                             fields' es' with
                                                     | Infer_ok p2 ->
                                                       let (p3, roots_rest) =
                                                         p2
                                                       in
                                                       Infer_ok (p3,
                                                       (root_set_union
                                                         roots_payload
                                                         roots_rest))
                                                     | Infer_err err ->
                                                       Infer_err err)
                                               else Infer_err
                                                      (compatible_error
                                                        t_payload t_expected)
                                             | Infer_err err -> Infer_err err))
                                     in go
                                   in
                                   (match go _UU03a3_ r
                                            vdef.enum_variant_fields payloads with
                                    | Infer_ok p ->
                                      let (p0, roots) = p in
                                      let (_UU03a3_', r') = p0 in
                                      Infer_ok
                                      ((((instantiate_enum_ty edef lts args),
                                      _UU03a3_'), r'), roots)
                                    | Infer_err err -> Infer_err err)
                            | None ->
                              Infer_err (ErrVariantNotFound variant_name)))
       | None -> Infer_err (ErrEnumNotFound enum_name0))
    | EMatch (scrut, branches) ->
      (match infer_core_env_state_fuel_roots fuel' env _UU03a9_ n r _UU03a3_
               scrut with
       | Infer_ok p ->
         let (p0, roots_scrut) = p in
         let (p1, r1) = p0 in
         let (t_scrut, _UU03a3_1) = p1 in
         (match ty_core t_scrut with
          | TEnum (enum_name0, lts, args) ->
            (match lookup_enum enum_name0 env with
             | Some edef ->
               if negb (Nat.eqb (length lts) edef.enum_lifetimes)
               then Infer_err ErrArityMismatch
               else if negb (Nat.eqb (length args) edef.enum_type_params)
                    then Infer_err ErrArityMismatch
                    else (match check_struct_bounds env edef.enum_bounds args with
                          | Some err -> Infer_err err
                          | None ->
                            if negb (enum_outlives_hold_b _UU03a9_ edef lts)
                            then Infer_err ErrLifetimeConflict
                            else (match first_duplicate_branch branches with
                                  | Some name ->
                                    Infer_err (ErrDuplicateVariant name)
                                  | None ->
                                    (match first_unknown_variant_branch
                                             branches edef.enum_variants with
                                     | Some name ->
                                       Infer_err (ErrVariantNotFound name)
                                     | None ->
                                       (match first_missing_variant_branch
                                                edef.enum_variants branches with
                                        | Some name ->
                                          Infer_err (ErrMissingVariant name)
                                        | None ->
                                          let infer_first = fun defs ->
                                            match defs with
                                            | [] ->
                                              Infer_err (ErrMissingVariant "")
                                            | v :: rest ->
                                              let infer_branch = fun v0 ->
                                                match lookup_expr_branch_binders
                                                        v0.enum_variant_name
                                                        branches with
                                                | Some binders ->
                                                  (match lookup_branch_b
                                                           v0.enum_variant_name
                                                           branches with
                                                   | Some e_branch ->
                                                     (match match_payload_params
                                                              binders lts
                                                              args v0 with
                                                      | Infer_ok ps ->
                                                        if (&&)
                                                             ((&&)
                                                               (params_names_nodup_b
                                                                 ps)
                                                               (ctx_lookup_params_none_b
                                                                 ps _UU03a3_1))
                                                             (root_env_lookup_params_none_b
                                                               ps r1)
                                                        then let r_payload =
                                                               root_env_add_params_roots_same
                                                                 ps
                                                                 roots_scrut
                                                                 r1
                                                             in
                                                             (match infer_core_env_state_fuel_roots
                                                                    fuel' env
                                                                    _UU03a9_
                                                                    n
                                                                    r_payload
                                                                    (sctx_add_params
                                                                    ps
                                                                    _UU03a3_1)
                                                                    e_branch with
                                                              | Infer_ok p2 ->
                                                                let (
                                                                  p3,
                                                                  roots_branch) =
                                                                  p2
                                                                in
                                                                let (
                                                                  p4,
                                                                  r_branch_payload) =
                                                                  p3
                                                                in
                                                                let (
                                                                  t_branch,
                                                                  _UU03a3__branch_payload) =
                                                                  p4
                                                                in
                                                                let r_branch =
                                                                  root_env_remove_match_params
                                                                    ps
                                                                    r_branch_payload
                                                                in
                                                                if contains_lbound_ty
                                                                    t_branch
                                                                then 
                                                                  Infer_err
                                                                    ErrLifetimeLeak
                                                                else 
                                                                  if 
                                                                    (&&)
                                                                    ((&&)
                                                                    (params_ok_sctx_b
                                                                    env ps
                                                                    _UU03a3__branch_payload)
                                                                    (roots_exclude_params_b
                                                                    ps
                                                                    roots_branch))
                                                                    (root_env_excludes_params_b
                                                                    ps
                                                                    r_branch)
                                                                  then 
                                                                    Infer_ok
                                                                    (((t_branch,
                                                                    (sctx_remove_params
                                                                    ps
                                                                    _UU03a3__branch_payload)),
                                                                    r_branch),
                                                                    roots_branch)
                                                                  else 
                                                                    Infer_err
                                                                    ErrContextCheckFailed
                                                              | Infer_err err ->
                                                                Infer_err err)
                                                        else Infer_err
                                                               ErrContextCheckFailed
                                                      | Infer_err err ->
                                                        Infer_err err)
                                                   | None ->
                                                     Infer_err
                                                       (ErrMissingVariant
                                                       v0.enum_variant_name))
                                                | None ->
                                                  Infer_err
                                                    (ErrMissingVariant
                                                    v0.enum_variant_name)
                                              in
                                              (match infer_branch v with
                                               | Infer_ok p2 ->
                                                 let (p3, roots_branch) = p2
                                                 in
                                                 let (p4, r_branch) = p3 in
                                                 let (t_branch,
                                                      _UU03a3__branch) =
                                                   p4
                                                 in
                                                 let infer_rest =
                                                   let rec infer_rest t_head r_out = function
                                                   | [] ->
                                                     Infer_ok (([], []), [])
                                                   | v0 :: rest0 ->
                                                     (match infer_branch v0 with
                                                      | Infer_ok p5 ->
                                                        let (p6, roots0) = p5
                                                        in
                                                        let (p7, r0) = p6 in
                                                        let (t0, _UU03a3_0) =
                                                          p7
                                                        in
                                                        if ty_core_eqb
                                                             (ty_core t0)
                                                             (ty_core t_head)
                                                        then let rest_ok =
                                                               let rest_result =
                                                                 infer_rest
                                                                   t_head
                                                                   r_out rest0
                                                               in
                                                               (match rest_result with
                                                                | Infer_ok p8 ->
                                                                  let (
                                                                    p9, rootss) =
                                                                    p8
                                                                  in
                                                                  let (
                                                                    _UU03a3_s,
                                                                    ts) = p9
                                                                  in
                                                                  Infer_ok
                                                                  (((_UU03a3_0 :: _UU03a3_s),
                                                                  (t0 :: ts)),
                                                                  (roots0 :: rootss))
                                                                | Infer_err err ->
                                                                  Infer_err
                                                                    err)
                                                             in
                                                             let context_error =
                                                               Infer_err
                                                               ErrContextCheckFailed
                                                             in
                                                             infer_if_bool
                                                               (root_env_eqb
                                                                 r0 r_out)
                                                               rest_ok
                                                               context_error
                                                        else Infer_err
                                                               (ErrTypeMismatch
                                                               ((ty_core t0),
                                                               (ty_core
                                                                 t_head)))
                                                      | Infer_err err ->
                                                        Infer_err err)
                                                   in infer_rest
                                                 in
                                                 (match infer_rest t_branch
                                                          r_branch rest with
                                                  | Infer_ok p5 ->
                                                    let (p6, rootss) = p5 in
                                                    let (_UU03a3_s, ts) = p6
                                                    in
                                                    Infer_ok ((((((t_branch,
                                                    _UU03a3__branch),
                                                    r_branch), roots_branch),
                                                    _UU03a3_s), ts), rootss)
                                                  | Infer_err err ->
                                                    Infer_err err)
                                               | Infer_err err ->
                                                 Infer_err err)
                                          in
                                          (match infer_first
                                                   edef.enum_variants with
                                           | Infer_ok p2 ->
                                             let (p3, roots_tail) = p2 in
                                             let (p4, ts_tail) = p3 in
                                             let (p5, _UU03a3__tail) = p4 in
                                             let (p6, roots_head) = p5 in
                                             let (p7, r_out) = p6 in
                                             let (t_head, _UU03a3__head) = p7
                                             in
                                             (match ctx_merge_many
                                                      (ctx_of_sctx
                                                        _UU03a3__head)
                                                      (map ctx_of_sctx
                                                        _UU03a3__tail) with
                                              | Some _UU0393__out ->
                                                Infer_ok ((((MkTy
                                                  ((usage_max_tys_nonempty
                                                     t_head ts_tail),
                                                  (ty_core t_head))),
                                                  (sctx_of_ctx _UU0393__out)),
                                                  r_out),
                                                  (root_sets_union
                                                    (roots_head :: roots_tail)))
                                              | None ->
                                                Infer_err
                                                  ErrContextCheckFailed)
                                           | Infer_err err -> Infer_err err)))))
             | None -> Infer_err (ErrEnumNotFound enum_name0))
          | x -> Infer_err (ErrNotAnEnum x))
       | Infer_err err -> Infer_err err)
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
       | None ->
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_old ->
            if place_resolved_write_writable_chain_b env r _UU03a3_ p
            then (match place_resolved_write_target r p with
                  | Some x ->
                    (match root_env_lookup x r with
                     | Some roots_result ->
                       (match sctx_lookup_mut x _UU03a3_ with
                        | Some m ->
                          (match m with
                           | MImmutable -> Infer_err (ErrNotMutable x)
                           | MMutable ->
                             if writable_place_b env _UU03a3_ p
                             then (match infer_core_env_state_fuel_roots
                                           fuel' env _UU03a9_ n r _UU03a3_
                                           e_new with
                                   | Infer_ok p0 ->
                                     let (p1, roots_new) = p0 in
                                     let (p2, r1) = p1 in
                                     let (t_new, _UU03a3_1) = p2 in
                                     (match root_env_lookup x r1 with
                                      | Some roots_old ->
                                        if ty_compatible_b _UU03a9_ t_new
                                             t_old
                                        then Infer_ok (((t_old, _UU03a3_1),
                                               (root_env_update x
                                                 (root_set_union roots_old
                                                   roots_new)
                                                 r1)),
                                               roots_result)
                                        else Infer_err
                                               (compatible_error t_new t_old)
                                      | None ->
                                        Infer_err ErrContextCheckFailed)
                                   | Infer_err err -> Infer_err err)
                             else Infer_err (ErrNotMutable x))
                        | None -> Infer_err (ErrUnknownVar x))
                     | None -> Infer_err ErrContextCheckFailed)
                  | None -> Infer_err ErrNotImplemented)
            else Infer_err ErrNotImplemented
          | Infer_err err -> Infer_err err))
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
       | None ->
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_old ->
            if usage_eqb (ty_usage t_old) ULinear
            then Infer_err (ErrUsageMismatch ((ty_usage t_old), UAffine))
            else if place_resolved_write_writable_chain_b env r _UU03a3_ p
                 then (match place_resolved_write_target r p with
                       | Some x ->
                         (match sctx_lookup_mut x _UU03a3_ with
                          | Some m ->
                            (match m with
                             | MImmutable -> Infer_err (ErrNotMutable x)
                             | MMutable ->
                               if writable_place_b env _UU03a3_ p
                               then (match infer_core_env_state_fuel_roots
                                             fuel' env _UU03a9_ n r _UU03a3_
                                             e_new with
                                     | Infer_ok p0 ->
                                       let (p1, roots_new) = p0 in
                                       let (p2, r1) = p1 in
                                       let (t_new, _UU03a3_1) = p2 in
                                       (match root_env_lookup x r1 with
                                        | Some roots_old ->
                                          if ty_compatible_b _UU03a9_ t_new
                                               t_old
                                          then Infer_ok ((((MkTy
                                                 (UUnrestricted, TUnits)),
                                                 _UU03a3_1),
                                                 (root_env_update x
                                                   (root_set_union roots_old
                                                     roots_new)
                                                   r1)),
                                                 [])
                                          else Infer_err
                                                 (compatible_error t_new
                                                   t_old)
                                        | None ->
                                          Infer_err ErrContextCheckFailed)
                                     | Infer_err err -> Infer_err err)
                               else Infer_err (ErrNotMutable x))
                          | None -> Infer_err (ErrUnknownVar x))
                       | None -> Infer_err ErrNotImplemented)
                 else Infer_err ErrNotImplemented
          | Infer_err err -> Infer_err err))
    | EBorrow (rk, p) ->
      (match infer_place_sctx env _UU03a3_ p with
       | Infer_ok t_p ->
         (match place_path p with
          | Some p0 ->
            let (x, _) = p0 in
            (match rk with
             | RShared ->
               Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n), RShared,
                 t_p)))), _UU03a3_), r), ((RStore x) :: []))
             | RUnique ->
               (match sctx_lookup_mut x _UU03a3_ with
                | Some m ->
                  (match m with
                   | MImmutable -> Infer_err (ErrImmutableBorrow x)
                   | MMutable ->
                     Infer_ok ((((MkTy (UAffine, (TRef ((LVar n), RUnique,
                       t_p)))), _UU03a3_), r), ((RStore x) :: [])))
                | None -> Infer_err (ErrUnknownVar x)))
          | None ->
            (match rk with
             | RShared ->
               (match place_resolved_roots r p with
                | Some roots ->
                  (match singleton_store_root roots with
                   | Some _ ->
                     Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n),
                       RShared, t_p)))), _UU03a3_), r), roots)
                   | None ->
                     (match place_borrow_roots r p with
                      | Some roots0 ->
                        Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n),
                          RShared, t_p)))), _UU03a3_), r), roots0)
                      | None -> Infer_err ErrContextCheckFailed))
                | None ->
                  (match place_borrow_roots r p with
                   | Some roots ->
                     Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n),
                       RShared, t_p)))), _UU03a3_), r), roots)
                   | None -> Infer_err ErrContextCheckFailed))
             | RUnique ->
               if place_under_unique_ref_b env _UU03a3_ p
               then if place_resolved_write_writable_chain_b env r _UU03a3_ p
                    then (match place_resolved_write_target r p with
                          | Some x ->
                            let roots = (RStore x) :: [] in
                            Infer_ok ((((MkTy (UAffine, (TRef ((LVar n),
                            RUnique, t_p)))), _UU03a3_), r), roots)
                          | None ->
                            (match place_resolved_roots r p with
                             | Some roots ->
                               (match singleton_store_root roots with
                                | Some _ ->
                                  Infer_ok ((((MkTy (UAffine, (TRef ((LVar
                                    n), RUnique, t_p)))), _UU03a3_), r),
                                    roots)
                                | None ->
                                  (match place_borrow_roots r p with
                                   | Some roots0 ->
                                     Infer_ok ((((MkTy (UAffine, (TRef ((LVar
                                       n), RUnique, t_p)))), _UU03a3_), r),
                                       roots0)
                                   | None -> Infer_err ErrContextCheckFailed))
                             | None ->
                               (match place_borrow_roots r p with
                                | Some roots ->
                                  Infer_ok ((((MkTy (UAffine, (TRef ((LVar
                                    n), RUnique, t_p)))), _UU03a3_), r),
                                    roots)
                                | None -> Infer_err ErrContextCheckFailed)))
                    else (match place_resolved_roots r p with
                          | Some roots ->
                            (match singleton_store_root roots with
                             | Some _ ->
                               Infer_ok ((((MkTy (UAffine, (TRef ((LVar n),
                                 RUnique, t_p)))), _UU03a3_), r), roots)
                             | None ->
                               (match place_borrow_roots r p with
                                | Some roots0 ->
                                  Infer_ok ((((MkTy (UAffine, (TRef ((LVar
                                    n), RUnique, t_p)))), _UU03a3_), r),
                                    roots0)
                                | None -> Infer_err ErrContextCheckFailed))
                          | None ->
                            (match place_borrow_roots r p with
                             | Some roots ->
                               Infer_ok ((((MkTy (UAffine, (TRef ((LVar n),
                                 RUnique, t_p)))), _UU03a3_), r), roots)
                             | None -> Infer_err ErrContextCheckFailed))
               else Infer_err (ErrImmutableBorrow (place_name p))))
       | Infer_err err -> Infer_err err)
    | EDeref e0 ->
      (match e0 with
       | EBorrow (rk, p) ->
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_p ->
            if usage_eqb (ty_usage t_p) UUnrestricted
            then (match place_path p with
                  | Some p0 ->
                    let (x, _) = p0 in
                    (match root_env_lookup x r with
                     | Some roots ->
                       (match rk with
                        | RShared -> Infer_ok (((t_p, _UU03a3_), r), roots)
                        | RUnique ->
                          (match sctx_lookup_mut x _UU03a3_ with
                           | Some m ->
                             (match m with
                              | MImmutable -> Infer_err (ErrImmutableBorrow x)
                              | MMutable ->
                                Infer_ok (((t_p, _UU03a3_), r), roots))
                           | None -> Infer_err (ErrUnknownVar x)))
                     | None -> Infer_err ErrContextCheckFailed)
                  | None ->
                    (match rk with
                     | RShared ->
                       (match place_resolved_roots r p with
                        | Some roots ->
                          (match singleton_store_root roots with
                           | Some _ -> Infer_ok (((t_p, _UU03a3_), r), roots)
                           | None ->
                             (match place_root_lookup r p with
                              | Some roots0 ->
                                Infer_ok (((t_p, _UU03a3_), r), roots0)
                              | None -> Infer_err ErrContextCheckFailed))
                        | None ->
                          (match place_root_lookup r p with
                           | Some roots ->
                             Infer_ok (((t_p, _UU03a3_), r), roots)
                           | None -> Infer_err ErrContextCheckFailed))
                     | RUnique ->
                       if place_under_unique_ref_b env _UU03a3_ p
                       then (match place_resolved_roots r p with
                             | Some roots ->
                               (match singleton_store_root roots with
                                | Some _ ->
                                  Infer_ok (((t_p, _UU03a3_), r), roots)
                                | None ->
                                  (match place_root_lookup r p with
                                   | Some roots0 ->
                                     Infer_ok (((t_p, _UU03a3_), r), roots0)
                                   | None -> Infer_err ErrContextCheckFailed))
                             | None ->
                               (match place_root_lookup r p with
                                | Some roots ->
                                  Infer_ok (((t_p, _UU03a3_), r), roots)
                                | None -> Infer_err ErrContextCheckFailed))
                       else Infer_err (ErrImmutableBorrow (place_name p))))
            else Infer_err (ErrUsageMismatch ((ty_usage t_p), UUnrestricted))
          | Infer_err err -> Infer_err err)
       | _ -> Infer_err ErrNotImplemented)
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
       | Infer_err err -> Infer_err err))
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

(** val infer_core_env_state_fuel_roots_shadow_safe :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    root_env -> sctx -> expr -> (((ty * sctx) * root_env) * root_set)
    infer_result **)

let rec infer_core_env_state_fuel_roots_shadow_safe fuel env _UU03a9_ n r _UU03a3_ e =
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
      (match infer_core_env_state_fuel_roots_shadow_safe fuel' env _UU03a9_ n
               r _UU03a3_ e1 with
       | Infer_ok p ->
         let (p0, roots1) = p in
         let (p1, r1) = p0 in
         let (t1, _UU03a3_1) = p1 in
         if ty_compatible_b _UU03a9_ t1 t
         then (match root_env_lookup x r1 with
               | Some _ -> Infer_err ErrContextCheckFailed
               | None ->
                 if (&&) (roots_exclude_b x roots1) (root_env_excludes_b x r1)
                 then (match infer_core_env_state_fuel_roots_shadow_safe
                               fuel' env _UU03a9_ n
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
                       | Infer_err err -> Infer_err err)
                 else Infer_err ErrContextCheckFailed)
         else Infer_err (compatible_error t1 t)
       | Infer_err err -> Infer_err err)
    | ELetInfer (m, x, e1, e2) ->
      (match infer_core_env_state_fuel_roots_shadow_safe fuel' env _UU03a9_ n
               r _UU03a3_ e1 with
       | Infer_ok p ->
         let (p0, roots1) = p in
         let (p1, r1) = p0 in
         let (t1, _UU03a3_1) = p1 in
         (match root_env_lookup x r1 with
          | Some _ -> Infer_err ErrContextCheckFailed
          | None ->
            if (&&) (roots_exclude_b x roots1) (root_env_excludes_b x r1)
            then (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                          _UU03a9_ n (root_env_add x roots1 r1)
                          (sctx_add x t1 m _UU03a3_1) e2 with
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
                  | Infer_err err -> Infer_err err)
            else Infer_err ErrContextCheckFailed)
       | Infer_err err -> Infer_err err)
    | EFn fname ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if no_captures_b fdef
         then Infer_ok ((((fn_value_ty fdef), _UU03a3_), r), [])
         else Infer_err ErrNotImplemented
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EMakeClosure (fname, captures) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         (match check_make_closure_captures_sctx_with_env env _UU03a9_
                  _UU03a3_ captures fdef.fn_captures with
          | Infer_ok p ->
            let (env_lt, captured_tys) = p in
            Infer_ok ((((closure_value_ty_at env_lt fdef captured_tys),
            _UU03a3_), r), [])
          | Infer_err err -> Infer_err err)
       | None -> Infer_err (ErrFunctionNotFound fname))
    | EPlace p ->
      (match consume_direct_place_value_roots env _UU03a3_ r p with
       | Infer_ok p0 -> let (p1, roots) = p0 in Infer_ok ((p1, r), roots)
       | Infer_err err -> Infer_err err)
    | ECall (fname, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if (&&) (no_captures_b fdef)
              (Nat.eqb fdef.fn_type_params Big_int_Z.zero_big_int)
         then let m = fdef.fn_lifetimes in
              let collect =
                let rec collect _UU03a3_0 r0 = function
                | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
                | e' :: es ->
                  (match infer_core_env_state_fuel_roots_shadow_safe fuel'
                           env _UU03a9_ n r0 _UU03a3_0 e' with
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
                            if outlives_constraints_hold_b _UU03a9_
                                 _UU03a9__subst
                            then Infer_ok
                                   ((((apply_lt_ty _UU03c3_ fdef.fn_ret),
                                   _UU03a3_'), r'),
                                   (root_sets_union arg_roots))
                            else Infer_err ErrHrtBoundUnsatisfied
                       else Infer_err ErrLifetimeLeak)
                  | None -> Infer_err ErrLifetimeConflict)
               | Infer_err err -> Infer_err err)
         else Infer_err ErrNotImplemented
       | None -> Infer_err (ErrFunctionNotFound fname))
    | ECallGeneric (fname, type_args, args) ->
      (match lookup_fn_b fname env.env_fns with
       | Some fdef ->
         if (&&) (no_captures_b fdef)
              (Nat.eqb (length type_args) fdef.fn_type_params)
         then (match check_struct_bounds env fdef.fn_bounds type_args with
               | Some err -> Infer_err err
               | None ->
                 let m = fdef.fn_lifetimes in
                 let params_typed = apply_type_params type_args fdef.fn_params
                 in
                 let collect =
                   let rec collect _UU03a3_0 r0 = function
                   | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
                   | e' :: es ->
                     (match infer_core_env_state_fuel_roots_shadow_safe fuel'
                              env _UU03a9_ n r0 _UU03a3_0 e' with
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
                    (match build_sigma m (repeat None m) arg_tys params_typed with
                     | Some _UU03c3__acc ->
                       let _UU03c3_ = finalize_subst _UU03c3__acc in
                       let ps_subst = apply_lt_params _UU03c3_ params_typed in
                       (match check_args _UU03a9_ arg_tys ps_subst with
                        | Some err -> Infer_err err
                        | None ->
                          if forallb (wf_lifetime_b (mk_region_ctx n))
                               _UU03c3_
                          then let _UU03a9__subst =
                                 apply_lt_outlives _UU03c3_ fdef.fn_outlives
                               in
                               if outlives_constraints_hold_b _UU03a9_
                                    _UU03a9__subst
                               then Infer_ok
                                      ((((apply_lt_ty _UU03c3_
                                           (subst_type_params_ty type_args
                                             fdef.fn_ret)),
                                      _UU03a3_'), r'),
                                      (root_sets_union arg_roots))
                               else Infer_err ErrHrtBoundUnsatisfied
                          else Infer_err ErrLifetimeLeak)
                     | None -> Infer_err ErrLifetimeConflict)
                  | Infer_err err -> Infer_err err))
         else Infer_err ErrArityMismatch
       | None -> Infer_err (ErrFunctionNotFound fname))
    | ECallExpr (callee, args) ->
      (match callee with
       | EUnit ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ELit _ ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EVar _ ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ELet (_, _, _, _, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ELetInfer (_, _, _, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EFn _ -> Infer_err ErrNotImplemented
       | EMakeClosure (fname, captures) ->
         (match lookup_fn_b fname env.env_fns with
          | Some fdef ->
            (match check_make_closure_captures_sctx_with_env env _UU03a9_
                     _UU03a3_ captures fdef.fn_captures with
             | Infer_ok _ ->
               let collect =
                 let rec collect _UU03a3_0 r0 = function
                 | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
                 | e' :: es ->
                   (match infer_core_env_state_fuel_roots_shadow_safe fuel'
                            env _UU03a9_ n r0 _UU03a3_0 e' with
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
                  (match build_sigma fdef.fn_lifetimes
                           (repeat None fdef.fn_lifetimes) arg_tys
                           fdef.fn_params with
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
                             if outlives_constraints_hold_b _UU03a9_
                                  _UU03a9__subst
                             then Infer_ok
                                    ((((apply_lt_ty _UU03c3_ fdef.fn_ret),
                                    _UU03a3_'), r'),
                                    (root_sets_union arg_roots))
                             else Infer_err ErrHrtBoundUnsatisfied
                        else Infer_err ErrLifetimeLeak)
                   | None -> Infer_err ErrLifetimeConflict)
                | Infer_err err -> Infer_err err)
             | Infer_err err -> Infer_err err)
          | None -> Infer_err (ErrFunctionNotFound fname))
       | EPlace _ ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ECall (_, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ECallGeneric (_, _, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ECallExpr (_, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | ECallExprGeneric (_, _, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EStruct (_, _, _, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EEnum (_, _, _, _, _, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EMatch (_, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EReplace (_, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EAssign (_, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EBorrow (_, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EDeref _ ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EDrop _ ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err)
       | EIf (_, _, _) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ callee with
          | Infer_ok p ->
            let (p0, roots_callee) = p in
            let (p1, r1) = p0 in
            let (t_callee, _UU03a3_1) = p1 in
            let collect =
              let rec collect _UU03a3_0 r0 = function
              | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
              | e' :: es ->
                (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                         _UU03a9_ n r0 _UU03a3_0 e' with
                 | Infer_ok p2 ->
                   let (p3, roots_e) = p2 in
                   let (p4, r2) = p3 in
                   let (t_e, _UU03a3_2) = p4 in
                   (match collect _UU03a3_2 r2 es with
                    | Infer_ok p5 ->
                      let (p6, roots_es) = p5 in
                      let (p7, r3) = p6 in
                      let (tys, _UU03a3_3) = p7 in
                      Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                      (roots_e :: roots_es))
                    | Infer_err err -> Infer_err err)
                 | Infer_err err -> Infer_err err)
              in collect
            in
            (match collect _UU03a3_1 r1 args with
             | Infer_ok p2 ->
               let (p3, arg_roots) = p2 in
               let (p4, r') = p3 in
               let (arg_tys, _UU03a3_') = p4 in
               (match ty_core t_callee with
                | TFn (param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TClosure (_, param_tys, ret) ->
                  (match check_arg_tys _UU03a9_ arg_tys param_tys with
                   | Some err -> Infer_err err
                   | None ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots))))
                | TForall (m, bounds, body) ->
                  (match ty_core body with
                   | TTypeForall (type_params, type_bounds, type_body) ->
                     (match infer_mixed_forall_call_env env _UU03a9_ n m
                              bounds type_params type_bounds type_body arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err)
                   | _ ->
                     (match infer_hrt_call_env _UU03a9_ n m bounds body
                              arg_tys with
                      | Infer_ok ret ->
                        Infer_ok (((ret, _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))
                      | Infer_err err -> Infer_err err))
                | TTypeForall (type_params, bounds, body) ->
                  (match infer_type_forall_call_env env _UU03a9_ type_params
                           bounds body arg_tys with
                   | Infer_ok ret ->
                     Infer_ok (((ret, _UU03a3_'), r'),
                       (root_set_union roots_callee
                         (root_sets_union arg_roots)))
                   | Infer_err err -> Infer_err err)
                | _ -> Infer_err ErrNotImplemented)
             | Infer_err err -> Infer_err err)
          | Infer_err err -> Infer_err err))
    | ECallExprGeneric (callee, type_args, args) ->
      (match infer_core_env_state_fuel_roots_shadow_safe fuel' env _UU03a9_ n
               r _UU03a3_ callee with
       | Infer_ok p ->
         let (p0, roots_callee) = p in
         let (p1, r1) = p0 in
         let (t_callee, _UU03a3_1) = p1 in
         let collect =
           let rec collect _UU03a3_0 r0 = function
           | [] -> Infer_ok ((([], _UU03a3_0), r0), [])
           | e' :: es ->
             (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                      _UU03a9_ n r0 _UU03a3_0 e' with
              | Infer_ok p2 ->
                let (p3, roots_e) = p2 in
                let (p4, r2) = p3 in
                let (t_e, _UU03a3_2) = p4 in
                (match collect _UU03a3_2 r2 es with
                 | Infer_ok p5 ->
                   let (p6, roots_es) = p5 in
                   let (p7, r3) = p6 in
                   let (tys, _UU03a3_3) = p7 in
                   Infer_ok ((((t_e :: tys), _UU03a3_3), r3),
                   (roots_e :: roots_es))
                 | Infer_err err -> Infer_err err)
              | Infer_err err -> Infer_err err)
           in collect
         in
         (match collect _UU03a3_1 r1 args with
          | Infer_ok p2 ->
            let (p3, arg_roots) = p2 in
            let (p4, r') = p3 in
            let (arg_tys, _UU03a3_') = p4 in
            (match ty_core t_callee with
             | TTypeForall (_, bounds, body) ->
               (match ty_core body with
                | TFn (param_tys, ret) ->
                  (match check_type_forall_bounds env bounds type_args with
                   | Some err -> Infer_err err
                   | None ->
                     (match check_arg_tys _UU03a9_ arg_tys
                              (map (subst_type_params_ty type_args) param_tys) with
                      | Some err -> Infer_err err
                      | None ->
                        Infer_ok ((((subst_type_params_ty type_args ret),
                          _UU03a3_'), r'),
                          (root_set_union roots_callee
                            (root_sets_union arg_roots)))))
                | x -> Infer_err (ErrMalformedHrtBody x))
             | _ -> Infer_err ErrNotImplemented)
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
                                 let rec go _UU03a3_0 r0 = function
                                 | [] -> Infer_ok ((_UU03a3_0, r0), [])
                                 | f :: rest ->
                                   (match lookup_field_b f.field_name fields with
                                    | Some e_field ->
                                      (match infer_core_env_state_fuel_roots_shadow_safe
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
    | EEnum (enum_name0, variant_name, lts, variant_lts, args, payloads) ->
      (match lookup_enum enum_name0 env with
       | Some edef ->
         if negb (Nat.eqb (length lts) edef.enum_lifetimes)
         then Infer_err ErrArityMismatch
         else if negb (Nat.eqb (length args) edef.enum_type_params)
              then Infer_err ErrArityMismatch
              else (match check_struct_bounds env edef.enum_bounds args with
                    | Some err -> Infer_err err
                    | None ->
                      if negb (enum_outlives_hold_b _UU03a9_ edef lts)
                      then Infer_err ErrLifetimeConflict
                      else (match lookup_enum_variant variant_name
                                    edef.enum_variants with
                            | Some vdef ->
                              if negb
                                   (Nat.eqb (length variant_lts)
                                     vdef.enum_variant_lifetimes)
                              then Infer_err ErrArityMismatch
                              else let go =
                                     let rec go _UU03a3_0 r0 fields es =
                                       match fields with
                                       | [] ->
                                         (match es with
                                          | [] ->
                                            Infer_ok ((_UU03a3_0, r0), [])
                                          | _ :: _ ->
                                            Infer_err ErrArityMismatch)
                                       | t_field :: fields' ->
                                         (match es with
                                          | [] -> Infer_err ErrArityMismatch
                                          | e_payload :: es' ->
                                            (match infer_core_env_state_fuel_roots_shadow_safe
                                                     fuel' env _UU03a9_ n r0
                                                     _UU03a3_0 e_payload with
                                             | Infer_ok p ->
                                               let (p0, roots_payload) = p in
                                               let (p1, r1) = p0 in
                                               let (t_payload, _UU03a3_1) = p1
                                               in
                                               let t_expected =
                                                 instantiate_enum_variant_field_ty
                                                   lts variant_lts args
                                                   t_field
                                               in
                                               if ty_compatible_b _UU03a9_
                                                    t_payload t_expected
                                               then (match go _UU03a3_1 r1
                                                             fields' es' with
                                                     | Infer_ok p2 ->
                                                       let (p3, roots_rest) =
                                                         p2
                                                       in
                                                       Infer_ok (p3,
                                                       (root_set_union
                                                         roots_payload
                                                         roots_rest))
                                                     | Infer_err err ->
                                                       Infer_err err)
                                               else Infer_err
                                                      (compatible_error
                                                        t_payload t_expected)
                                             | Infer_err err -> Infer_err err))
                                     in go
                                   in
                                   (match go _UU03a3_ r
                                            vdef.enum_variant_fields payloads with
                                    | Infer_ok p ->
                                      let (p0, roots) = p in
                                      let (_UU03a3_', r') = p0 in
                                      Infer_ok
                                      ((((instantiate_enum_ty edef lts args),
                                      _UU03a3_'), r'), roots)
                                    | Infer_err err -> Infer_err err)
                            | None ->
                              Infer_err (ErrVariantNotFound variant_name)))
       | None -> Infer_err (ErrEnumNotFound enum_name0))
    | EMatch (scrut, branches) ->
      (match infer_core_env_state_fuel_roots_shadow_safe fuel' env _UU03a9_ n
               r _UU03a3_ scrut with
       | Infer_ok p ->
         let (p0, roots_scrut) = p in
         let (p1, r1) = p0 in
         let (t_scrut, _UU03a3_1) = p1 in
         (match ty_core t_scrut with
          | TEnum (enum_name0, lts, args) ->
            (match lookup_enum enum_name0 env with
             | Some edef ->
               if negb (Nat.eqb (length lts) edef.enum_lifetimes)
               then Infer_err ErrArityMismatch
               else if negb (Nat.eqb (length args) edef.enum_type_params)
                    then Infer_err ErrArityMismatch
                    else (match check_struct_bounds env edef.enum_bounds args with
                          | Some err -> Infer_err err
                          | None ->
                            if negb (enum_outlives_hold_b _UU03a9_ edef lts)
                            then Infer_err ErrLifetimeConflict
                            else (match first_duplicate_branch branches with
                                  | Some name ->
                                    Infer_err (ErrDuplicateVariant name)
                                  | None ->
                                    (match first_unknown_variant_branch
                                             branches edef.enum_variants with
                                     | Some name ->
                                       Infer_err (ErrVariantNotFound name)
                                     | None ->
                                       (match first_missing_variant_branch
                                                edef.enum_variants branches with
                                        | Some name ->
                                          Infer_err (ErrMissingVariant name)
                                        | None ->
                                          let infer_first = fun defs ->
                                            match defs with
                                            | [] ->
                                              Infer_err (ErrMissingVariant "")
                                            | v :: rest ->
                                              let infer_branch = fun v0 ->
                                                match lookup_expr_branch_binders
                                                        v0.enum_variant_name
                                                        branches with
                                                | Some binders ->
                                                  (match lookup_branch_b
                                                           v0.enum_variant_name
                                                           branches with
                                                   | Some e_branch ->
                                                     (match match_payload_params
                                                              binders lts
                                                              args v0 with
                                                      | Infer_ok ps ->
                                                        if (&&)
                                                             ((&&)
                                                               (params_names_nodup_b
                                                                 ps)
                                                               (ctx_lookup_params_none_b
                                                                 ps _UU03a3_1))
                                                             (root_env_lookup_params_none_b
                                                               ps r1)
                                                        then let r_payload =
                                                               root_env_add_params_roots_same
                                                                 ps
                                                                 roots_scrut
                                                                 r1
                                                             in
                                                             (match infer_core_env_state_fuel_roots_shadow_safe
                                                                    fuel' env
                                                                    _UU03a9_
                                                                    n
                                                                    r_payload
                                                                    (sctx_add_params
                                                                    ps
                                                                    _UU03a3_1)
                                                                    e_branch with
                                                              | Infer_ok p2 ->
                                                                let (
                                                                  p3,
                                                                  roots_branch) =
                                                                  p2
                                                                in
                                                                let (
                                                                  p4,
                                                                  r_branch_payload) =
                                                                  p3
                                                                in
                                                                let (
                                                                  t_branch,
                                                                  _UU03a3__branch_payload) =
                                                                  p4
                                                                in
                                                                let r_branch =
                                                                  root_env_remove_match_params
                                                                    ps
                                                                    r_branch_payload
                                                                in
                                                                if contains_lbound_ty
                                                                    t_branch
                                                                then 
                                                                  Infer_err
                                                                    ErrLifetimeLeak
                                                                else 
                                                                  if 
                                                                    (&&)
                                                                    ((&&)
                                                                    (params_ok_sctx_b
                                                                    env ps
                                                                    _UU03a3__branch_payload)
                                                                    (roots_exclude_params_b
                                                                    ps
                                                                    roots_branch))
                                                                    (root_env_excludes_params_b
                                                                    ps
                                                                    r_branch)
                                                                  then 
                                                                    Infer_ok
                                                                    (((t_branch,
                                                                    (sctx_remove_params
                                                                    ps
                                                                    _UU03a3__branch_payload)),
                                                                    r_branch),
                                                                    roots_branch)
                                                                  else 
                                                                    Infer_err
                                                                    ErrContextCheckFailed
                                                              | Infer_err err ->
                                                                Infer_err err)
                                                        else Infer_err
                                                               ErrContextCheckFailed
                                                      | Infer_err err ->
                                                        Infer_err err)
                                                   | None ->
                                                     Infer_err
                                                       (ErrMissingVariant
                                                       v0.enum_variant_name))
                                                | None ->
                                                  Infer_err
                                                    (ErrMissingVariant
                                                    v0.enum_variant_name)
                                              in
                                              (match infer_branch v with
                                               | Infer_ok p2 ->
                                                 let (p3, roots_branch) = p2
                                                 in
                                                 let (p4, r_branch) = p3 in
                                                 let (t_branch,
                                                      _UU03a3__branch) =
                                                   p4
                                                 in
                                                 let infer_rest =
                                                   let rec infer_rest t_head r_out = function
                                                   | [] ->
                                                     Infer_ok (([], []), [])
                                                   | v0 :: rest0 ->
                                                     (match infer_branch v0 with
                                                      | Infer_ok p5 ->
                                                        let (p6, roots0) = p5
                                                        in
                                                        let (p7, r0) = p6 in
                                                        let (t0, _UU03a3_0) =
                                                          p7
                                                        in
                                                        if ty_core_eqb
                                                             (ty_core t0)
                                                             (ty_core t_head)
                                                        then let rest_ok =
                                                               let rest_result =
                                                                 infer_rest
                                                                   t_head
                                                                   r_out rest0
                                                               in
                                                               (match rest_result with
                                                                | Infer_ok p8 ->
                                                                  let (
                                                                    p9, rootss) =
                                                                    p8
                                                                  in
                                                                  let (
                                                                    _UU03a3_s,
                                                                    ts) = p9
                                                                  in
                                                                  Infer_ok
                                                                  (((_UU03a3_0 :: _UU03a3_s),
                                                                  (t0 :: ts)),
                                                                  (roots0 :: rootss))
                                                                | Infer_err err ->
                                                                  Infer_err
                                                                    err)
                                                             in
                                                             let context_error =
                                                               Infer_err
                                                               ErrContextCheckFailed
                                                             in
                                                             infer_if_bool
                                                               (root_env_eqb
                                                                 r0 r_out)
                                                               rest_ok
                                                               context_error
                                                        else Infer_err
                                                               (ErrTypeMismatch
                                                               ((ty_core t0),
                                                               (ty_core
                                                                 t_head)))
                                                      | Infer_err err ->
                                                        Infer_err err)
                                                   in infer_rest
                                                 in
                                                 (match infer_rest t_branch
                                                          r_branch rest with
                                                  | Infer_ok p5 ->
                                                    let (p6, rootss) = p5 in
                                                    let (_UU03a3_s, ts) = p6
                                                    in
                                                    Infer_ok ((((((t_branch,
                                                    _UU03a3__branch),
                                                    r_branch), roots_branch),
                                                    _UU03a3_s), ts), rootss)
                                                  | Infer_err err ->
                                                    Infer_err err)
                                               | Infer_err err ->
                                                 Infer_err err)
                                          in
                                          (match infer_first
                                                   edef.enum_variants with
                                           | Infer_ok p2 ->
                                             let (p3, roots_tail) = p2 in
                                             let (p4, ts_tail) = p3 in
                                             let (p5, _UU03a3__tail) = p4 in
                                             let (p6, roots_head) = p5 in
                                             let (p7, r_out) = p6 in
                                             let (t_head, _UU03a3__head) = p7
                                             in
                                             (match ctx_merge_many
                                                      (ctx_of_sctx
                                                        _UU03a3__head)
                                                      (map ctx_of_sctx
                                                        _UU03a3__tail) with
                                              | Some _UU0393__out ->
                                                Infer_ok ((((MkTy
                                                  ((usage_max_tys_nonempty
                                                     t_head ts_tail),
                                                  (ty_core t_head))),
                                                  (sctx_of_ctx _UU0393__out)),
                                                  r_out),
                                                  (root_sets_union
                                                    (roots_head :: roots_tail)))
                                              | None ->
                                                Infer_err
                                                  ErrContextCheckFailed)
                                           | Infer_err err -> Infer_err err)))))
             | None -> Infer_err (ErrEnumNotFound enum_name0))
          | x -> Infer_err (ErrNotAnEnum x))
       | Infer_err err -> Infer_err err)
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
                     then (match infer_core_env_state_fuel_roots_shadow_safe
                                   fuel' env _UU03a9_ n r _UU03a3_ e_new with
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
       | None ->
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_old ->
            if place_resolved_write_writable_chain_b env r _UU03a3_ p
            then (match place_resolved_write_target r p with
                  | Some x ->
                    (match root_env_lookup x r with
                     | Some roots_result ->
                       (match sctx_lookup_mut x _UU03a3_ with
                        | Some m ->
                          (match m with
                           | MImmutable -> Infer_err (ErrNotMutable x)
                           | MMutable ->
                             if writable_place_b env _UU03a3_ p
                             then (match infer_core_env_state_fuel_roots_shadow_safe
                                           fuel' env _UU03a9_ n r _UU03a3_
                                           e_new with
                                   | Infer_ok p0 ->
                                     let (p1, roots_new) = p0 in
                                     let (p2, r1) = p1 in
                                     let (t_new, _UU03a3_1) = p2 in
                                     (match root_env_lookup x r1 with
                                      | Some roots_old ->
                                        if ty_compatible_b _UU03a9_ t_new
                                             t_old
                                        then Infer_ok (((t_old, _UU03a3_1),
                                               (root_env_update x
                                                 (root_set_union roots_old
                                                   roots_new)
                                                 r1)),
                                               roots_result)
                                        else Infer_err
                                               (compatible_error t_new t_old)
                                      | None ->
                                        Infer_err ErrContextCheckFailed)
                                   | Infer_err err -> Infer_err err)
                             else Infer_err (ErrNotMutable x))
                        | None -> Infer_err (ErrUnknownVar x))
                     | None -> Infer_err ErrContextCheckFailed)
                  | None -> Infer_err ErrNotImplemented)
            else Infer_err ErrNotImplemented
          | Infer_err err -> Infer_err err))
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
                       then (match infer_core_env_state_fuel_roots_shadow_safe
                                     fuel' env _UU03a9_ n r _UU03a3_ e_new with
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
       | None ->
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_old ->
            if usage_eqb (ty_usage t_old) ULinear
            then Infer_err (ErrUsageMismatch ((ty_usage t_old), UAffine))
            else if place_resolved_write_writable_chain_b env r _UU03a3_ p
                 then (match place_resolved_write_target r p with
                       | Some x ->
                         (match sctx_lookup_mut x _UU03a3_ with
                          | Some m ->
                            (match m with
                             | MImmutable -> Infer_err (ErrNotMutable x)
                             | MMutable ->
                               if writable_place_b env _UU03a3_ p
                               then (match infer_core_env_state_fuel_roots_shadow_safe
                                             fuel' env _UU03a9_ n r _UU03a3_
                                             e_new with
                                     | Infer_ok p0 ->
                                       let (p1, roots_new) = p0 in
                                       let (p2, r1) = p1 in
                                       let (t_new, _UU03a3_1) = p2 in
                                       (match root_env_lookup x r1 with
                                        | Some roots_old ->
                                          if ty_compatible_b _UU03a9_ t_new
                                               t_old
                                          then Infer_ok ((((MkTy
                                                 (UUnrestricted, TUnits)),
                                                 _UU03a3_1),
                                                 (root_env_update x
                                                   (root_set_union roots_old
                                                     roots_new)
                                                   r1)),
                                                 [])
                                          else Infer_err
                                                 (compatible_error t_new
                                                   t_old)
                                        | None ->
                                          Infer_err ErrContextCheckFailed)
                                     | Infer_err err -> Infer_err err)
                               else Infer_err (ErrNotMutable x))
                          | None -> Infer_err (ErrUnknownVar x))
                       | None -> Infer_err ErrNotImplemented)
                 else Infer_err ErrNotImplemented
          | Infer_err err -> Infer_err err))
    | EBorrow (rk, p) ->
      (match infer_place_sctx env _UU03a3_ p with
       | Infer_ok t_p ->
         (match place_path p with
          | Some p0 ->
            let (x, _) = p0 in
            (match rk with
             | RShared ->
               Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n), RShared,
                 t_p)))), _UU03a3_), r), ((RStore x) :: []))
             | RUnique ->
               (match sctx_lookup_mut x _UU03a3_ with
                | Some m ->
                  (match m with
                   | MImmutable -> Infer_err (ErrImmutableBorrow x)
                   | MMutable ->
                     Infer_ok ((((MkTy (UAffine, (TRef ((LVar n), RUnique,
                       t_p)))), _UU03a3_), r), ((RStore x) :: [])))
                | None -> Infer_err (ErrUnknownVar x)))
          | None ->
            (match rk with
             | RShared ->
               (match place_resolved_roots r p with
                | Some roots ->
                  (match singleton_store_root roots with
                   | Some root_x ->
                     (match root_env_lookup root_x r with
                      | Some roots_x ->
                        (match singleton_store_root roots_x with
                         | Some root_y ->
                           if ident_eqb root_x root_y
                           then Infer_ok ((((MkTy (UUnrestricted, (TRef
                                  ((LVar n), RShared, t_p)))), _UU03a3_), r),
                                  roots)
                           else (match place_borrow_roots r p with
                                 | Some roots0 ->
                                   Infer_ok ((((MkTy (UUnrestricted, (TRef
                                     ((LVar n), RShared, t_p)))), _UU03a3_),
                                     r), roots0)
                                 | None -> Infer_err ErrContextCheckFailed)
                         | None ->
                           (match place_borrow_roots r p with
                            | Some roots0 ->
                              Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar
                                n), RShared, t_p)))), _UU03a3_), r), roots0)
                            | None -> Infer_err ErrContextCheckFailed))
                      | None ->
                        (match place_borrow_roots r p with
                         | Some roots0 ->
                           Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n),
                             RShared, t_p)))), _UU03a3_), r), roots0)
                         | None -> Infer_err ErrContextCheckFailed))
                   | None ->
                     (match place_borrow_roots r p with
                      | Some roots0 ->
                        Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n),
                          RShared, t_p)))), _UU03a3_), r), roots0)
                      | None -> Infer_err ErrContextCheckFailed))
                | None ->
                  (match place_borrow_roots r p with
                   | Some roots ->
                     Infer_ok ((((MkTy (UUnrestricted, (TRef ((LVar n),
                       RShared, t_p)))), _UU03a3_), r), roots)
                   | None -> Infer_err ErrContextCheckFailed))
             | RUnique ->
               if place_under_unique_ref_b env _UU03a3_ p
               then if place_resolved_write_writable_chain_b env r _UU03a3_ p
                    then (match place_resolved_write_target r p with
                          | Some x ->
                            let roots = (RStore x) :: [] in
                            Infer_ok ((((MkTy (UAffine, (TRef ((LVar n),
                            RUnique, t_p)))), _UU03a3_), r), roots)
                          | None ->
                            (match place_resolved_roots r p with
                             | Some roots ->
                               (match singleton_store_root roots with
                                | Some root_x ->
                                  (match root_env_lookup root_x r with
                                   | Some roots_x ->
                                     (match singleton_store_root roots_x with
                                      | Some root_y ->
                                        if ident_eqb root_x root_y
                                        then Infer_ok ((((MkTy (UAffine,
                                               (TRef ((LVar n), RUnique,
                                               t_p)))), _UU03a3_), r), roots)
                                        else (match place_borrow_roots r p with
                                              | Some roots0 ->
                                                Infer_ok ((((MkTy (UAffine,
                                                  (TRef ((LVar n), RUnique,
                                                  t_p)))), _UU03a3_), r),
                                                  roots0)
                                              | None ->
                                                Infer_err
                                                  ErrContextCheckFailed)
                                      | None ->
                                        (match place_borrow_roots r p with
                                         | Some roots0 ->
                                           Infer_ok ((((MkTy (UAffine, (TRef
                                             ((LVar n), RUnique, t_p)))),
                                             _UU03a3_), r), roots0)
                                         | None ->
                                           Infer_err ErrContextCheckFailed))
                                   | None ->
                                     (match place_borrow_roots r p with
                                      | Some roots0 ->
                                        Infer_ok ((((MkTy (UAffine, (TRef
                                          ((LVar n), RUnique, t_p)))),
                                          _UU03a3_), r), roots0)
                                      | None ->
                                        Infer_err ErrContextCheckFailed))
                                | None ->
                                  (match place_borrow_roots r p with
                                   | Some roots0 ->
                                     Infer_ok ((((MkTy (UAffine, (TRef ((LVar
                                       n), RUnique, t_p)))), _UU03a3_), r),
                                       roots0)
                                   | None -> Infer_err ErrContextCheckFailed))
                             | None ->
                               (match place_borrow_roots r p with
                                | Some roots ->
                                  Infer_ok ((((MkTy (UAffine, (TRef ((LVar
                                    n), RUnique, t_p)))), _UU03a3_), r),
                                    roots)
                                | None -> Infer_err ErrContextCheckFailed)))
                    else (match place_resolved_roots r p with
                          | Some roots ->
                            (match singleton_store_root roots with
                             | Some root_x ->
                               (match root_env_lookup root_x r with
                                | Some roots_x ->
                                  (match singleton_store_root roots_x with
                                   | Some root_y ->
                                     if ident_eqb root_x root_y
                                     then Infer_ok ((((MkTy (UAffine, (TRef
                                            ((LVar n), RUnique, t_p)))),
                                            _UU03a3_), r), roots)
                                     else (match place_borrow_roots r p with
                                           | Some roots0 ->
                                             Infer_ok ((((MkTy (UAffine,
                                               (TRef ((LVar n), RUnique,
                                               t_p)))), _UU03a3_), r), roots0)
                                           | None ->
                                             Infer_err ErrContextCheckFailed)
                                   | None ->
                                     (match place_borrow_roots r p with
                                      | Some roots0 ->
                                        Infer_ok ((((MkTy (UAffine, (TRef
                                          ((LVar n), RUnique, t_p)))),
                                          _UU03a3_), r), roots0)
                                      | None ->
                                        Infer_err ErrContextCheckFailed))
                                | None ->
                                  (match place_borrow_roots r p with
                                   | Some roots0 ->
                                     Infer_ok ((((MkTy (UAffine, (TRef ((LVar
                                       n), RUnique, t_p)))), _UU03a3_), r),
                                       roots0)
                                   | None -> Infer_err ErrContextCheckFailed))
                             | None ->
                               (match place_borrow_roots r p with
                                | Some roots0 ->
                                  Infer_ok ((((MkTy (UAffine, (TRef ((LVar
                                    n), RUnique, t_p)))), _UU03a3_), r),
                                    roots0)
                                | None -> Infer_err ErrContextCheckFailed))
                          | None ->
                            (match place_borrow_roots r p with
                             | Some roots ->
                               Infer_ok ((((MkTy (UAffine, (TRef ((LVar n),
                                 RUnique, t_p)))), _UU03a3_), r), roots)
                             | None -> Infer_err ErrContextCheckFailed))
               else Infer_err (ErrImmutableBorrow (place_name p))))
       | Infer_err err -> Infer_err err)
    | EDeref e0 ->
      (match e0 with
       | EBorrow (rk, p) ->
         (match infer_place_sctx env _UU03a3_ p with
          | Infer_ok t_p ->
            if usage_eqb (ty_usage t_p) UUnrestricted
            then (match place_path p with
                  | Some p0 ->
                    let (x, _) = p0 in
                    (match root_env_lookup x r with
                     | Some roots ->
                       (match rk with
                        | RShared -> Infer_ok (((t_p, _UU03a3_), r), roots)
                        | RUnique ->
                          (match sctx_lookup_mut x _UU03a3_ with
                           | Some m ->
                             (match m with
                              | MImmutable -> Infer_err (ErrImmutableBorrow x)
                              | MMutable ->
                                Infer_ok (((t_p, _UU03a3_), r), roots))
                           | None -> Infer_err (ErrUnknownVar x)))
                     | None -> Infer_err ErrContextCheckFailed)
                  | None ->
                    (match place_root_lookup r p with
                     | Some roots ->
                       (match rk with
                        | RShared -> Infer_ok (((t_p, _UU03a3_), r), roots)
                        | RUnique ->
                          if place_under_unique_ref_b env _UU03a3_ p
                          then Infer_ok (((t_p, _UU03a3_), r), roots)
                          else Infer_err (ErrImmutableBorrow (place_name p)))
                     | None -> Infer_err ErrContextCheckFailed))
            else Infer_err (ErrUsageMismatch ((ty_usage t_p), UUnrestricted))
          | Infer_err err -> Infer_err err)
       | _ -> Infer_err ErrNotImplemented)
    | EDrop e1 ->
      (match infer_core_env_state_fuel_roots_shadow_safe fuel' env _UU03a9_ n
               r _UU03a3_ e1 with
       | Infer_ok p ->
         let (p0, _) = p in
         let (p1, r') = p0 in
         let (_, _UU03a3_') = p1 in
         Infer_ok ((((MkTy (UUnrestricted, TUnits)), _UU03a3_'), r'), [])
       | Infer_err err -> Infer_err err)
    | EIf (e1, e2, e3) ->
      (match infer_core_env_state_fuel_roots_shadow_safe fuel' env _UU03a9_ n
               r _UU03a3_ e1 with
       | Infer_ok p ->
         let (p0, _) = p in
         let (p1, r1) = p0 in
         let (t_cond, _UU03a3_1) = p1 in
         if ty_core_eqb (ty_core t_cond) TBooleans
         then (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                       _UU03a9_ n r1 _UU03a3_1 e2 with
               | Infer_ok p2 ->
                 let (p3, roots2) = p2 in
                 let (p4, r2) = p3 in
                 let (t2, _UU03a3_2) = p4 in
                 (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                          _UU03a9_ n r1 _UU03a3_1 e3 with
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
       | Infer_err err -> Infer_err err))
    fuel

(** val infer_core_env_state_fuel_roots_shadow_safe_checked :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    root_env -> sctx -> expr -> (((ty * sctx) * root_env) * root_set)
    infer_result **)

let rec infer_core_env_state_fuel_roots_shadow_safe_checked fuel env _UU03a9_ n r _UU03a3_ e =
  match infer_core_env_state_fuel_roots_shadow_safe fuel env _UU03a9_ n r
          _UU03a3_ e with
  | Infer_ok p ->
    let (p0, roots) = p in
    let (p1, r') = p0 in
    let (t, _UU03a3_') = p1 in
    Infer_ok (((t, _UU03a3_'), r'), (roots_for_checked_result env t roots))
  | Infer_err err ->
    ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
       (fun _ -> Infer_err err)
       (fun fuel' ->
       match e with
       | ELet (m, x, t, e1, e2) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ e1 with
          | Infer_ok p ->
            let (p0, roots1) = p in
            let (p1, r1) = p0 in
            let (t1, _UU03a3_1) = p1 in
            if ty_compatible_b _UU03a9_ t1 t
            then (match root_env_lookup x r1 with
                  | Some _ -> Infer_err ErrContextCheckFailed
                  | None ->
                    if (&&) (roots_exclude_b x roots1)
                         (root_env_excludes_b x r1)
                    then (match infer_core_env_state_fuel_roots_shadow_safe_checked
                                  fuel' env _UU03a9_ n
                                  (root_env_add x roots1 r1)
                                  (sctx_add x t m _UU03a3_1) e2 with
                          | Infer_ok p2 ->
                            let (p3, roots2) = p2 in
                            let (p4, r2) = p3 in
                            let (t2, _UU03a3_2) = p4 in
                            if (&&)
                                 ((&&) (sctx_check_ok env x t _UU03a3_2)
                                   (capture_ref_free_ty_b env t2))
                                 (root_env_excludes_b x
                                   (root_env_remove x r2))
                            then Infer_ok (((t2, (sctx_remove x _UU03a3_2)),
                                   (root_env_remove x r2)),
                                   (roots_for_checked_result env t2 roots2))
                            else Infer_err ErrContextCheckFailed
                          | Infer_err err2 -> Infer_err err2)
                    else Infer_err ErrContextCheckFailed)
            else Infer_err (compatible_error t1 t)
          | Infer_err err1 -> Infer_err err1)
       | ELetInfer (m, x, e1, e2) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ e1 with
          | Infer_ok p ->
            let (p0, roots1) = p in
            let (p1, r1) = p0 in
            let (t1, _UU03a3_1) = p1 in
            (match root_env_lookup x r1 with
             | Some _ -> Infer_err ErrContextCheckFailed
             | None ->
               if (&&) (roots_exclude_b x roots1) (root_env_excludes_b x r1)
               then (match infer_core_env_state_fuel_roots_shadow_safe_checked
                             fuel' env _UU03a9_ n (root_env_add x roots1 r1)
                             (sctx_add x t1 m _UU03a3_1) e2 with
                     | Infer_ok p2 ->
                       let (p3, roots2) = p2 in
                       let (p4, r2) = p3 in
                       let (t2, _UU03a3_2) = p4 in
                       if (&&)
                            ((&&) (sctx_check_ok env x t1 _UU03a3_2)
                              (capture_ref_free_ty_b env t2))
                            (root_env_excludes_b x (root_env_remove x r2))
                       then Infer_ok (((t2, (sctx_remove x _UU03a3_2)),
                              (root_env_remove x r2)),
                              (roots_for_checked_result env t2 roots2))
                       else Infer_err ErrContextCheckFailed
                     | Infer_err err2 -> Infer_err err2)
               else Infer_err ErrContextCheckFailed)
          | Infer_err err1 -> Infer_err err1)
       | _ -> Infer_err err)
       fuel)

(** val infer_core_env_roots_shadow_safe :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx ->
    expr -> (((ty * ctx) * root_env) * root_set) infer_result **)

let infer_core_env_roots_shadow_safe env _UU03a9_ n r _UU0393_ e =
  match infer_core_env_state_fuel_roots_shadow_safe
          (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) env
          _UU03a9_ n r (sctx_of_ctx _UU0393_) e with
  | Infer_ok p ->
    let (p0, roots) = p in
    let (p1, r') = p0 in
    let (t, _UU03a3_) = p1 in
    Infer_ok (((t, (ctx_of_sctx _UU03a3_)), r'), roots)
  | Infer_err err -> Infer_err err

(** val infer_core_env_roots_shadow_safe_checked :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx ->
    expr -> (((ty * ctx) * root_env) * root_set) infer_result **)

let infer_core_env_roots_shadow_safe_checked env _UU03a9_ n r _UU0393_ e =
  match infer_core_env_state_fuel_roots_shadow_safe_checked
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

(** val check_fn_binding_params :
    region_ctx -> fn_def -> infer_error option **)

let check_fn_binding_params _UU0394_ f =
  if negb (wf_params_b _UU0394_ f.fn_captures)
  then Some ErrLifetimeLeak
  else if negb (wf_params_b _UU0394_ f.fn_params)
       then Some ErrLifetimeLeak
       else (match duplicate_param_name (fn_binding_params f) with
             | Some x -> Some (ErrDuplicateParam x)
             | None -> None)

(** val string_names_unique_b : string list -> bool **)

let rec string_names_unique_b = function
| [] -> true
| x :: xs' -> (&&) (negb (string_in x xs')) (string_names_unique_b xs')

(** val fn_name_strings : fn_def list -> string list **)

let fn_name_strings fns =
  map (fun f -> fst f.fn_name) fns

(** val enum_variant_names : enum_def -> string list **)

let enum_variant_names e =
  map (fun e0 -> e0.enum_variant_name) e.enum_variants

(** val top_level_names : global_env -> string list **)

let top_level_names env =
  app (map (fun s -> s.struct_name) env.env_structs)
    (app (map (fun e -> e.enum_name) env.env_enums)
      (app (map (fun t -> t.trait_name) env.env_traits)
        (fn_name_strings env.env_fns)))

(** val top_level_names_unique_b : global_env -> bool **)

let top_level_names_unique_b env =
  string_names_unique_b (top_level_names env)

(** val enum_variants_unique_b : enum_def -> bool **)

let enum_variants_unique_b e =
  string_names_unique_b (enum_variant_names e)

(** val enum_variant_names_unique_b : global_env -> bool **)

let enum_variant_names_unique_b env =
  forallb enum_variants_unique_b env.env_enums

(** val global_names_unique_b : global_env -> bool **)

let global_names_unique_b env =
  (&&) (top_level_names_unique_b env) (enum_variant_names_unique_b env)

(** val infer_env : global_env -> fn_def -> (ty * ctx) infer_result **)

let infer_env env f =
  let n = f.fn_lifetimes in
  let _UU03a9_ = f.fn_outlives in
  let _UU0394_ = mk_region_ctx n in
  let body_env = global_env_with_local_bounds env f.fn_bounds in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_type_b _UU0394_ f.fn_ret)
       then Infer_err ErrLifetimeLeak
       else (match check_fn_binding_params _UU0394_ f with
             | Some err -> Infer_err err
             | None ->
               (match infer_core_env body_env _UU03a9_ n (fn_body_ctx f)
                        f.fn_body with
                | Infer_ok p ->
                  let (t_body, _UU0393__out) = p in
                  if negb (wf_type_b _UU0394_ t_body)
                  then Infer_err ErrLifetimeLeak
                  else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                       then if params_ok_env_b env f.fn_params _UU0393__out
                            then Infer_ok (f.fn_ret, _UU0393__out)
                            else Infer_err ErrContextCheckFailed
                       else Infer_err (compatible_error t_body f.fn_ret)
                | Infer_err err -> Infer_err err))

(** val fn_with_body : fn_def -> expr -> fn_def **)

let fn_with_body f body =
  { fn_name = f.fn_name; fn_lifetimes = f.fn_lifetimes; fn_outlives =
    f.fn_outlives; fn_captures = f.fn_captures; fn_params = f.fn_params;
    fn_ret = f.fn_ret; fn_body = body; fn_type_params = f.fn_type_params;
    fn_bounds = f.fn_bounds }

(** val lookup_param_ty : ident -> param list -> ty option **)

let rec lookup_param_ty x = function
| [] -> None
| p :: ps' ->
  if ident_eqb x p.param_name then Some p.param_ty else lookup_param_ty x ps'

(** val mixed_forall_type_generic_fn_ty_b : ty -> bool **)

let mixed_forall_type_generic_fn_ty_b t =
  match ty_core t with
  | TForall (_, _, body) ->
    (match ty_core body with
     | TTypeForall (_, _, inner) ->
       (match ty_core inner with
        | TFn (_, _) -> true
        | _ -> false)
     | _ -> false)
  | _ -> false

(** val cleanup_mixed_param_call_expr : param list -> expr -> expr **)

let cleanup_mixed_param_call_expr ps e = match e with
| ECallExprGeneric (e0, _, args) ->
  (match e0 with
   | EVar x ->
     (match lookup_param_ty x ps with
      | Some t ->
        if mixed_forall_type_generic_fn_ty_b t
        then ECallExpr ((EVar x), args)
        else e
      | None -> e)
   | _ -> e)
| _ -> e

(** val infer_env_elab :
    global_env -> fn_def -> ((ty * ctx) * fn_def) infer_result **)

let infer_env_elab env f =
  let n = f.fn_lifetimes in
  let _UU03a9_ = f.fn_outlives in
  let _UU0394_ = mk_region_ctx n in
  let body_env = global_env_with_local_bounds env f.fn_bounds in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_type_b _UU0394_ f.fn_ret)
       then Infer_err ErrLifetimeLeak
       else (match check_fn_binding_params _UU0394_ f with
             | Some err -> Infer_err err
             | None ->
               (match infer_core_env_elab body_env _UU03a9_ n (fn_body_ctx f)
                        f.fn_body with
                | Infer_ok p ->
                  let (p0, body') = p in
                  let (t_body, _UU0393__out) = p0 in
                  if negb (wf_type_b _UU0394_ t_body)
                  then Infer_err ErrLifetimeLeak
                  else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                       then if params_ok_env_b env f.fn_params _UU0393__out
                            then Infer_ok ((f.fn_ret, _UU0393__out),
                                   (fn_with_body f
                                     (cleanup_mixed_param_call_expr
                                       f.fn_params body')))
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
  let body_env = global_env_with_local_bounds env f.fn_bounds in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_type_b _UU0394_ f.fn_ret)
       then Infer_err ErrLifetimeLeak
       else (match check_fn_binding_params _UU0394_ f with
             | Some err -> Infer_err err
             | None ->
               (match infer_core_env_roots body_env _UU03a9_ n r0
                        (fn_body_ctx f) f.fn_body with
                | Infer_ok p ->
                  let (p0, roots) = p in
                  let (p1, r_out) = p0 in
                  let (t_body, _UU0393__out) = p1 in
                  if negb (wf_type_b _UU0394_ t_body)
                  then Infer_err ErrLifetimeLeak
                  else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                       then if params_ok_env_b env f.fn_params _UU0393__out
                            then Infer_ok (((f.fn_ret, _UU0393__out), r_out),
                                   roots)
                            else Infer_err ErrContextCheckFailed
                       else Infer_err (compatible_error t_body f.fn_ret)
                | Infer_err err -> Infer_err err))

(** val infer_env_roots_shadow_safe :
    global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
    infer_result **)

let infer_env_roots_shadow_safe env f r0 =
  let n = f.fn_lifetimes in
  let _UU03a9_ = f.fn_outlives in
  let _UU0394_ = mk_region_ctx n in
  let body_env = global_env_with_local_bounds env f.fn_bounds in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_type_b _UU0394_ f.fn_ret)
       then Infer_err ErrLifetimeLeak
       else (match check_fn_binding_params _UU0394_ f with
             | Some err -> Infer_err err
             | None ->
               (match infer_core_env_roots_shadow_safe body_env _UU03a9_ n r0
                        (fn_body_ctx f) f.fn_body with
                | Infer_ok p ->
                  let (p0, roots) = p in
                  let (p1, r_out) = p0 in
                  let (t_body, _UU0393__out) = p1 in
                  if negb (wf_type_b _UU0394_ t_body)
                  then Infer_err ErrLifetimeLeak
                  else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                       then if params_ok_env_b env f.fn_params _UU0393__out
                            then Infer_ok (((f.fn_ret, _UU0393__out), r_out),
                                   roots)
                            else Infer_err ErrContextCheckFailed
                       else Infer_err (compatible_error t_body f.fn_ret)
                | Infer_err err -> Infer_err err))

(** val infer_env_roots_shadow_safe_checked :
    global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
    infer_result **)

let infer_env_roots_shadow_safe_checked env f r0 =
  let n = f.fn_lifetimes in
  let _UU03a9_ = f.fn_outlives in
  let _UU0394_ = mk_region_ctx n in
  let body_env = global_env_with_local_bounds env f.fn_bounds in
  if negb (wf_outlives_b _UU0394_ _UU03a9_)
  then Infer_err ErrLifetimeLeak
  else if negb (wf_type_b _UU0394_ f.fn_ret)
       then Infer_err ErrLifetimeLeak
       else (match check_fn_binding_params _UU0394_ f with
             | Some err -> Infer_err err
             | None ->
               (match infer_core_env_roots_shadow_safe_checked body_env
                        _UU03a9_ n r0 (fn_body_ctx f) f.fn_body with
                | Infer_ok p ->
                  let (p0, roots) = p in
                  let (p1, r_out) = p0 in
                  let (t_body, _UU0393__out) = p1 in
                  if negb (wf_type_b _UU0394_ t_body)
                  then Infer_err ErrLifetimeLeak
                  else if ty_compatible_b _UU03a9_ t_body f.fn_ret
                       then if params_ok_env_b env f.fn_params _UU0393__out
                            then Infer_ok (((f.fn_ret, _UU0393__out), r_out),
                                   roots)
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
| EMakeClosure (_, captures) ->
  let rec go = function
  | [] -> Infer_ok pBS
  | x :: rest ->
    if pbs_has_mut x [] pBS then Infer_err (ErrBorrowConflict x) else go rest
  in go captures
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
| ECallGeneric (_, _, args) ->
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
| ECallExprGeneric (callee, _, args) ->
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
| EEnum (_, _, _, _, _, payloads) ->
  let rec go pBS0 = function
  | [] -> Infer_ok pBS0
  | a :: rest ->
    (match borrow_check_env env pBS0 _UU0393_ a with
     | Infer_ok pBS1 -> go pBS1 rest
     | Infer_err err -> Infer_err err)
  in go pBS payloads
| EMatch (scrut, branches) ->
  (match borrow_check_env env pBS _UU0393_ scrut with
   | Infer_ok pBS1 ->
     let rec go expected = function
     | [] ->
       (match expected with
        | Some pBS_out -> Infer_ok pBS_out
        | None -> Infer_err (ErrMissingVariant ""))
     | p :: rest ->
       let (p0, e_branch) = p in
       let (_, binders) = p0 in
       let _UU0393__branch =
         ctx_add_params (unrestricted_unit_params_of_binders binders) _UU0393_
       in
       (match borrow_check_env env pBS1 _UU0393__branch e_branch with
        | Infer_ok pBS_branch ->
          (match expected with
           | Some pBS_expected ->
             if pbs_eqb pBS_branch pBS_expected
             then go expected rest
             else Infer_err ErrContextCheckFailed
           | None -> go (Some pBS_branch) rest)
        | Infer_err err -> Infer_err err)
     in go None branches
   | Infer_err err -> Infer_err err)
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
    (match borrow_check_env env [] (fn_body_ctx f) f.fn_body with
     | Infer_ok _ -> Infer_ok res
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val infer_full_env_elab :
    global_env -> fn_def -> ((ty * ctx) * fn_def) infer_result **)

let infer_full_env_elab env f =
  match infer_env_elab env f with
  | Infer_ok p ->
    let (p0, f') = p in
    (match borrow_check_env env [] (fn_body_ctx f') f'.fn_body with
     | Infer_ok _ -> Infer_ok (p0, f')
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val infer_full_env_roots :
    global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
    infer_result **)

let infer_full_env_roots env f r0 =
  match infer_env_roots env f r0 with
  | Infer_ok res ->
    (match borrow_check_env env [] (fn_body_ctx f) f.fn_body with
     | Infer_ok _ -> Infer_ok res
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val infer_full_env_roots_checked :
    global_env -> fn_def -> root_env -> (((ty * ctx) * root_env) * root_set)
    infer_result **)

let infer_full_env_roots_checked env f r0 =
  match infer_env_roots_shadow_safe_checked env f r0 with
  | Infer_ok res ->
    (match borrow_check_env env [] (fn_body_ctx f) f.fn_body with
     | Infer_ok _ -> Infer_ok res
     | Infer_err err -> Infer_err err)
  | Infer_err err -> Infer_err err

(** val alpha_normalize_global_env : global_env -> global_env **)

let alpha_normalize_global_env env =
  { env_structs = env.env_structs; env_enums = env.env_enums; env_traits =
    env.env_traits; env_impls = env.env_impls; env_local_bounds =
    env.env_local_bounds; env_fns = (alpha_rename_syntax env.env_fns) }

(** val expr_vars_match_params : expr list -> param list -> bool **)

let rec expr_vars_match_params args ps =
  match args with
  | [] -> (match ps with
           | [] -> true
           | _ :: _ -> false)
  | e :: args' ->
    (match e with
     | EVar x ->
       (match ps with
        | [] -> false
        | p :: ps' ->
          (&&) (ident_eqb x p.param_name) (expr_vars_match_params args' ps'))
     | _ -> false)

(** val specialize_simple_generic_wrapper_call :
    global_env -> ident -> ty list -> expr list -> ((ident * ty list) * expr
    list) option **)

let specialize_simple_generic_wrapper_call env fname type_args args =
  match lookup_fn_b fname env.env_fns with
  | Some fdef ->
    if (&&) (no_captures_b fdef)
         (Nat.eqb (length type_args) fdef.fn_type_params)
    then (match fdef.fn_body with
          | ECallGeneric (target, nested_type_args, wrapper_args) ->
            if expr_vars_match_params wrapper_args fdef.fn_params
            then Some ((target,
                   (map (subst_type_params_ty type_args) nested_type_args)),
                   args)
            else None
          | _ -> None)
    else None
  | None -> None

(** val specialize_simple_generic_wrapper_calls_top :
    global_env -> expr -> expr **)

let specialize_simple_generic_wrapper_calls_top env e = match e with
| ECallGeneric (fname, type_args, args) ->
  (match specialize_simple_generic_wrapper_call env fname type_args args with
   | Some p ->
     let (p0, target_args) = p in
     let (target, target_type_args) = p0 in
     ECallGeneric (target, target_type_args, target_args)
   | None -> e)
| _ -> e

(** val simplify_local_fn_value_result_let_top : expr -> expr **)

let simplify_local_fn_value_result_let_top e = match e with
| ELet (m, x, t, e0, e1) ->
  (match e0 with
   | EFn fname ->
     (match e1 with
      | ELet (_, result, _, e2, e3) ->
        (match e2 with
         | ECallExpr (e4, args) ->
           (match e4 with
            | EVar y ->
              (match e3 with
               | EVar result' ->
                 if (&&) ((&&) (ident_eqb x y) (ident_eqb result result'))
                      (usage_eqb (ty_usage t) UUnrestricted)
                 then ELet (m, x, t, (EFn fname), (ECallExpr ((EVar y),
                        args)))
                 else e
               | _ -> e)
            | _ -> e)
         | _ -> e)
      | _ -> e)
   | _ -> e)
| ELetInfer (m, x, e0, e1) ->
  (match e0 with
   | EFn fname ->
     (match e1 with
      | ELet (_, result, _, e2, e3) ->
        (match e2 with
         | ECallExpr (e4, args) ->
           (match e4 with
            | EVar y ->
              (match e3 with
               | EVar result' ->
                 if (&&) (ident_eqb x y) (ident_eqb result result')
                 then ELetInfer (m, x, (EFn fname), (ECallExpr ((EVar y),
                        args)))
                 else e
               | _ -> e)
            | _ -> e)
         | _ -> e)
      | _ -> e)
   | _ -> e)
| _ -> e

(** val specialize_simple_generic_wrapper_fn :
    global_env -> fn_def -> fn_def **)

let specialize_simple_generic_wrapper_fn env f =
  fn_with_body f
    (simplify_local_fn_value_result_let_top
      (specialize_simple_generic_wrapper_calls_top env f.fn_body))

(** val specialize_simple_generic_wrapper_fns :
    global_env -> fn_def list -> fn_def list **)

let rec specialize_simple_generic_wrapper_fns env = function
| [] -> []
| f :: rest ->
  (specialize_simple_generic_wrapper_fn env f) :: (specialize_simple_generic_wrapper_fns
                                                    env rest)

(** val infer_fns_env_elab :
    global_env -> fn_def list -> fn_def list infer_result **)

let rec infer_fns_env_elab env = function
| [] -> Infer_ok []
| f :: rest ->
  (match infer_full_env_elab env f with
   | Infer_ok p ->
     let (_, f') = p in
     (match infer_fns_env_elab env rest with
      | Infer_ok rest' -> Infer_ok (f' :: rest')
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)

(** val infer_program_env_alpha_elab :
    global_env -> global_env infer_result **)

let infer_program_env_alpha_elab env =
  let env_alpha = alpha_normalize_global_env env in
  (match infer_fns_env_elab env_alpha env_alpha.env_fns with
   | Infer_ok fns' ->
     let env_elab = { env_structs = env_alpha.env_structs; env_enums =
       env_alpha.env_enums; env_traits = env_alpha.env_traits; env_impls =
       env_alpha.env_impls; env_local_bounds = env_alpha.env_local_bounds;
       env_fns = fns' }
     in
     Infer_ok { env_structs = env_elab.env_structs; env_enums =
     env_elab.env_enums; env_traits = env_elab.env_traits; env_impls =
     env_elab.env_impls; env_local_bounds = env_elab.env_local_bounds;
     env_fns = (specialize_simple_generic_wrapper_fns env_elab fns') }
   | Infer_err err -> Infer_err err)

(** val fn_params_roots_exclude_b : param list -> root_set -> bool **)

let fn_params_roots_exclude_b ps roots =
  forallb (fun x -> roots_exclude_b x roots) (ctx_names (params_ctx ps))

(** val fn_params_root_env_excludes_b : param list -> root_env -> bool **)

let fn_params_root_env_excludes_b ps r =
  forallb (fun x -> root_env_excludes_b x r) (ctx_names (params_ctx ps))

(** val check_fn_root_shadow_summary : global_env -> fn_def -> bool **)

let check_fn_root_shadow_summary env fdef =
  (&&) (preservation_ready_expr_b fdef.fn_body)
    (match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
     | Infer_ok p ->
       let (p0, roots) = p in
       let (_, r_out) = p0 in
       (&&) (fn_params_roots_exclude_b fdef.fn_params roots)
         (fn_params_root_env_excludes_b fdef.fn_params r_out)
     | Infer_err _ -> false)

(** val check_env_root_shadow_summary : global_env -> bool **)

let check_env_root_shadow_summary env =
  forallb (check_fn_root_shadow_summary env) env.env_fns

(** val check_fn_root_shadow_provenance_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_provenance_summary env fdef =
  (&&) (provenance_ready_expr_b fdef.fn_body)
    (match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
     | Infer_ok p ->
       let (p0, roots) = p in
       let (_, r_out) = p0 in
       (&&) (fn_params_roots_exclude_b fdef.fn_params roots)
         (fn_params_root_env_excludes_b fdef.fn_params r_out)
     | Infer_err _ -> false)

(** val check_env_root_shadow_provenance_summary : global_env -> bool **)

let check_env_root_shadow_provenance_summary env =
  forallb (check_fn_root_shadow_provenance_summary env) env.env_fns

(** val store_safe_function_value_call_args_b :
    global_env -> expr list -> bool **)

let rec store_safe_function_value_call_args_b env = function
| [] -> true
| e :: rest ->
  (match e with
   | EUnit -> store_safe_function_value_call_args_b env rest
   | ELit _ -> store_safe_function_value_call_args_b env rest
   | EVar _ -> store_safe_function_value_call_args_b env rest
   | EFn fname ->
     (match lookup_fn_b fname env.env_fns with
      | Some callee ->
        (&&) (check_fn_root_shadow_provenance_summary env callee)
          (store_safe_function_value_call_args_b env rest)
      | None -> false)
   | _ -> false)

(** val direct_call_target_expr :
    expr -> ((ident * expr list) * expr) option **)

let direct_call_target_expr = function
| ECall (fname, args) -> Some ((fname, args), (ECall (fname, args)))
| ECallExpr (e0, args) ->
  (match e0 with
   | EFn fname -> Some ((fname, args), (ECall (fname, args)))
   | _ -> None)
| _ -> None

(** val generic_direct_call_target_expr :
    expr -> (((ident * ty list) * expr list) * expr) option **)

let generic_direct_call_target_expr = function
| ECallGeneric (fname, type_args, args) ->
  Some (((fname, type_args), args), (ECallGeneric (fname, type_args, args)))
| _ -> None

(** val let_bound_generic_direct_call_target_expr :
    expr -> ((((ident * ty list) * expr list) * ty) * expr) option **)

let let_bound_generic_direct_call_target_expr = function
| ELet (m, x, t_hidden, e0, e1) ->
  (match e0 with
   | ECallGeneric (fname, type_args, args) ->
     (match e1 with
      | EVar y ->
        if ident_eqb x y
        then Some ((((fname, type_args), args), t_hidden), (ELet (m, x,
               t_hidden, (ECallGeneric (fname, type_args, args)), (EVar y))))
        else None
      | _ -> None)
   | _ -> None)
| _ -> None

(** val if_literal_generic_direct_call_target_expr :
    expr -> (((((((bool * ident) * ty list) * expr list) * ident) * ty
    list) * expr list) * expr) option **)

let if_literal_generic_direct_call_target_expr = function
| EIf (e0, e1, e2) ->
  (match e0 with
   | ELit l ->
     (match l with
      | LBool b ->
        (match e1 with
         | ECallGeneric (fname_then, type_args_then, args_then) ->
           (match e2 with
            | ECallGeneric (fname_else, type_args_else, args_else) ->
              if (&&) (ident_eqb fname_then fname_else)
                   (ty_list_eqb type_args_then type_args_else)
              then (match args_then with
                    | [] ->
                      (match args_else with
                       | [] ->
                         Some (((((((b, fname_then), type_args_then),
                           args_then), fname_else), type_args_else),
                           args_else), (EIf ((ELit (LBool b)), (ECallGeneric
                           (fname_then, type_args_then, args_then)),
                           (ECallGeneric (fname_else, type_args_else,
                           args_else)))))
                       | _ :: _ -> None)
                    | _ :: _ -> None)
              else None
            | _ -> None)
         | _ -> None)
      | _ -> None)
   | _ -> None)
| _ -> None

(** val direct_call_ready_expr_b : expr -> bool **)

let direct_call_ready_expr_b e =
  match direct_call_target_expr e with
  | Some p ->
    let (p0, _) = p in let (_, args) = p0 in preservation_ready_args_b args
  | None -> false

(** val check_fn_root_shadow_direct_call_provenance_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_direct_call_provenance_summary env fdef =
  if check_fn_root_shadow_provenance_summary env fdef
  then true
  else (match direct_call_target_expr fdef.fn_body with
        | Some p ->
          let (p0, synthetic_body) = p in
          let (fname, args) = p0 in
          (&&) (preservation_ready_args_b args)
            (match lookup_fn_b fname env.env_fns with
             | Some callee ->
               (&&) (check_fn_root_shadow_provenance_summary env callee)
                 (match infer_env_roots_shadow_safe env
                          (fn_with_body fdef synthetic_body)
                          (initial_root_env_for_fn fdef) with
                  | Infer_ok p1 ->
                    let (p2, roots) = p1 in
                    let (_, r_out) = p2 in
                    (&&) (fn_params_roots_exclude_b fdef.fn_params roots)
                      (fn_params_root_env_excludes_b fdef.fn_params r_out)
                  | Infer_err _ -> false)
             | None -> false)
        | None -> false)

(** val local_fn_value_call_target_expr :
    expr -> ((ident * expr list) * expr) option **)

let local_fn_value_call_target_expr = function
| ELet (m, x, t, e0, e1) ->
  (match e0 with
   | EFn fname ->
     (match e1 with
      | ECallExpr (e2, args) ->
        (match e2 with
         | EVar y ->
           if (&&) (ident_eqb x y) (usage_eqb (ty_usage t) UUnrestricted)
           then Some ((fname, args), (ELet (m, x, t, (EFn fname), (ECall
                  (fname, args)))))
           else None
         | _ -> None)
      | _ -> None)
   | _ -> None)
| ELetInfer (m, x, e0, e1) ->
  (match e0 with
   | EFn fname ->
     (match e1 with
      | ECallExpr (e2, args) ->
        (match e2 with
         | EVar y ->
           if ident_eqb x y
           then Some ((fname, args), (ELetInfer (m, x, (EFn fname), (ECall
                  (fname, args)))))
           else None
         | _ -> None)
      | _ -> None)
   | _ -> None)
| _ -> None

(** val local_fn_value_call_target_expr_with_binder :
    expr -> (((ident * ident) * expr list) * expr) option **)

let local_fn_value_call_target_expr_with_binder = function
| ELet (m, x, t, e0, e1) ->
  (match e0 with
   | EFn fname ->
     (match e1 with
      | ECallExpr (e2, args) ->
        (match e2 with
         | EVar y ->
           if (&&) (ident_eqb x y) (usage_eqb (ty_usage t) UUnrestricted)
           then Some (((x, fname), args), (ELet (m, x, t, (EFn fname), (ECall
                  (fname, args)))))
           else None
         | _ -> None)
      | _ -> None)
   | _ -> None)
| ELetInfer (m, x, e0, e1) ->
  (match e0 with
   | EFn fname ->
     (match e1 with
      | ECallExpr (e2, args) ->
        (match e2 with
         | EVar y ->
           if ident_eqb x y
           then Some (((x, fname), args), (ELetInfer (m, x, (EFn fname),
                  (ECall (fname, args)))))
           else None
         | _ -> None)
      | _ -> None)
   | _ -> None)
| _ -> None

(** val supported_non_type_generic_function_value_call_callee_ty_b :
    ty -> bool **)

let supported_non_type_generic_function_value_call_callee_ty_b t =
  match ty_core t with
  | TFn (_, _) -> true
  | TForall (_, _, body) ->
    (match ty_core body with
     | TFn (_, _) -> true
     | _ -> false)
  | _ -> false

(** val type_arg_no_lifetime_forall_b : ty -> bool **)

let type_arg_no_lifetime_forall_b t =
  match ty_core t with
  | TForall (_, _, _) -> false
  | _ -> true

(** val type_args_no_lifetime_forall_b : ty list -> bool **)

let type_args_no_lifetime_forall_b type_args =
  forallb type_arg_no_lifetime_forall_b type_args

(** val type_args_lbound_free_b : ty list -> bool **)

let type_args_lbound_free_b type_args =
  forallb (fun t -> negb (contains_lbound_ty t)) type_args

(** val check_supported_non_type_generic_function_value_call_expr :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx ->
    expr -> bool **)

let check_supported_non_type_generic_function_value_call_expr env _UU03a9_ n r _UU0393_ callee = match callee with
| EVar _ ->
  (match infer_core_env_roots_shadow_safe env _UU03a9_ n r _UU0393_ callee with
   | Infer_ok p ->
     let (p0, _) = p in
     let (p1, _) = p0 in
     let (t_callee, _) = p1 in
     supported_non_type_generic_function_value_call_callee_ty_b t_callee
   | Infer_err _ -> false)
| _ -> false

(** val check_supported_type_generic_function_value_call_expr :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx ->
    expr -> ty list -> bool **)

let check_supported_type_generic_function_value_call_expr env _UU03a9_ n r _UU0393_ callee type_args =
  (&&)
    ((&&) (type_args_lbound_free_b type_args)
      (type_args_no_lifetime_forall_b type_args))
    (match callee with
     | EVar _ ->
       (match infer_core_env_roots_shadow_safe env _UU03a9_ n r _UU0393_
                callee with
        | Infer_ok p ->
          let (p0, _) = p in
          let (p1, _) = p0 in
          let (t_callee, _) = p1 in
          (match ty_core t_callee with
           | TTypeForall (type_params, bounds, body) ->
             (&&) (Nat.eqb (length type_args) type_params)
               (match bounds with
                | [] ->
                  (match ty_core body with
                   | TFn (_, _) -> true
                   | _ -> false)
                | _ :: _ -> false)
           | _ -> false)
        | Infer_err _ -> false)
     | _ -> false)

(** val check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel :
    (Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    root_env -> sctx -> expr -> bool) -> Big_int_Z.big_int -> global_env ->
    fn_def -> ty list -> bool **)

let check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel check_expr fuel env fdef type_args =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> false)
    (fun fuel' ->
    let body_ctx = subst_type_params_ctx type_args (fn_body_ctx fdef) in
    let body = subst_type_params_expr type_args fdef.fn_body in
    let params = apply_type_params type_args fdef.fn_params in
    let body_env =
      global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args fdef.fn_bounds)
    in
    (match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
     | Infer_ok _ ->
       (match infer_core_env_state_fuel_roots_shadow_safe fuel' body_env
                fdef.fn_outlives fdef.fn_lifetimes
                (initial_root_env_for_fn fdef) (sctx_of_ctx body_ctx) body with
        | Infer_ok p ->
          let (p0, roots_body) = p in
          let (p1, r_body) = p0 in
          let (t_body, _) = p1 in
          (&&)
            ((&&)
              ((&&)
                (check_expr fuel' body_env fdef.fn_outlives fdef.fn_lifetimes
                  (initial_root_env_for_fn fdef) (sctx_of_ctx body_ctx) body)
                (ty_compatible_b fdef.fn_outlives t_body
                  (subst_type_params_ty type_args fdef.fn_ret)))
              (fn_params_roots_exclude_b params roots_body))
            (fn_params_root_env_excludes_b params r_body)
        | Infer_err _ -> false)
     | Infer_err _ -> false))
    fuel

(** val check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel :
    (Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    root_env -> sctx -> expr -> bool) -> Big_int_Z.big_int -> global_env ->
    ty list -> bool **)

let check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel check_expr fuel env type_args =
  forallb (fun fdef ->
    if Nat.eqb (length type_args) fdef.fn_type_params
    then check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
           check_expr fuel env fdef type_args
    else true) env.env_fns

(** val check_fn_root_shadow_non_capturing_call_provenance_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_non_capturing_call_provenance_summary env fdef =
  if check_fn_root_shadow_direct_call_provenance_summary env fdef
  then true
  else (match local_fn_value_call_target_expr fdef.fn_body with
        | Some p ->
          let (p0, synthetic_body) = p in
          let (fname, args) = p0 in
          (&&) (preservation_ready_args_b args)
            (match lookup_fn_b fname env.env_fns with
             | Some callee ->
               (&&) (check_fn_root_shadow_provenance_summary env callee)
                 (match infer_env_roots_shadow_safe env
                          (fn_with_body fdef synthetic_body)
                          (initial_root_env_for_fn fdef) with
                  | Infer_ok p1 ->
                    let (p2, roots) = p1 in
                    let (_, r_out) = p2 in
                    (&&) (fn_params_roots_exclude_b fdef.fn_params roots)
                      (fn_params_root_env_excludes_b fdef.fn_params r_out)
                  | Infer_err _ -> false)
             | None -> false)
        | None ->
          (match fdef.fn_body with
           | ECallExpr (callee, args) ->
             (&&)
               ((&&)
                 ((&&) (preservation_ready_expr_b callee)
                   (preservation_ready_args_b args))
                 (check_supported_non_type_generic_function_value_call_expr
                   (global_env_with_local_bounds env fdef.fn_bounds)
                   fdef.fn_outlives fdef.fn_lifetimes
                   (initial_root_env_for_fn fdef) (fn_body_ctx fdef) callee))
               (match infer_env_roots_shadow_safe env fdef
                        (initial_root_env_for_fn fdef) with
                | Infer_ok p ->
                  let (p0, roots) = p in
                  let (_, r_out) = p0 in
                  (&&) (fn_params_roots_exclude_b fdef.fn_params roots)
                    (fn_params_root_env_excludes_b fdef.fn_params r_out)
                | Infer_err _ -> false)
           | _ -> false))

(** val captured_call_target_expr :
    expr -> ((ident * ident list) * expr list) option **)

let captured_call_target_expr = function
| ECallExpr (e0, args) ->
  (match e0 with
   | EMakeClosure (fname, captures) -> Some ((fname, captures), args)
   | _ -> None)
| _ -> None

(** val args_free_vars_checker : expr list -> ident list **)

let args_free_vars_checker args =
  args_local_store_names_with free_vars_expr args

(** val local_captured_call_target_expr :
    expr -> (((((((ident * ident list) * expr
    list) * mutability) * ident) * ty) * expr) * expr) option **)

let local_captured_call_target_expr = function
| ELet (m, x, t, e0, e1) ->
  (match e0 with
   | EMakeClosure (fname, captures) ->
     (match e1 with
      | ECallExpr (e2, args) ->
        (match e2 with
         | EVar y ->
           if (&&)
                ((&&)
                  ((&&)
                    ((&&) (ident_eqb x y)
                      (usage_eqb (ty_usage t) UUnrestricted))
                    (negb (existsb (ident_eqb x) captures)))
                  (negb (existsb (ident_eqb x) (args_free_vars_checker args))))
                (negb (existsb (ident_eqb x) (args_local_store_names args)))
           then let direct_body = ECallExpr ((EMakeClosure (fname,
                  captures)), args)
                in
                Some (((((((fname, captures), args), m), x), t),
                direct_body), (ELet (m, x, t, (EMakeClosure (fname,
                captures)), direct_body)))
           else None
         | _ -> None)
      | _ -> None)
   | _ -> None)
| _ -> None

(** val check_fn_root_shadow_captured_callee_provenance_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_captured_callee_provenance_summary env fdef =
  (&&) (provenance_ready_expr_b fdef.fn_body)
    (match infer_env_roots_shadow_safe env fdef
             (initial_root_env_for_params
               (app fdef.fn_params fdef.fn_captures)) with
     | Infer_ok p ->
       let (p0, roots) = p in
       let (_, r_out) = p0 in
       (&&)
         (fn_params_roots_exclude_b (app fdef.fn_params fdef.fn_captures)
           roots)
         (fn_params_root_env_excludes_b (app fdef.fn_params fdef.fn_captures)
           r_out)
     | Infer_err _ -> false)

(** val capture_root_bound :
    root_env -> ident list -> param list -> root_set option **)

let rec capture_root_bound r captures caps =
  match captures with
  | [] -> (match caps with
           | [] -> Some []
           | _ :: _ -> None)
  | x :: captures' ->
    (match caps with
     | [] -> None
     | _ :: caps' ->
       (match root_env_lookup x r with
        | Some roots ->
          (match capture_root_bound r captures' caps' with
           | Some rest -> Some (root_set_union roots rest)
           | None -> None)
        | None -> None))

(** val callee_hidden_capture_args_disjoint_b :
    fn_def -> expr list -> bool **)

let callee_hidden_capture_args_disjoint_b callee args =
  forallb (fun x ->
    negb (existsb (ident_eqb x) (args_local_store_names args)))
    (ctx_names (params_ctx callee.fn_captures))

(** val check_expr_root_shadow_captured_call_provenance_summary_fuel :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    root_env -> sctx -> expr -> bool **)

let rec check_expr_root_shadow_captured_call_provenance_summary_fuel fuel env _UU03a9_ n r _UU03a3_ e =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> false)
    (fun fuel' ->
    match infer_core_env_state_fuel_roots_shadow_safe fuel env _UU03a9_ n r
            _UU03a3_ e with
    | Infer_ok _ ->
      (||)
        ((||)
          ((||)
            ((||)
              ((||) (provenance_ready_expr_b e)
                (match direct_call_target_expr e with
                 | Some p ->
                   let (p0, synthetic_body) = p in
                   let (fname, args) = p0 in
                   (&&) (preservation_ready_args_b args)
                     (match lookup_fn_b fname env.env_fns with
                      | Some callee ->
                        (&&)
                          (check_fn_root_shadow_provenance_summary env callee)
                          (match infer_core_env_state_fuel_roots_shadow_safe
                                   fuel env _UU03a9_ n r _UU03a3_
                                   synthetic_body with
                           | Infer_ok _ -> true
                           | Infer_err _ -> false)
                      | None -> false)
                 | None -> false))
              (match captured_call_target_expr e with
               | Some p ->
                 let (p0, args) = p in
                 let (fname, captures) = p0 in
                 (&&) (preservation_ready_args_b args)
                   (match lookup_fn_b fname env.env_fns with
                    | Some callee ->
                      (&&)
                        (callee_hidden_capture_args_disjoint_b callee args)
                        (match check_make_closure_captures_exact_sctx_with_env
                                 env _UU03a9_ _UU03a3_ captures
                                 callee.fn_captures with
                         | Infer_ok _ ->
                           (match capture_root_bound r captures
                                    callee.fn_captures with
                            | Some _ ->
                              check_fn_root_shadow_captured_callee_provenance_summary
                                env callee
                            | None -> false)
                         | Infer_err _ -> false)
                    | None -> false)
               | None -> false))
            (match local_captured_call_target_expr e with
             | Some p ->
               let (p0, _) = p in
               let (p1, direct_body) = p0 in
               let (p2, _) = p1 in
               let (p3, x) = p2 in
               let (p4, _) = p3 in
               let (p5, args) = p4 in
               let (fname, captures) = p5 in
               (&&) (preservation_ready_args_b args)
                 (match lookup_fn_b fname env.env_fns with
                  | Some callee ->
                    (&&)
                      ((&&)
                        (callee_hidden_capture_args_disjoint_b callee args)
                        (negb
                          (existsb (ident_eqb x)
                            (ctx_names (params_ctx callee.fn_captures)))))
                      (match root_env_lookup x r with
                       | Some _ -> false
                       | None ->
                         (match check_make_closure_captures_exact_sctx_with_env
                                  env _UU03a9_ _UU03a3_ captures
                                  callee.fn_captures with
                          | Infer_ok _ ->
                            (match capture_root_bound r captures
                                     callee.fn_captures with
                             | Some _ ->
                               (&&)
                                 (check_fn_root_shadow_captured_callee_provenance_summary
                                   env callee)
                                 (match infer_core_env_state_fuel_roots_shadow_safe
                                          fuel env _UU03a9_ n r _UU03a3_
                                          direct_body with
                                  | Infer_ok p6 ->
                                    let (p7, _) = p6 in
                                    let (p8, r_direct) = p7 in
                                    let (t_direct, _UU03a3__direct) = p8 in
                                    (match infer_core_env_state_fuel_roots_shadow_safe
                                             fuel env _UU03a9_ n r _UU03a3_ e with
                                     | Infer_ok p9 ->
                                       let (p10, _) = p9 in
                                       let (p11, r_let) = p10 in
                                       let (t_let, _UU03a3__let) = p11 in
                                       (&&)
                                         ((&&)
                                           (sctx_eqb _UU03a3__direct
                                             _UU03a3__let)
                                           (root_env_eqb r_direct r_let))
                                         (ty_compatible_b _UU03a9_ t_direct
                                           t_let)
                                     | Infer_err _ -> false)
                                  | Infer_err _ -> false)
                             | None -> false)
                          | Infer_err _ -> false))
                  | None -> false)
             | None -> false))
          (match e with
           | ELet (m, x, t_hidden, e1, e2) ->
             (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                      _UU03a9_ n r _UU03a3_ e1 with
              | Infer_ok p ->
                let (p0, roots1) = p in
                let (p1, r1) = p0 in
                let (t1, _UU03a3_1) = p1 in
                (&&)
                  ((&&) (ty_compatible_b _UU03a9_ t1 t_hidden)
                    (provenance_ready_expr_b e1))
                  (match root_env_lookup x r1 with
                   | Some _ -> false
                   | None ->
                     (&&)
                       ((&&) (roots_exclude_b x roots1)
                         (root_env_excludes_b x r1))
                       (match infer_core_env_state_fuel_roots_shadow_safe
                                fuel' env _UU03a9_ n
                                (root_env_add x roots1 r1)
                                (sctx_add x t_hidden m _UU03a3_1) e2 with
                        | Infer_ok p2 ->
                          let (p3, roots2) = p2 in
                          let (p4, r2) = p3 in
                          let (t2, _UU03a3_2) = p4 in
                          (&&)
                            ((&&)
                              ((&&)
                                ((&&) (capture_ref_free_ty_b env t2)
                                  (sctx_check_ok env x t_hidden _UU03a3_2))
                                (roots_exclude_b x roots2))
                              (root_env_excludes_b x (root_env_remove x r2)))
                            (check_expr_root_shadow_captured_call_provenance_summary_fuel
                              fuel' env _UU03a9_ n (root_env_add x roots1 r1)
                              (sctx_add x t_hidden m _UU03a3_1) e2)
                        | Infer_err _ -> false))
              | Infer_err _ -> false)
           | _ -> false))
        (match e with
         | EIf (e1, e2, e3) ->
           (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                    _UU03a9_ n r _UU03a3_ e1 with
            | Infer_ok p ->
              let (p0, _) = p in
              let (p1, r1) = p0 in
              let (t_cond, _UU03a3_1) = p1 in
              (&&)
                ((&&)
                  ((&&) (ty_core_eqb (ty_core t_cond) TBooleans)
                    (provenance_ready_expr_b e1))
                  (check_expr_root_shadow_captured_call_provenance_summary_fuel
                    fuel' env _UU03a9_ n r1 _UU03a3_1 e2))
                (check_expr_root_shadow_captured_call_provenance_summary_fuel
                  fuel' env _UU03a9_ n r1 _UU03a3_1 e3)
            | Infer_err _ -> false)
         | _ -> false)
    | Infer_err _ -> false)
    fuel

(** val check_expr_root_shadow_captured_call_provenance_summary :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx ->
    expr -> bool **)

let check_expr_root_shadow_captured_call_provenance_summary env _UU03a9_ n r _UU0393_ e =
  check_expr_root_shadow_captured_call_provenance_summary_fuel
    (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) env _UU03a9_ n r
    (sctx_of_ctx _UU0393_) e

(** val non_function_value_ty_b : ty -> bool **)

let rec non_function_value_ty_b = function
| MkTy (_, t0) ->
  (match t0 with
   | TFn (_, _) -> false
   | TClosure (_, _, _) -> false
   | TForall (_, _, body) -> non_function_value_ty_b body
   | TTypeForall (_, _, body) -> non_function_value_ty_b body
   | _ -> true)

(** val check_expr_root_shadow_store_safe_narrow_summary_fuel :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    root_env -> sctx -> expr -> bool **)

let rec check_expr_root_shadow_store_safe_narrow_summary_fuel fuel env _UU03a9_ n r _UU03a3_ e =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> false)
    (fun fuel' ->
    match infer_core_env_state_fuel_roots_shadow_safe fuel env _UU03a9_ n r
            _UU03a3_ e with
    | Infer_ok p ->
      let (p0, roots) = p in
      let (p1, _) = p0 in
      let (t, _) = p1 in
      (match e with
       | EUnit -> true
       | EVar _ -> non_function_value_ty_b t
       | ELet (m, x, t_hidden, e1, e2) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ e1 with
          | Infer_ok p2 ->
            let (p3, roots1) = p2 in
            let (p4, r1) = p3 in
            let (t1, _UU03a3_1) = p4 in
            (&&)
              ((&&)
                ((&&) (ty_compatible_b _UU03a9_ t1 t_hidden)
                  (non_function_value_ty_b t_hidden))
                (check_expr_root_shadow_store_safe_narrow_summary_fuel fuel'
                  env _UU03a9_ n r _UU03a3_ e1))
              (match root_env_lookup x r1 with
               | Some _ -> false
               | None ->
                 (&&)
                   ((&&) (roots_exclude_b x roots1)
                     (root_env_excludes_b x r1))
                   (match infer_core_env_state_fuel_roots_shadow_safe fuel'
                            env _UU03a9_ n (root_env_add x roots1 r1)
                            (sctx_add x t_hidden m _UU03a3_1) e2 with
                    | Infer_ok p5 ->
                      let (p6, roots2) = p5 in
                      let (p7, r2) = p6 in
                      let (_, _UU03a3_2) = p7 in
                      (&&)
                        ((&&)
                          ((&&) (sctx_check_ok env x t_hidden _UU03a3_2)
                            (roots_exclude_b x roots2))
                          (root_env_excludes_b x (root_env_remove x r2)))
                        (check_expr_root_shadow_store_safe_narrow_summary_fuel
                          fuel' env _UU03a9_ n (root_env_add x roots1 r1)
                          (sctx_add x t_hidden m _UU03a3_1) e2)
                    | Infer_err _ -> false))
          | Infer_err _ -> false)
       | ELetInfer (m, x, e1, e2) ->
         (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                  _UU03a9_ n r _UU03a3_ e1 with
          | Infer_ok p2 ->
            let (p3, roots1) = p2 in
            let (p4, r1) = p3 in
            let (t1, _UU03a3_1) = p4 in
            (&&)
              ((&&) (non_function_value_ty_b t1)
                (check_expr_root_shadow_store_safe_narrow_summary_fuel fuel'
                  env _UU03a9_ n r _UU03a3_ e1))
              (match root_env_lookup x r1 with
               | Some _ -> false
               | None ->
                 (&&)
                   ((&&) (roots_exclude_b x roots1)
                     (root_env_excludes_b x r1))
                   (match infer_core_env_state_fuel_roots_shadow_safe fuel'
                            env _UU03a9_ n (root_env_add x roots1 r1)
                            (sctx_add x t1 m _UU03a3_1) e2 with
                    | Infer_ok p5 ->
                      let (p6, roots2) = p5 in
                      let (p7, r2) = p6 in
                      let (_, _UU03a3_2) = p7 in
                      (&&)
                        ((&&)
                          ((&&) (sctx_check_ok env x t1 _UU03a3_2)
                            (roots_exclude_b x roots2))
                          (root_env_excludes_b x (root_env_remove x r2)))
                        (check_expr_root_shadow_store_safe_narrow_summary_fuel
                          fuel' env _UU03a9_ n (root_env_add x roots1 r1)
                          (sctx_add x t1 m _UU03a3_1) e2)
                    | Infer_err _ -> false))
          | Infer_err _ -> false)
       | ECallExpr (callee, args) ->
         (&&) (store_safe_function_value_call_args_b env args)
           (check_supported_non_type_generic_function_value_call_expr env
             _UU03a9_ n r (ctx_of_sctx _UU03a3_) callee)
       | ECallExprGeneric (callee, type_args, args) ->
         (&&)
           ((&&) (store_safe_function_value_call_args_b env args)
             (check_supported_type_generic_function_value_call_expr env
               _UU03a9_ n r (ctx_of_sctx _UU03a3_) callee type_args))
           (check_all_callee_bodies_root_shadow_store_safe_narrow_summary_instantiated_fuel
             check_expr_root_shadow_store_safe_narrow_summary_fuel
             (Big_int_Z.succ_big_int fuel') env type_args)
       | EStruct (name, _, _, l1) ->
         (match l1 with
          | [] ->
            (match lookup_struct name env with
             | Some sdef ->
               (match sdef.struct_bounds with
                | [] -> capture_ref_free_ty_b env t
                | _ :: _ -> false)
             | None -> false)
          | _ :: _ -> false)
       | EAssign (p2, e0) ->
         (match p2 with
          | PVar x ->
            (match e0 with
             | ELit _ -> true
             | ECallGeneric (fname, type_args, l) ->
               (match l with
                | [] ->
                  (match lookup_fn_b fname env.env_fns with
                   | Some callee ->
                     (match callee.fn_bounds with
                      | [] ->
                        (match callee.fn_params with
                         | [] ->
                           (&&)
                             (Nat.eqb (length type_args)
                               callee.fn_type_params)
                             (let body_ctx =
                                subst_type_params_ctx type_args
                                  (fn_body_ctx callee)
                              in
                              let body =
                                subst_type_params_expr type_args
                                  callee.fn_body
                              in
                              (match body_ctx with
                               | [] ->
                                 (match body with
                                  | EStruct (_, _, _, l1) ->
                                    (match l1 with
                                     | [] ->
                                       let params =
                                         apply_type_params type_args
                                           callee.fn_params
                                       in
                                       (match infer_core_env_state_fuel_roots_shadow_safe
                                                fuel' env callee.fn_outlives
                                                callee.fn_lifetimes
                                                (initial_root_env_for_fn
                                                  callee)
                                                (sctx_of_ctx body_ctx) body with
                                        | Infer_ok p3 ->
                                          let (p4, roots_body) = p3 in
                                          let (p5, r_body) = p4 in
                                          let (t_body, _) = p5 in
                                          (match infer_env_roots_shadow_safe
                                                   env callee
                                                   (initial_root_env_for_fn
                                                     callee) with
                                           | Infer_ok _ ->
                                             (match infer_core_env_state_fuel_roots_shadow_safe
                                                      fuel' env _UU03a9_ n r
                                                      _UU03a3_ (ECallGeneric
                                                      (fname, type_args, [])) with
                                              | Infer_ok p6 ->
                                                let (p7, _) = p6 in
                                                let (p8, _) = p7 in
                                                let (t_rhs, _) = p8 in
                                                (match infer_place_sctx env
                                                         _UU03a3_ (PVar x) with
                                                 | Infer_ok t_old ->
                                                   (&&)
                                                     ((&&)
                                                       ((&&)
                                                         ((&&)
                                                           (check_expr_root_shadow_store_safe_narrow_summary_fuel
                                                             fuel' env
                                                             callee.fn_outlives
                                                             callee.fn_lifetimes
                                                             (initial_root_env_for_fn
                                                               callee)
                                                             (sctx_of_ctx
                                                               body_ctx)
                                                             body)
                                                           (ty_compatible_b
                                                             callee.fn_outlives
                                                             t_body
                                                             (subst_type_params_ty
                                                               type_args
                                                               callee.fn_ret)))
                                                         (fn_params_roots_exclude_b
                                                           params roots_body))
                                                       (fn_params_root_env_excludes_b
                                                         params r_body))
                                                     (ty_compatible_b
                                                       _UU03a9_ t_rhs t_old)
                                                 | Infer_err _ -> false)
                                              | Infer_err _ -> false)
                                           | Infer_err _ -> false)
                                        | Infer_err _ -> false)
                                     | _ :: _ -> false)
                                  | _ -> false)
                               | _ :: _ -> false))
                         | _ :: _ -> false)
                      | _ :: _ -> false)
                   | None -> false)
                | _ :: _ -> false)
             | _ -> false)
          | _ -> (match e0 with
                  | ELit _ -> true
                  | _ -> false))
       | EBorrow (rk, p2) ->
         (match place_path p2 with
          | Some _ -> true
          | None ->
            (match rk with
             | RShared -> false
             | RUnique ->
               (&&) (place_resolved_write_writable_chain_b env r _UU03a3_ p2)
                 (match place_resolved_write_target r p2 with
                  | Some root_x ->
                    (match singleton_store_root roots with
                     | Some root_y -> ident_eqb root_x root_y
                     | None -> false)
                  | None -> false)))
       | EDrop e0 ->
         (match e0 with
          | EPlace p2 ->
            (match place_path p2 with
             | Some _ -> true
             | None -> false)
          | _ -> false)
       | _ -> false)
    | Infer_err _ -> false)
    fuel

(** val check_expr_root_shadow_store_safe_narrow_summary :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx ->
    expr -> bool **)

let check_expr_root_shadow_store_safe_narrow_summary env _UU03a9_ n r _UU0393_ e =
  check_expr_root_shadow_store_safe_narrow_summary_fuel
    (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) env _UU03a9_ n r
    (sctx_of_ctx _UU0393_) e

(** val check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel :
    Big_int_Z.big_int -> global_env -> fn_def -> ty list -> bool **)

let rec check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel fuel env fdef type_args =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> false)
    (fun fuel' ->
    let body_ctx = subst_type_params_ctx type_args (fn_body_ctx fdef) in
    let body = subst_type_params_expr type_args fdef.fn_body in
    let params = apply_type_params type_args fdef.fn_params in
    let body_env =
      global_env_with_local_bounds env
        (subst_type_params_trait_bounds type_args fdef.fn_bounds)
    in
    (match infer_env_roots_shadow_safe env fdef (initial_root_env_for_fn fdef) with
     | Infer_ok _ ->
       (||)
         (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_body_fuel
           check_expr_root_shadow_store_safe_narrow_summary_fuel
           (Big_int_Z.succ_big_int fuel') env fdef type_args)
         (match generic_direct_call_target_expr body with
          | Some p ->
            let (p0, synthetic_body) = p in
            let (p1, args) = p0 in
            let (fname, nested_type_args) = p1 in
            (&&) (store_safe_function_value_call_args_b env args)
              (match lookup_fn_b fname env.env_fns with
               | Some fcallee ->
                 (&&)
                   (Nat.eqb (length nested_type_args) fcallee.fn_type_params)
                   (match check_struct_bounds body_env fcallee.fn_bounds
                            nested_type_args with
                    | Some _ -> false
                    | None ->
                      (match infer_core_env_roots_shadow_safe body_env
                               fdef.fn_outlives fdef.fn_lifetimes
                               (initial_root_env_for_fn fdef) body_ctx
                               synthetic_body with
                       | Infer_ok p2 ->
                         let (p3, roots_synth) = p2 in
                         let (p4, r_synth) = p3 in
                         let (t_synth, _) = p4 in
                         (&&)
                           ((&&)
                             ((&&)
                               (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
                                 fuel' env fcallee nested_type_args)
                               (ty_compatible_b fdef.fn_outlives t_synth
                                 (subst_type_params_ty type_args fdef.fn_ret)))
                             (fn_params_roots_exclude_b params roots_synth))
                           (fn_params_root_env_excludes_b params r_synth)
                       | Infer_err _ -> false))
               | None -> false)
          | None -> false)
     | Infer_err _ -> false))
    fuel

(** val check_callee_body_root_shadow_store_safe_narrow_summary_instantiated :
    global_env -> fn_def -> ty list -> bool **)

let check_callee_body_root_shadow_store_safe_narrow_summary_instantiated env fdef type_args =
  check_callee_body_root_shadow_store_safe_narrow_summary_instantiated_fuel
    (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) env fdef
    type_args

(** val check_expr_root_shadow_store_safe_narrow_summary_checked_fuel :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    root_env -> sctx -> expr -> bool **)

let rec check_expr_root_shadow_store_safe_narrow_summary_checked_fuel fuel env _UU03a9_ n r _UU03a3_ e =
  if check_expr_root_shadow_store_safe_narrow_summary_fuel fuel env _UU03a9_
       n r _UU03a3_ e
  then true
  else (match infer_core_env_state_fuel_roots_shadow_safe fuel env _UU03a9_ n
                r _UU03a3_ e with
        | Infer_ok p ->
          let (p0, _) = p in
          let (p1, _) = p0 in
          let (t, _) = p1 in
          (match e with
           | ELet (m, x, t_hidden, e1, e2) ->
             ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
                (fun _ -> false)
                (fun fuel' ->
                match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                        _UU03a9_ n r _UU03a3_ e1 with
                | Infer_ok p2 ->
                  let (p3, roots1) = p2 in
                  let (p4, r1) = p3 in
                  let (t1, _UU03a3_1) = p4 in
                  (&&)
                    ((&&)
                      ((&&) (ty_compatible_b _UU03a9_ t1 t_hidden)
                        (non_function_value_ty_b t_hidden))
                      ((||)
                        (check_expr_root_shadow_store_safe_narrow_summary_fuel
                          fuel' env _UU03a9_ n r _UU03a3_ e1)
                        ((&&) (capture_ref_free_ty_b env t1)
                          (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                            fuel' env _UU03a9_ n r _UU03a3_ e1))))
                    (match root_env_lookup x r1 with
                     | Some _ -> false
                     | None ->
                       (&&)
                         ((&&) (roots_exclude_b x roots1)
                           (root_env_excludes_b x r1))
                         (match infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env _UU03a9_ n
                                  (root_env_add x roots1 r1)
                                  (sctx_add x t_hidden m _UU03a3_1) e2 with
                          | Infer_ok p5 ->
                            let (p6, _) = p5 in
                            let (p7, r2) = p6 in
                            let (t2, _UU03a3_2) = p7 in
                            (&&)
                              ((&&)
                                ((&&)
                                  (sctx_check_ok env x t_hidden _UU03a3_2)
                                  (capture_ref_free_ty_b env t2))
                                (root_env_excludes_b x (root_env_remove x r2)))
                              (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                                fuel' env _UU03a9_ n
                                (root_env_add x roots1 r1)
                                (sctx_add x t_hidden m _UU03a3_1) e2)
                          | Infer_err _ -> false))
                | Infer_err _ -> false)
                fuel)
           | ELetInfer (m, x, e1, e2) ->
             ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
                (fun _ -> false)
                (fun fuel' ->
                match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                        _UU03a9_ n r _UU03a3_ e1 with
                | Infer_ok p2 ->
                  let (p3, roots1) = p2 in
                  let (p4, r1) = p3 in
                  let (t1, _UU03a3_1) = p4 in
                  (&&)
                    ((&&) (non_function_value_ty_b t1)
                      ((||)
                        (check_expr_root_shadow_store_safe_narrow_summary_fuel
                          fuel' env _UU03a9_ n r _UU03a3_ e1)
                        ((&&) (capture_ref_free_ty_b env t1)
                          (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                            fuel' env _UU03a9_ n r _UU03a3_ e1))))
                    (match root_env_lookup x r1 with
                     | Some _ -> false
                     | None ->
                       (&&)
                         ((&&) (roots_exclude_b x roots1)
                           (root_env_excludes_b x r1))
                         (match infer_core_env_state_fuel_roots_shadow_safe
                                  fuel' env _UU03a9_ n
                                  (root_env_add x roots1 r1)
                                  (sctx_add x t1 m _UU03a3_1) e2 with
                          | Infer_ok p5 ->
                            let (p6, _) = p5 in
                            let (p7, r2) = p6 in
                            let (t2, _UU03a3_2) = p7 in
                            (&&)
                              ((&&)
                                ((&&) (sctx_check_ok env x t1 _UU03a3_2)
                                  (capture_ref_free_ty_b env t2))
                                (root_env_excludes_b x (root_env_remove x r2)))
                              (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                                fuel' env _UU03a9_ n
                                (root_env_add x roots1 r1)
                                (sctx_add x t1 m _UU03a3_1) e2)
                          | Infer_err _ -> false))
                | Infer_err _ -> false)
                fuel)
           | EStruct (_, _, _, l1) ->
             (match l1 with
              | [] -> capture_ref_free_ty_b env t
              | _ :: _ -> false)
           | EDeref e0 ->
             (match e0 with
              | EBorrow (r0, _) ->
                (match r0 with
                 | RShared -> capture_ref_free_ty_b env t
                 | RUnique -> false)
              | _ -> false)
           | _ -> false)
        | Infer_err _ ->
          ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
             (fun _ -> false)
             (fun fuel' ->
             match e with
             | ELet (m, x, t_hidden, e1, e2) ->
               (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                        _UU03a9_ n r _UU03a3_ e1 with
                | Infer_ok p ->
                  let (p0, roots1) = p in
                  let (p1, r1) = p0 in
                  let (t1, _UU03a3_1) = p1 in
                  (&&)
                    ((&&)
                      ((&&) (ty_compatible_b _UU03a9_ t1 t_hidden)
                        (non_function_value_ty_b t_hidden))
                      ((||)
                        (check_expr_root_shadow_store_safe_narrow_summary_fuel
                          fuel' env _UU03a9_ n r _UU03a3_ e1)
                        ((&&) (capture_ref_free_ty_b env t1)
                          (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                            fuel' env _UU03a9_ n r _UU03a3_ e1))))
                    (match root_env_lookup x r1 with
                     | Some _ -> false
                     | None ->
                       (&&)
                         ((&&) (roots_exclude_b x roots1)
                           (root_env_excludes_b x r1))
                         (match infer_core_env_state_fuel_roots_shadow_safe_checked
                                  fuel' env _UU03a9_ n
                                  (root_env_add x roots1 r1)
                                  (sctx_add x t_hidden m _UU03a3_1) e2 with
                          | Infer_ok p2 ->
                            let (p3, _) = p2 in
                            let (p4, r2) = p3 in
                            let (t2, _UU03a3_2) = p4 in
                            (&&)
                              ((&&)
                                ((&&)
                                  (sctx_check_ok env x t_hidden _UU03a3_2)
                                  (capture_ref_free_ty_b env t2))
                                (root_env_excludes_b x (root_env_remove x r2)))
                              (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                                fuel' env _UU03a9_ n
                                (root_env_add x roots1 r1)
                                (sctx_add x t_hidden m _UU03a3_1) e2)
                          | Infer_err _ -> false))
                | Infer_err _ -> false)
             | ELetInfer (m, x, e1, e2) ->
               (match infer_core_env_state_fuel_roots_shadow_safe fuel' env
                        _UU03a9_ n r _UU03a3_ e1 with
                | Infer_ok p ->
                  let (p0, roots1) = p in
                  let (p1, r1) = p0 in
                  let (t1, _UU03a3_1) = p1 in
                  (&&)
                    ((&&) (non_function_value_ty_b t1)
                      ((||)
                        (check_expr_root_shadow_store_safe_narrow_summary_fuel
                          fuel' env _UU03a9_ n r _UU03a3_ e1)
                        ((&&) (capture_ref_free_ty_b env t1)
                          (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                            fuel' env _UU03a9_ n r _UU03a3_ e1))))
                    (match root_env_lookup x r1 with
                     | Some _ -> false
                     | None ->
                       (&&)
                         ((&&) (roots_exclude_b x roots1)
                           (root_env_excludes_b x r1))
                         (match infer_core_env_state_fuel_roots_shadow_safe_checked
                                  fuel' env _UU03a9_ n
                                  (root_env_add x roots1 r1)
                                  (sctx_add x t1 m _UU03a3_1) e2 with
                          | Infer_ok p2 ->
                            let (p3, _) = p2 in
                            let (p4, r2) = p3 in
                            let (t2, _UU03a3_2) = p4 in
                            (&&)
                              ((&&)
                                ((&&) (sctx_check_ok env x t1 _UU03a3_2)
                                  (capture_ref_free_ty_b env t2))
                                (root_env_excludes_b x (root_env_remove x r2)))
                              (check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
                                fuel' env _UU03a9_ n
                                (root_env_add x roots1 r1)
                                (sctx_add x t1 m _UU03a3_1) e2)
                          | Infer_err _ -> false))
                | Infer_err _ -> false)
             | _ -> false)
             fuel))

(** val check_expr_root_shadow_store_safe_narrow_summary_checked :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> root_env -> ctx ->
    expr -> bool **)

let check_expr_root_shadow_store_safe_narrow_summary_checked env _UU03a9_ n r _UU0393_ e =
  check_expr_root_shadow_store_safe_narrow_summary_checked_fuel
    (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) env _UU03a9_ n r
    (sctx_of_ctx _UU0393_) e

(** val check_fn_root_shadow_generic_direct_store_safe_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_generic_direct_store_safe_summary env fdef =
  match generic_direct_call_target_expr fdef.fn_body with
  | Some p ->
    let (p0, synthetic_body) = p in
    let (p1, args) = p0 in
    let (fname, type_args) = p1 in
    (&&) (store_safe_function_value_call_args_b env args)
      (match lookup_fn_b fname env.env_fns with
       | Some callee ->
         (&&) (Nat.eqb (length type_args) callee.fn_type_params)
           (match check_struct_bounds
                    (global_env_with_local_bounds env fdef.fn_bounds)
                    callee.fn_bounds type_args with
            | Some _ -> false
            | None ->
              let callee_body_env =
                global_env_with_local_bounds env
                  (subst_type_params_trait_bounds type_args callee.fn_bounds)
              in
              (match infer_core_env_roots_shadow_safe callee_body_env
                       callee.fn_outlives callee.fn_lifetimes
                       (initial_root_env_for_fn callee)
                       (subst_type_params_ctx type_args (fn_body_ctx callee))
                       (subst_type_params_expr type_args callee.fn_body) with
               | Infer_ok p2 ->
                 let (p3, roots_callee) = p2 in
                 let (p4, r_callee) = p3 in
                 let (t_callee, _) = p4 in
                 (match infer_env_roots_shadow_safe env callee
                          (initial_root_env_for_fn callee) with
                  | Infer_ok _ ->
                    (match infer_env_roots_shadow_safe env
                             (fn_with_body fdef synthetic_body)
                             (initial_root_env_for_fn fdef) with
                     | Infer_ok p5 ->
                       let (p6, roots) = p5 in
                       let (p7, r_out) = p6 in
                       let (t_body, _) = p7 in
                       (&&)
                         ((&&)
                           ((&&)
                             ((&&)
                               ((&&)
                                 ((&&)
                                   ((&&)
                                     (preservation_ready_expr_b
                                       (subst_type_params_expr type_args
                                         callee.fn_body))
                                     (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                                       env callee type_args))
                                   (ty_compatible_b callee.fn_outlives
                                     t_callee
                                     (subst_type_params_ty type_args
                                       callee.fn_ret)))
                                 (fn_params_roots_exclude_b
                                   (apply_type_params type_args
                                     callee.fn_params)
                                   roots_callee))
                               (fn_params_root_env_excludes_b
                                 (apply_type_params type_args
                                   callee.fn_params)
                                 r_callee))
                             (ty_compatible_b fdef.fn_outlives t_body
                               fdef.fn_ret))
                           (fn_params_roots_exclude_b fdef.fn_params roots))
                         (fn_params_root_env_excludes_b fdef.fn_params r_out)
                     | Infer_err _ -> false)
                  | Infer_err _ -> false)
               | Infer_err _ -> false))
       | None -> false)
  | None -> false

(** val check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary env fdef =
  match fdef.fn_captures with
  | [] ->
    (match direct_call_target_expr fdef.fn_body with
     | Some p ->
       let (p0, synthetic_body) = p in
       let (fname, args) = p0 in
       (&&) (store_safe_function_value_call_args_b env args)
         (match lookup_fn_b fname env.env_fns with
          | Some callee ->
            (match callee.fn_captures with
             | [] ->
               (match infer_env_roots_shadow_safe env
                        (fn_with_body fdef synthetic_body)
                        (initial_root_env_for_fn fdef) with
                | Infer_ok p1 ->
                  let (p2, roots) = p1 in
                  let (p3, r_out) = p2 in
                  let (t_body, _) = p3 in
                  (&&)
                    ((&&)
                      (ty_compatible_b fdef.fn_outlives t_body fdef.fn_ret)
                      (fn_params_roots_exclude_b fdef.fn_params roots))
                    (fn_params_root_env_excludes_b fdef.fn_params r_out)
                | Infer_err _ -> false)
             | _ :: _ -> false)
          | None -> false)
     | None -> false)
  | _ :: _ -> false

(** val check_fn_root_shadow_no_capture_direct_call_component_exact_body_target :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_no_capture_direct_call_component_exact_body_target _ fdef =
  match fdef.fn_body with
  | ECall (_, _) -> true
  | _ -> false

(** val check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen :
    Big_int_Z.big_int -> ident list -> global_env -> fn_def -> bool **)

let rec check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen fuel seen env fdef =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> false)
    (fun fuel' ->
    if ident_in_b fdef.fn_name seen
    then true
    else (&&)
           ((&&)
             (check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
               env fdef)
             (check_fn_root_shadow_no_capture_direct_call_component_exact_body_target
               env fdef))
           (match direct_call_target_expr fdef.fn_body with
            | Some p ->
              let (p0, _) = p in
              let (fname, _) = p0 in
              (match lookup_fn_b fname env.env_fns with
               | Some callee ->
                 check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
                   fuel' (fdef.fn_name :: seen) env callee
               | None -> false)
            | None -> false))
    fuel

(** val check_fn_root_shadow_no_capture_direct_call_component_exact_closure :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_no_capture_direct_call_component_exact_closure env fdef =
  check_fn_root_shadow_no_capture_direct_call_component_exact_closure_seen
    (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D1 Nil))))))) [] env fdef

(** val check_fn_root_shadow_captured_call_provenance_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_captured_call_provenance_summary env fdef =
  if check_fn_root_shadow_non_capturing_call_provenance_summary env fdef
  then true
  else (||)
         ((&&) (preservation_ready_expr_b fdef.fn_body)
           (check_fn_root_shadow_captured_callee_provenance_summary env fdef))
         ((||)
           ((||)
             (match captured_call_target_expr fdef.fn_body with
              | Some p ->
                let (p0, args) = p in
                let (fname, captures) = p0 in
                (&&) (preservation_ready_args_b args)
                  (match lookup_fn_b fname env.env_fns with
                   | Some callee ->
                     (&&) (callee_hidden_capture_args_disjoint_b callee args)
                       (match check_make_closure_captures_exact_sctx_with_env
                                env fdef.fn_outlives
                                (sctx_of_ctx (fn_body_ctx fdef)) captures
                                callee.fn_captures with
                        | Infer_ok _ ->
                          (&&)
                            (check_fn_root_shadow_captured_callee_provenance_summary
                              env callee)
                            (match infer_env_roots_shadow_safe env fdef
                                     (initial_root_env_for_fn fdef) with
                             | Infer_ok p1 ->
                               let (p2, roots) = p1 in
                               let (_, r_out) = p2 in
                               (&&)
                                 (fn_params_roots_exclude_b fdef.fn_params
                                   roots)
                                 (fn_params_root_env_excludes_b
                                   fdef.fn_params r_out)
                             | Infer_err _ -> false)
                        | Infer_err _ -> false)
                   | None -> false)
              | None -> false)
             (match infer_core_env_roots_shadow_safe env fdef.fn_outlives
                      fdef.fn_lifetimes (initial_root_env_for_fn fdef)
                      (fn_body_ctx fdef) fdef.fn_body with
              | Infer_ok p ->
                let (p0, roots) = p in
                let (p1, r_out) = p0 in
                let (t_body, _) = p1 in
                (match infer_env_roots_shadow_safe env fdef
                         (initial_root_env_for_fn fdef) with
                 | Infer_ok _ ->
                   (&&)
                     ((&&)
                       ((&&)
                         (check_expr_root_shadow_captured_call_provenance_summary
                           env fdef.fn_outlives fdef.fn_lifetimes
                           (initial_root_env_for_fn fdef) (fn_body_ctx fdef)
                           fdef.fn_body)
                         (ty_compatible_b fdef.fn_outlives t_body fdef.fn_ret))
                       (fn_params_roots_exclude_b fdef.fn_params roots))
                     (fn_params_root_env_excludes_b fdef.fn_params r_out)
                 | Infer_err _ -> false)
              | Infer_err _ -> false))
           (match local_captured_call_target_expr fdef.fn_body with
            | Some p ->
              let (p0, let_body) = p in
              let (p1, direct_body) = p0 in
              let (p2, _) = p1 in
              let (p3, x) = p2 in
              let (p4, _) = p3 in
              let (p5, args) = p4 in
              let (fname, captures) = p5 in
              (&&) (preservation_ready_args_b args)
                (match lookup_fn_b fname env.env_fns with
                 | Some callee ->
                   (&&)
                     ((&&)
                       (callee_hidden_capture_args_disjoint_b callee args)
                       (negb
                         (existsb (ident_eqb x)
                           (ctx_names (params_ctx callee.fn_captures)))))
                     (match check_make_closure_captures_exact_sctx_with_env
                              env fdef.fn_outlives
                              (sctx_of_ctx (fn_body_ctx fdef)) captures
                              callee.fn_captures with
                      | Infer_ok _ ->
                        (&&)
                          (check_fn_root_shadow_captured_callee_provenance_summary
                            env callee)
                          (match infer_env_roots_shadow_safe env
                                   (fn_with_body fdef direct_body)
                                   (initial_root_env_for_fn fdef) with
                           | Infer_ok p6 ->
                             let (p7, roots_direct) = p6 in
                             let (_, r_direct) = p7 in
                             (match infer_env_roots_shadow_safe env
                                      (fn_with_body fdef let_body)
                                      (initial_root_env_for_fn fdef) with
                              | Infer_ok _ ->
                                (&&)
                                  (fn_params_roots_exclude_b fdef.fn_params
                                    roots_direct)
                                  (fn_params_root_env_excludes_b
                                    fdef.fn_params r_direct)
                              | Infer_err _ -> false)
                           | Infer_err _ -> false)
                      | Infer_err _ -> false)
                 | None -> false)
            | None -> false))

(** val check_fn_root_shadow_captured_call_store_safe_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_captured_call_store_safe_summary env fdef =
  (||)
    ((||)
      ((||)
        ((||)
          ((||)
            ((||)
              (check_fn_root_shadow_captured_call_provenance_summary env fdef)
              (match direct_call_target_expr fdef.fn_body with
               | Some p ->
                 let (p0, synthetic_body) = p in
                 let (fname, args) = p0 in
                 (&&) (store_safe_function_value_call_args_b env args)
                   (match lookup_fn_b fname env.env_fns with
                    | Some callee ->
                      (match infer_core_env_roots_shadow_safe env
                               callee.fn_outlives callee.fn_lifetimes
                               (initial_root_env_for_fn callee)
                               (fn_body_ctx callee) callee.fn_body with
                       | Infer_ok p1 ->
                         let (p2, roots_callee) = p1 in
                         let (p3, r_callee) = p2 in
                         let (t_callee, _) = p3 in
                         (match infer_env_roots_shadow_safe env callee
                                  (initial_root_env_for_fn callee) with
                          | Infer_ok _ ->
                            (match infer_env_roots_shadow_safe env
                                     (fn_with_body fdef synthetic_body)
                                     (initial_root_env_for_fn fdef) with
                             | Infer_ok p4 ->
                               let (p5, roots) = p4 in
                               let (p6, r_out) = p5 in
                               let (t_body, _) = p6 in
                               (&&)
                                 ((&&)
                                   ((&&)
                                     ((&&)
                                       ((&&)
                                         ((&&)
                                           (check_expr_root_shadow_store_safe_narrow_summary
                                             env callee.fn_outlives
                                             callee.fn_lifetimes
                                             (initial_root_env_for_fn callee)
                                             (fn_body_ctx callee)
                                             callee.fn_body)
                                           (ty_compatible_b
                                             callee.fn_outlives t_callee
                                             callee.fn_ret))
                                         (fn_params_roots_exclude_b
                                           callee.fn_params roots_callee))
                                       (fn_params_root_env_excludes_b
                                         callee.fn_params r_callee))
                                     (ty_compatible_b fdef.fn_outlives t_body
                                       fdef.fn_ret))
                                   (fn_params_roots_exclude_b fdef.fn_params
                                     roots))
                                 (fn_params_root_env_excludes_b
                                   fdef.fn_params r_out)
                             | Infer_err _ -> false)
                          | Infer_err _ -> false)
                       | Infer_err _ -> false)
                    | None -> false)
               | None -> false))
            (check_fn_root_shadow_generic_direct_store_safe_summary env fdef))
          (match let_bound_generic_direct_call_target_expr fdef.fn_body with
           | Some p ->
             let (p0, synthetic_body) = p in
             let (p1, t_hidden) = p0 in
             let (p2, args) = p1 in
             let (fname, type_args) = p2 in
             (&&) (store_safe_function_value_call_args_b env args)
               (match lookup_fn_b fname env.env_fns with
                | Some callee ->
                  (&&) (Nat.eqb (length type_args) callee.fn_type_params)
                    (match check_struct_bounds
                             (global_env_with_local_bounds env fdef.fn_bounds)
                             callee.fn_bounds type_args with
                     | Some _ -> false
                     | None ->
                       let callee_body_env =
                         global_env_with_local_bounds env
                           (subst_type_params_trait_bounds type_args
                             callee.fn_bounds)
                       in
                       (match infer_core_env_roots_shadow_safe
                                callee_body_env callee.fn_outlives
                                callee.fn_lifetimes
                                (initial_root_env_for_fn callee)
                                (subst_type_params_ctx type_args
                                  (fn_body_ctx callee))
                                (subst_type_params_expr type_args
                                  callee.fn_body) with
                        | Infer_ok p3 ->
                          let (p4, roots_callee) = p3 in
                          let (p5, r_callee) = p4 in
                          let (t_callee, _) = p5 in
                          (match infer_env_roots_shadow_safe env callee
                                   (initial_root_env_for_fn callee) with
                           | Infer_ok _ ->
                             (match infer_env_roots_shadow_safe env
                                      (fn_with_body fdef synthetic_body)
                                      (initial_root_env_for_fn fdef) with
                              | Infer_ok p6 ->
                                let (p7, roots) = p6 in
                                let (_, r_out) = p7 in
                                (&&)
                                  ((&&)
                                    ((&&)
                                      ((&&)
                                        ((&&)
                                          ((&&)
                                            (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                                              env callee type_args)
                                            (ty_compatible_b
                                              callee.fn_outlives t_callee
                                              (subst_type_params_ty type_args
                                                callee.fn_ret)))
                                          (fn_params_roots_exclude_b
                                            (apply_type_params type_args
                                              callee.fn_params)
                                            roots_callee))
                                        (fn_params_root_env_excludes_b
                                          (apply_type_params type_args
                                            callee.fn_params)
                                          r_callee))
                                      (ty_compatible_b fdef.fn_outlives
                                        t_hidden fdef.fn_ret))
                                    (fn_params_roots_exclude_b fdef.fn_params
                                      roots))
                                  (fn_params_root_env_excludes_b
                                    fdef.fn_params r_out)
                              | Infer_err _ -> false)
                           | Infer_err _ -> false)
                        | Infer_err _ -> false))
                | None -> false)
           | None -> false))
        (match if_literal_generic_direct_call_target_expr fdef.fn_body with
         | Some p ->
           let (p0, synthetic_body) = p in
           let (p1, args_else) = p0 in
           let (p2, type_args_else) = p1 in
           let (p3, fname_else) = p2 in
           let (p4, args_then) = p3 in
           let (p5, type_args_then) = p4 in
           let (_, fname_then) = p5 in
           (&&)
             ((&&) (store_safe_function_value_call_args_b env args_then)
               (store_safe_function_value_call_args_b env args_else))
             (match lookup_fn_b fname_then env.env_fns with
              | Some callee_then ->
                (match lookup_fn_b fname_else env.env_fns with
                 | Some callee_else ->
                   (&&)
                     ((&&)
                       (Nat.eqb (length type_args_then)
                         callee_then.fn_type_params)
                       (Nat.eqb (length type_args_else)
                         callee_else.fn_type_params))
                     (match check_struct_bounds
                              (global_env_with_local_bounds env
                                fdef.fn_bounds)
                              callee_then.fn_bounds type_args_then with
                      | Some _ -> false
                      | None ->
                        (match check_struct_bounds
                                 (global_env_with_local_bounds env
                                   fdef.fn_bounds)
                                 callee_else.fn_bounds type_args_else with
                         | Some _ -> false
                         | None ->
                           (match infer_core_env_roots_shadow_safe env
                                    callee_then.fn_outlives
                                    callee_then.fn_lifetimes
                                    (initial_root_env_for_fn callee_then)
                                    (subst_type_params_ctx type_args_then
                                      (fn_body_ctx callee_then))
                                    (subst_type_params_expr type_args_then
                                      callee_then.fn_body) with
                            | Infer_ok p6 ->
                              let (p7, roots_then) = p6 in
                              let (p8, r_then) = p7 in
                              let (t_then, _) = p8 in
                              (match infer_env_roots_shadow_safe env
                                       callee_then
                                       (initial_root_env_for_fn callee_then) with
                               | Infer_ok _ ->
                                 (match infer_core_env_roots_shadow_safe env
                                          callee_else.fn_outlives
                                          callee_else.fn_lifetimes
                                          (initial_root_env_for_fn
                                            callee_else)
                                          (subst_type_params_ctx
                                            type_args_else
                                            (fn_body_ctx callee_else))
                                          (subst_type_params_expr
                                            type_args_else
                                            callee_else.fn_body) with
                                  | Infer_ok p9 ->
                                    let (p10, roots_else) = p9 in
                                    let (p11, r_else) = p10 in
                                    let (t_else, _) = p11 in
                                    (match infer_env_roots_shadow_safe env
                                             callee_else
                                             (initial_root_env_for_fn
                                               callee_else) with
                                     | Infer_ok _ ->
                                       (match infer_env_roots_shadow_safe env
                                                (fn_with_body fdef
                                                  synthetic_body)
                                                (initial_root_env_for_fn fdef) with
                                        | Infer_ok p12 ->
                                          let (p13, roots) = p12 in
                                          let (p14, r_out) = p13 in
                                          let (t_body, _) = p14 in
                                          (&&)
                                            ((&&)
                                              ((&&)
                                                ((&&)
                                                  ((&&)
                                                    ((&&)
                                                      ((&&)
                                                        ((&&)
                                                          ((&&)
                                                            ((&&)
                                                              (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                                                                env
                                                                callee_then
                                                                type_args_then)
                                                              (ty_compatible_b
                                                                callee_then.fn_outlives
                                                                t_then
                                                                (subst_type_params_ty
                                                                  type_args_then
                                                                  callee_then.fn_ret)))
                                                            (fn_params_roots_exclude_b
                                                              (apply_type_params
                                                                type_args_then
                                                                callee_then.fn_params)
                                                              roots_then))
                                                          (fn_params_root_env_excludes_b
                                                            (apply_type_params
                                                              type_args_then
                                                              callee_then.fn_params)
                                                            r_then))
                                                        (check_callee_body_root_shadow_store_safe_narrow_summary_instantiated
                                                          env callee_else
                                                          type_args_else))
                                                      (ty_compatible_b
                                                        callee_else.fn_outlives
                                                        t_else
                                                        (subst_type_params_ty
                                                          type_args_else
                                                          callee_else.fn_ret)))
                                                    (fn_params_roots_exclude_b
                                                      (apply_type_params
                                                        type_args_else
                                                        callee_else.fn_params)
                                                      roots_else))
                                                  (fn_params_root_env_excludes_b
                                                    (apply_type_params
                                                      type_args_else
                                                      callee_else.fn_params)
                                                    r_else))
                                                (ty_compatible_b
                                                  fdef.fn_outlives t_body
                                                  fdef.fn_ret))
                                              (fn_params_roots_exclude_b
                                                fdef.fn_params roots))
                                            (fn_params_root_env_excludes_b
                                              fdef.fn_params r_out)
                                        | Infer_err _ -> false)
                                     | Infer_err _ -> false)
                                  | Infer_err _ -> false)
                               | Infer_err _ -> false)
                            | Infer_err _ -> false)))
                 | None -> false)
              | None -> false)
         | None -> false))
      (match local_fn_value_call_target_expr_with_binder fdef.fn_body with
       | Some p ->
         let (p0, synthetic_body) = p in
         let (p1, args) = p0 in
         let (x, fname) = p1 in
         (&&)
           ((&&)
             ((&&) (store_safe_function_value_call_args_b env args)
               (negb (ident_in_b x (args_free_vars_checker args))))
             (negb (ident_in_b x (args_local_store_names args))))
           (match lookup_fn_b fname env.env_fns with
            | Some callee ->
              (&&)
                (check_fn_root_shadow_generic_direct_store_safe_summary env
                  callee)
                (match infer_env_roots_shadow_safe env
                         (fn_with_body fdef synthetic_body)
                         (initial_root_env_for_fn fdef) with
                 | Infer_ok p2 ->
                   let (p3, roots) = p2 in
                   let (p4, r_out) = p3 in
                   let (t_body, _) = p4 in
                   (&&)
                     ((&&)
                       (ty_compatible_b fdef.fn_outlives t_body fdef.fn_ret)
                       (fn_params_roots_exclude_b fdef.fn_params roots))
                     (fn_params_root_env_excludes_b fdef.fn_params r_out)
                 | Infer_err _ -> false)
            | None -> false)
       | None -> false))
    (match infer_core_env_roots_shadow_safe_checked env fdef.fn_outlives
             fdef.fn_lifetimes (initial_root_env_for_fn fdef)
             (fn_body_ctx fdef) fdef.fn_body with
     | Infer_ok p ->
       let (p0, roots) = p in
       let (p1, r_out) = p0 in
       let (t_body, _) = p1 in
       (match infer_env_roots_shadow_safe_checked env fdef
                (initial_root_env_for_fn fdef) with
        | Infer_ok _ ->
          (&&)
            ((&&)
              ((&&)
                (check_expr_root_shadow_store_safe_narrow_summary_checked env
                  fdef.fn_outlives fdef.fn_lifetimes
                  (initial_root_env_for_fn fdef) (fn_body_ctx fdef)
                  fdef.fn_body)
                (ty_compatible_b fdef.fn_outlives t_body fdef.fn_ret))
              (fn_params_roots_exclude_b fdef.fn_params roots))
            (fn_params_root_env_excludes_b fdef.fn_params r_out)
        | Infer_err _ -> false)
     | Infer_err _ -> false)

(** val check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary env fdef =
  (||) (check_fn_root_shadow_captured_call_store_safe_summary env fdef)
    (check_fn_root_shadow_no_capture_direct_call_component_exact_closure env
      fdef)

(** val check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary :
    global_env -> fn_def -> bool **)

let check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary env fdef =
  if check_fn_root_shadow_no_capture_direct_call_component_store_safe_summary
       env fdef
  then check_fn_root_shadow_no_capture_direct_call_component_exact_closure
         env fdef
  else check_fn_root_shadow_captured_call_store_safe_summary env fdef

(** val check_env_root_shadow_direct_call_provenance_summary :
    global_env -> bool **)

let check_env_root_shadow_direct_call_provenance_summary env =
  forallb (check_fn_root_shadow_direct_call_provenance_summary env)
    env.env_fns

(** val check_env_root_shadow_captured_call_provenance_summary :
    global_env -> bool **)

let check_env_root_shadow_captured_call_provenance_summary env =
  forallb (check_fn_root_shadow_captured_call_provenance_summary env)
    env.env_fns

(** val check_fn_ordinary_safety_gate : global_env -> fn_def -> bool **)

let check_fn_ordinary_safety_gate =
  check_fn_root_shadow_captured_call_provenance_summary

(** val check_program_env : global_env -> bool **)

let check_program_env env =
  forallb (fun f ->
    match infer_full_env env f with
    | Infer_ok _ -> check_fn_ordinary_safety_gate env f
    | Infer_err _ -> false) env.env_fns

(** val check_program_env_alpha : global_env -> bool **)

let check_program_env_alpha env =
  (&&) (global_names_unique_b (alpha_normalize_global_env env))
    (check_program_env (alpha_normalize_global_env env))

(** val check_program_env_alpha_validated : global_env -> bool **)

let check_program_env_alpha_validated =
  check_program_env_alpha

(** val check_program_env_alpha_elab : global_env -> bool **)

let check_program_env_alpha_elab env =
  (&&) (global_names_unique_b (alpha_normalize_global_env env))
    (match infer_program_env_alpha_elab env with
     | Infer_ok env' -> check_program_env env'
     | Infer_err _ -> false)

(** val check_env_preservation_ready : global_env -> bool **)

let check_env_preservation_ready env =
  forallb (fun fdef -> preservation_ready_expr_b fdef.fn_body) env.env_fns

(** val check_program_env_alpha_validated_root_shadow : global_env -> bool **)

let check_program_env_alpha_validated_root_shadow env =
  (&&) (check_program_env_alpha_validated env)
    (check_env_root_shadow_summary (alpha_normalize_global_env env))

(** val check_program_env_alpha_validated_root_shadow_provenance_summary :
    global_env -> bool **)

let check_program_env_alpha_validated_root_shadow_provenance_summary env =
  (&&) (check_program_env_alpha_validated env)
    (check_env_root_shadow_provenance_summary
      (alpha_normalize_global_env env))

(** val check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary :
    global_env -> bool **)

let check_program_env_alpha_validated_root_shadow_direct_call_provenance_summary env =
  (&&) (check_program_env_alpha_validated env)
    (check_env_root_shadow_direct_call_provenance_summary
      (alpha_normalize_global_env env))

(** val check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary :
    global_env -> bool **)

let check_program_env_alpha_elab_validated_root_shadow_captured_call_provenance_summary env =
  (&&) (top_level_names_unique_b (alpha_normalize_global_env env))
    (match infer_program_env_alpha_elab env with
     | Infer_ok env' ->
       check_env_root_shadow_captured_call_provenance_summary env'
     | Infer_err _ -> false)

(** val check_program_env_alpha_validated_root_shadow_provenance :
    global_env -> bool **)

let check_program_env_alpha_validated_root_shadow_provenance env =
  (&&) (check_program_env_alpha_validated env)
    ((&&)
      (check_env_root_shadow_provenance_summary
        (alpha_normalize_global_env env))
      (check_env_preservation_ready (alpha_normalize_global_env env)))

(** val infer_fn_env_end2end :
    global_env -> fn_def -> (((ty * ctx) * root_env) * root_set) infer_result **)

let infer_fn_env_end2end env f =
  let r0 = initial_root_env_for_params (app f.fn_params f.fn_captures) in
  (match infer_full_env_roots_checked env f r0 with
   | Infer_ok res ->
     if check_fn_root_shadow_captured_call_store_safe_or_no_capture_direct_component_exact_closure_summary
          env f
     then Infer_ok res
     else Infer_err ErrEndToEndSafetyGateFailed
   | Infer_err err -> Infer_err err)

(** val infer_fns_env_end2end :
    global_env -> fn_def list -> unit infer_result **)

let rec infer_fns_env_end2end env = function
| [] -> Infer_ok ()
| f :: rest ->
  (match infer_fn_env_end2end env f with
   | Infer_ok _ -> infer_fns_env_end2end env rest
   | Infer_err err -> Infer_err (ErrInFunction (f.fn_name, err)))

(** val infer_program_env_end2end : global_env -> global_env infer_result **)

let infer_program_env_end2end env =
  let env_alpha = alpha_normalize_global_env env in
  if global_names_unique_b env_alpha
  then (match infer_program_env_alpha_elab env with
        | Infer_ok env_elab ->
          (match infer_fns_env_end2end env_elab env_elab.env_fns with
           | Infer_ok _ -> Infer_ok env_elab
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
  else Infer_err ErrGlobalNamesNotUnique

(** val check_program_env_end2end : global_env -> bool **)

let check_program_env_end2end env =
  match infer_program_env_end2end env with
  | Infer_ok _ -> true
  | Infer_err _ -> false

(** val infer_fn_env_end2end_strict_exact_closure :
    global_env -> fn_def -> (((ty * ctx) * root_env) * root_set) infer_result **)

let infer_fn_env_end2end_strict_exact_closure env f =
  let r0 = initial_root_env_for_params (app f.fn_params f.fn_captures) in
  (match infer_full_env_roots_checked env f r0 with
   | Infer_ok res ->
     if check_fn_root_shadow_strict_exact_closure_captured_or_no_capture_direct_component_summary
          env f
     then Infer_ok res
     else Infer_err ErrEndToEndSafetyGateFailed
   | Infer_err err -> Infer_err err)

(** val infer_fns_env_end2end_strict_exact_closure :
    global_env -> fn_def list -> unit infer_result **)

let rec infer_fns_env_end2end_strict_exact_closure env = function
| [] -> Infer_ok ()
| f :: rest ->
  (match infer_fn_env_end2end_strict_exact_closure env f with
   | Infer_ok _ -> infer_fns_env_end2end_strict_exact_closure env rest
   | Infer_err err -> Infer_err (ErrInFunction (f.fn_name, err)))

(** val infer_program_env_end2end_strict_exact_closure :
    global_env -> global_env infer_result **)

let infer_program_env_end2end_strict_exact_closure env =
  let env_alpha = alpha_normalize_global_env env in
  if global_names_unique_b env_alpha
  then (match infer_program_env_alpha_elab env with
        | Infer_ok env_elab ->
          (match infer_fns_env_end2end_strict_exact_closure env_elab
                   env_elab.env_fns with
           | Infer_ok _ -> Infer_ok env_elab
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
  else Infer_err ErrGlobalNamesNotUnique

(** val check_program_env_end2end_strict_exact_closure :
    global_env -> bool **)

let check_program_env_end2end_strict_exact_closure env =
  match infer_program_env_end2end_strict_exact_closure env with
  | Infer_ok _ -> true
  | Infer_err _ -> false

type raw_expr =
| RawUnit
| RawLit of literal
| RawVar of ident
| RawFn of ident
| RawPlace of place
| RawLet of mutability * ident * ty * raw_expr * raw_expr
| RawLetInfer of mutability * ident * raw_expr * raw_expr
| RawCall of ident * raw_expr list
| RawCallGeneric of ident * ty list * raw_expr list
| RawCallExpr of raw_expr * raw_expr list
| RawStruct of string * lifetime list * ty list * (string * raw_expr) list
| RawEnum of string * string * lifetime list * lifetime list * ty list
   * raw_expr list
| RawMatch of raw_expr * ((string * ident list) * raw_expr) list
| RawReplace of place * raw_expr
| RawAssign of place * raw_expr
| RawBorrow of ref_kind * place
| RawDeref of raw_expr
| RawDrop of raw_expr
| RawIf of raw_expr * raw_expr * raw_expr
| RawClosure of ident list * param list * ty * raw_expr
| RawLetRec of ident list * raw_rec_fn list * raw_expr
| RawCore of expr
and raw_rec_fn =
| MkRawRecFn of ident * param list * ty * raw_expr

(** val raw_rec_fn_name : raw_rec_fn -> ident **)

let raw_rec_fn_name = function
| MkRawRecFn (fname, _, _, _) -> fname

(** val raw_rec_fn_params : raw_rec_fn -> param list **)

let raw_rec_fn_params = function
| MkRawRecFn (_, params, _, _) -> params

(** val raw_rec_fn_ret : raw_rec_fn -> ty **)

let raw_rec_fn_ret = function
| MkRawRecFn (_, _, ret, _) -> ret

(** val raw_rec_fn_body : raw_rec_fn -> raw_expr **)

let raw_rec_fn_body = function
| MkRawRecFn (_, _, _, body) -> body

type raw_fn_def = { raw_fn_name : ident;
                    raw_fn_lifetimes : Big_int_Z.big_int;
                    raw_fn_outlives : outlives_ctx;
                    raw_fn_params : param list; raw_fn_ret : ty;
                    raw_fn_body : raw_expr;
                    raw_fn_type_params : Big_int_Z.big_int;
                    raw_fn_bounds : trait_bound list }

(** val fn_stub_of_raw : raw_fn_def -> fn_def **)

let fn_stub_of_raw f =
  { fn_name = f.raw_fn_name; fn_lifetimes = f.raw_fn_lifetimes; fn_outlives =
    f.raw_fn_outlives; fn_captures = []; fn_params = f.raw_fn_params;
    fn_ret = f.raw_fn_ret; fn_body = EUnit; fn_type_params =
    f.raw_fn_type_params; fn_bounds = f.raw_fn_bounds }

(** val append_env_fns : global_env -> fn_def list -> global_env **)

let append_env_fns env fns =
  { env_structs = env.env_structs; env_enums = env.env_enums; env_traits =
    env.env_traits; env_impls = env.env_impls; env_local_bounds =
    env.env_local_bounds; env_fns = (app env.env_fns fns) }

(** val closure_elab_suffix : Big_int_Z.big_int -> string **)

let rec closure_elab_suffix idx =
  (fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
    (fun _ -> "")
    (fun idx' -> (^) "_" (closure_elab_suffix idx'))
    idx

(** val closure_elab_name : Big_int_Z.big_int -> ident **)

let closure_elab_name idx =
  (((^) "__facet_closure" (closure_elab_suffix idx)), Big_int_Z.zero_big_int)

(** val generic_fn_value_wrapper_name : Big_int_Z.big_int -> ident **)

let generic_fn_value_wrapper_name idx =
  (((^) "__facet_generic_fn_value" (closure_elab_suffix idx)),
    Big_int_Z.zero_big_int)

(** val wrapper_params_from_tys_from :
    Big_int_Z.big_int -> ty list -> param list **)

let rec wrapper_params_from_tys_from idx = function
| [] -> []
| t :: rest ->
  { param_mutability = MImmutable; param_name = ("__facet_generic_arg", idx);
    param_ty =
    t } :: (wrapper_params_from_tys_from (Big_int_Z.succ_big_int idx) rest)

(** val wrapper_params_from_tys : ty list -> param list **)

let wrapper_params_from_tys tys =
  wrapper_params_from_tys_from Big_int_Z.zero_big_int tys

(** val expr_vars_of_params : param list -> expr list **)

let rec expr_vars_of_params = function
| [] -> []
| p :: rest -> (EVar p.param_name) :: (expr_vars_of_params rest)

(** val infer_fn_value_type_args_expected :
    fn_def -> ty option -> ((ty list * ty list) * ty) option **)

let infer_fn_value_type_args_expected fdef = function
| Some t ->
  let MkTy (_, t0) = t in
  (match t0 with
   | TFn (param_tys, ret) ->
     (match infer_call_type_args_expected fdef param_tys (Some ret) with
      | Some type_args -> Some ((type_args, param_tys), ret)
      | None -> None)
   | _ -> None)
| None -> None

(** val auto_drop_ret_name : Big_int_Z.big_int -> ident **)

let auto_drop_ret_name idx =
  ("__facet_auto_drop_ret", idx)

(** val auto_drop_tmp_name : Big_int_Z.big_int -> ident **)

let auto_drop_tmp_name idx =
  ("__facet_auto_drop", idx)

(** val place_of_path_from : place -> field_path -> place **)

let rec place_of_path_from base = function
| [] -> base
| field :: rest -> place_of_path_from (PField (base, field)) rest

(** val place_of_field_path : ident -> field_path -> place **)

let place_of_field_path x p =
  place_of_path_from (PVar x) p

(** val wrap_auto_drop_expr :
    ident -> field_path list -> expr -> Big_int_Z.big_int ->
    expr * Big_int_Z.big_int **)

let rec wrap_auto_drop_expr x paths ret next =
  match paths with
  | [] -> (ret, next)
  | path :: rest ->
    let tmp = auto_drop_tmp_name next in
    let (tail, next') =
      wrap_auto_drop_expr x rest ret (Big_int_Z.succ_big_int next)
    in
    ((ELet (MImmutable, tmp, (MkTy (UUnrestricted, TUnits)), (EDrop (EPlace
    (place_of_field_path x path))), tail)), next')

(** val wrap_let_body_auto_drops :
    global_env -> ident -> ty -> sctx -> ty -> expr -> Big_int_Z.big_int ->
    expr * Big_int_Z.big_int **)

let wrap_let_body_auto_drops env x t _UU03a3__body body_ty body next =
  match auto_drop_live_paths env x t _UU03a3__body with
  | [] -> (body, next)
  | f :: l ->
    let ret = auto_drop_ret_name next in
    let (tail, next') =
      wrap_auto_drop_expr x (f :: l) (EVar ret) (Big_int_Z.succ_big_int next)
    in
    ((ELet (MImmutable, ret, body_ty, body, tail)), next')

(** val closure_elab_capture_param :
    global_env -> outlives_ctx -> sctx -> ident -> param infer_result **)

let closure_elab_capture_param env _ _UU03a3_ x =
  match sctx_lookup x _UU03a3_ with
  | Some p ->
    let (t, st) = p in
    if negb (binding_available_b st [])
    then Infer_err (ErrAlreadyConsumed x)
    else (match sctx_lookup_mut x _UU03a3_ with
          | Some m ->
            (match m with
             | MImmutable ->
               if usage_eqb (ty_usage t) UUnrestricted
               then if capture_ref_free_ty_b env t
                    then Infer_ok { param_mutability = MImmutable;
                           param_name = x; param_ty = t }
                    else let MkTy (_, t0) = t in
                         (match t0 with
                          | TRef (_, r, _) ->
                            (match r with
                             | RShared ->
                               Infer_ok { param_mutability = MImmutable;
                                 param_name = x; param_ty = t }
                             | RUnique ->
                               Infer_err (ErrNotAReference (ty_core t)))
                          | _ -> Infer_err (ErrNotAReference (ty_core t)))
               else Infer_err (ErrUsageMismatch ((ty_usage t), UUnrestricted))
             | MMutable -> Infer_err (ErrNotMutable x))
          | None -> Infer_err (ErrUnknownVar x))
  | None -> Infer_err (ErrUnknownVar x)

(** val closure_elab_capture_params :
    global_env -> outlives_ctx -> sctx -> ident list -> param list
    infer_result **)

let rec closure_elab_capture_params env _UU03a9_ _UU03a3_ = function
| [] -> Infer_ok []
| x :: xs ->
  (match closure_elab_capture_param env _UU03a9_ _UU03a3_ x with
   | Infer_ok p ->
     (match closure_elab_capture_params env _UU03a9_ _UU03a3_ xs with
      | Infer_ok ps -> Infer_ok (p :: ps)
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)

(** val infer_elaborated_expr_state :
    Big_int_Z.big_int -> global_env -> outlives_ctx -> Big_int_Z.big_int ->
    sctx -> expr -> sctx infer_result **)

let infer_elaborated_expr_state fuel env _UU03a9_ n _UU03a3_ e =
  match infer_core_env_state_fuel fuel env _UU03a9_ n _UU03a3_ e with
  | Infer_ok p -> let (_, _UU03a3_') = p in Infer_ok _UU03a3_'
  | Infer_err err -> Infer_err err

(** val elaborate_raw_expr_fuel :
    Big_int_Z.big_int -> ty option -> global_env -> outlives_ctx ->
    Big_int_Z.big_int -> sctx -> Big_int_Z.big_int -> raw_expr ->
    (((expr * sctx) * fn_def list) * Big_int_Z.big_int) infer_result **)

let rec elaborate_raw_expr_fuel fuel expected env _UU03a9_ n _UU03a3_ next e =
  let finish = fun env' e' extras next' ->
    match infer_elaborated_expr_state fuel env' _UU03a9_ n _UU03a3_ e' with
    | Infer_ok _UU03a3_' -> Infer_ok (((e', _UU03a3_'), extras), next')
    | Infer_err err -> Infer_err err
  in
  let go_args =
    let rec go_args fuel0 env0 _UU03a3_0 next0 = function
    | [] -> Infer_ok ((([], _UU03a3_0), []), next0)
    | a :: rest ->
      (match elaborate_raw_expr_fuel fuel0 None env0 _UU03a9_ n _UU03a3_0
               next0 a with
       | Infer_ok p ->
         let (p0, next1) = p in
         let (p1, extras1) = p0 in
         let (a', _UU03a3_1) = p1 in
         let env1 = append_env_fns env0 extras1 in
         (match go_args fuel0 env1 _UU03a3_1 next1 rest with
          | Infer_ok p2 ->
            let (p3, next2) = p2 in
            let (p4, extras2) = p3 in
            let (rest', _UU03a3_2) = p4 in
            Infer_ok ((((a' :: rest'), _UU03a3_2), (app extras1 extras2)),
            next2)
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    in go_args
  in
  let go_args_expected =
    let rec go_args_expected fuel0 env0 _UU03a3_0 next0 args params =
      match args with
      | [] ->
        (match params with
         | [] -> Infer_ok ((([], _UU03a3_0), []), next0)
         | _ :: _ -> Infer_err ErrArityMismatch)
      | a :: rest ->
        (match params with
         | [] -> Infer_err ErrArityMismatch
         | p :: ps ->
           (match elaborate_raw_expr_fuel fuel0 (Some p.param_ty) env0
                    _UU03a9_ n _UU03a3_0 next0 a with
            | Infer_ok p0 ->
              let (p1, next1) = p0 in
              let (p2, extras1) = p1 in
              let (a', _UU03a3_1) = p2 in
              let env1 = append_env_fns env0 extras1 in
              (match go_args_expected fuel0 env1 _UU03a3_1 next1 rest ps with
               | Infer_ok p3 ->
                 let (p4, next2) = p3 in
                 let (p5, extras2) = p4 in
                 let (rest', _UU03a3_2) = p5 in
                 Infer_ok ((((a' :: rest'), _UU03a3_2),
                 (app extras1 extras2)), next2)
               | Infer_err err -> Infer_err err)
            | Infer_err err -> Infer_err err))
    in go_args_expected
  in
  let infer_arg_tys_state =
    let rec infer_arg_tys_state fuel0 env0 _UU03a3_0 = function
    | [] -> Infer_ok ([], _UU03a3_0)
    | a :: rest ->
      (match infer_core_env_state_fuel fuel0 env0 _UU03a9_ n _UU03a3_0 a with
       | Infer_ok p ->
         let (t, _UU03a3_1) = p in
         (match infer_arg_tys_state fuel0 env0 _UU03a3_1 rest with
          | Infer_ok p0 ->
            let (ts, _UU03a3_2) = p0 in Infer_ok ((t :: ts), _UU03a3_2)
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    in infer_arg_tys_state
  in
  let go_fields =
    let rec go_fields fuel0 env0 _UU03a3_0 next0 = function
    | [] -> Infer_ok ((([], _UU03a3_0), []), next0)
    | y :: rest ->
      let (fname, fe) = y in
      (match elaborate_raw_expr_fuel fuel0 None env0 _UU03a9_ n _UU03a3_0
               next0 fe with
       | Infer_ok p ->
         let (p0, next1) = p in
         let (p1, extras1) = p0 in
         let (fe', _UU03a3_1) = p1 in
         let env1 = append_env_fns env0 extras1 in
         (match go_fields fuel0 env1 _UU03a3_1 next1 rest with
          | Infer_ok p2 ->
            let (p3, next2) = p2 in
            let (p4, extras2) = p3 in
            let (rest', _UU03a3_2) = p4 in
            Infer_ok (((((fname, fe') :: rest'), _UU03a3_2),
            (app extras1 extras2)), next2)
          | Infer_err err -> Infer_err err)
       | Infer_err err -> Infer_err err)
    in go_fields
  in
  ((fun fO fS n -> if Big_int_Z.sign_big_int n <= 0 then fO ()
  else fS (Big_int_Z.pred_big_int n))
     (fun _ -> Infer_err ErrNotImplemented)
     (fun fuel' ->
     match e with
     | RawUnit -> finish env EUnit [] next
     | RawLit lit -> finish env (ELit lit) [] next
     | RawVar x -> finish env (EVar x) [] next
     | RawFn fname ->
       (match lookup_fn_b fname env.env_fns with
        | Some fdef ->
          if Nat.eqb fdef.fn_type_params Big_int_Z.zero_big_int
          then finish env (EFn fname) [] next
          else if negb (no_captures_b fdef)
               then Infer_err ErrNotImplemented
               else (match expected with
                     | Some t_expected ->
                       if ty_compatible_b _UU03a9_ (fn_value_ty fdef)
                            t_expected
                       then finish env (EFn fname) [] next
                       else if negb
                                 (Nat.eqb fdef.fn_lifetimes
                                   Big_int_Z.zero_big_int)
                            then Infer_err ErrTypeArgInferenceFailed
                            else (match infer_fn_value_type_args_expected
                                          fdef expected with
                                  | Some p ->
                                    let (p0, ret) = p in
                                    let (type_args, param_tys) = p0 in
                                    (match check_struct_bounds env
                                             fdef.fn_bounds type_args with
                                     | Some err -> Infer_err err
                                     | None ->
                                       let wrapper_name =
                                         generic_fn_value_wrapper_name next
                                       in
                                       let wrapper_params =
                                         wrapper_params_from_tys param_tys
                                       in
                                       let wrapper_body = ECallGeneric
                                         (fname, type_args,
                                         (expr_vars_of_params wrapper_params))
                                       in
                                       let wrapper = { fn_name =
                                         wrapper_name; fn_lifetimes =
                                         Big_int_Z.zero_big_int;
                                         fn_outlives = []; fn_captures = [];
                                         fn_params = wrapper_params; fn_ret =
                                         ret; fn_body = wrapper_body;
                                         fn_type_params =
                                         Big_int_Z.zero_big_int; fn_bounds =
                                         [] }
                                       in
                                       let env' =
                                         append_env_fns env (wrapper :: [])
                                       in
                                       finish env' (EFn wrapper_name)
                                         (wrapper :: [])
                                         (Big_int_Z.succ_big_int next))
                                  | None ->
                                    Infer_err ErrTypeArgInferenceFailed)
                     | None -> Infer_err ErrTypeArgInferenceFailed)
        | None -> finish env (EFn fname) [] next)
     | RawPlace p -> finish env (EPlace p) [] next
     | RawLet (m, x, t, e1, e2) ->
       (match elaborate_raw_expr_fuel fuel' (Some t) env _UU03a9_ n _UU03a3_
                next e1 with
        | Infer_ok p ->
          let (p0, next1) = p in
          let (p1, extras1) = p0 in
          let (e1', _UU03a3_1) = p1 in
          let env1 = append_env_fns env extras1 in
          (match elaborate_raw_expr_fuel fuel' expected env1 _UU03a9_ n
                   (sctx_add x t m _UU03a3_1) next1 e2 with
           | Infer_ok p2 ->
             let (p3, next2) = p2 in
             let (p4, extras2) = p3 in
             let (e2', _UU03a3_2) = p4 in
             let extras = app extras1 extras2 in
             let env2 = append_env_fns env extras in
             (match infer_core_env_state_fuel fuel' env2 _UU03a9_ n
                      (sctx_add x t m _UU03a3_1) e2' with
              | Infer_ok p5 ->
                let (t2, _) = p5 in
                let (e2'', next3) =
                  wrap_let_body_auto_drops env2 x t _UU03a3_2 t2 e2' next2
                in
                let e' = ELet (m, x, t, e1', e2'') in
                finish env2 e' extras next3
              | Infer_err err -> Infer_err err)
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
     | RawLetInfer (m, x, e1, e2) ->
       (match elaborate_raw_expr_fuel fuel' None env _UU03a9_ n _UU03a3_ next
                e1 with
        | Infer_ok p ->
          let (p0, next1) = p in
          let (p1, extras1) = p0 in
          let (e1', _UU03a3_1) = p1 in
          (match infer_core_env_state_fuel fuel' (append_env_fns env extras1)
                   _UU03a9_ n _UU03a3_ e1' with
           | Infer_ok p2 ->
             let (t1, _) = p2 in
             let env1 = append_env_fns env extras1 in
             (match elaborate_raw_expr_fuel fuel' expected env1 _UU03a9_ n
                      (sctx_add x t1 m _UU03a3_1) next1 e2 with
              | Infer_ok p3 ->
                let (p4, next2) = p3 in
                let (p5, extras2) = p4 in
                let (e2', _UU03a3_2) = p5 in
                let extras = app extras1 extras2 in
                let env2 = append_env_fns env extras in
                (match infer_core_env_state_fuel fuel' env2 _UU03a9_ n
                         (sctx_add x t1 m _UU03a3_1) e2' with
                 | Infer_ok p6 ->
                   let (t2, _) = p6 in
                   let (e2'', next3) =
                     wrap_let_body_auto_drops env2 x t1 _UU03a3_2 t2 e2' next2
                   in
                   let e' = ELet (m, x, t1, e1', e2'') in
                   finish env2 e' extras next3
                 | Infer_err err -> Infer_err err)
              | Infer_err err -> Infer_err err)
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
     | RawCall (fname, args) ->
       let infer_plain =
         match go_args fuel' env _UU03a3_ next args with
         | Infer_ok p ->
           let (p0, next') = p in
           let (p1, extras) = p0 in
           let (args', _) = p1 in
           let env' = append_env_fns env extras in
           (match lookup_fn_b fname env'.env_fns with
            | Some fdef ->
              if Nat.eqb fdef.fn_type_params Big_int_Z.zero_big_int
              then finish env' (ECall (fname, args')) extras next'
              else (match infer_arg_tys_state fuel' env' _UU03a3_ args' with
                    | Infer_ok p2 ->
                      let (arg_tys, _) = p2 in
                      (match infer_call_type_args_expected fdef arg_tys
                               expected with
                       | Some type_args ->
                         (match check_struct_bounds env' fdef.fn_bounds
                                  type_args with
                          | Some err -> Infer_err err
                          | None ->
                            (match specialize_simple_generic_wrapper_call
                                     env' fname type_args args' with
                             | Some p3 ->
                               let (p4, target_args) = p3 in
                               let (target, target_type_args) = p4 in
                               finish env' (ECallGeneric (target,
                                 target_type_args, target_args)) extras next'
                             | None ->
                               finish env' (ECallGeneric (fname, type_args,
                                 args')) extras next'))
                       | None -> Infer_err ErrTypeArgInferenceFailed)
                    | Infer_err err -> Infer_err err)
            | None -> finish env' (ECall (fname, args')) extras next')
         | Infer_err err -> Infer_err err
       in
       (match lookup_fn_b fname env.env_fns with
        | Some fdef ->
          if Nat.eqb fdef.fn_type_params Big_int_Z.zero_big_int
          then (match go_args_expected fuel' env _UU03a3_ next args
                        fdef.fn_params with
                | Infer_ok p ->
                  let (p0, next') = p in
                  let (p1, extras) = p0 in
                  let (args', _) = p1 in
                  finish (append_env_fns env extras) (ECall (fname, args'))
                    extras next'
                | Infer_err _ -> infer_plain)
          else infer_plain
        | None -> infer_plain)
     | RawCallGeneric (fname, type_args, args) ->
       (match go_args fuel' env _UU03a3_ next args with
        | Infer_ok p ->
          let (p0, next') = p in
          let (p1, extras) = p0 in
          let (args', _) = p1 in
          let env' = append_env_fns env extras in
          (match specialize_simple_generic_wrapper_call env' fname type_args
                   args' with
           | Some p2 ->
             let (p3, target_args) = p2 in
             let (target, target_type_args) = p3 in
             finish env' (ECallGeneric (target, target_type_args,
               target_args)) extras next'
           | None ->
             finish env' (ECallGeneric (fname, type_args, args')) extras next')
        | Infer_err err -> Infer_err err)
     | RawCallExpr (callee, args) ->
       (match elaborate_raw_expr_fuel fuel' None env _UU03a9_ n _UU03a3_ next
                callee with
        | Infer_ok p ->
          let (p0, next1) = p in
          let (p1, extras1) = p0 in
          let (callee', _UU03a3_1) = p1 in
          let env1 = append_env_fns env extras1 in
          (match go_args fuel' env1 _UU03a3_1 next1 args with
           | Infer_ok p2 ->
             let (p3, next2) = p2 in
             let (p4, extras2) = p3 in
             let (args', _) = p4 in
             let extras = app extras1 extras2 in
             finish (append_env_fns env extras) (ECallExpr (callee', args'))
               extras next2
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
     | RawStruct (sname, lts, tys, fields) ->
       (match go_fields fuel' env _UU03a3_ next fields with
        | Infer_ok p ->
          let (p0, next') = p in
          let (p1, extras) = p0 in
          let (fields', _) = p1 in
          finish (append_env_fns env extras) (EStruct (sname, lts, tys,
            fields')) extras next'
        | Infer_err err -> Infer_err err)
     | RawEnum (enum_name0, variant_name, lts, variant_lts, tys, payloads) ->
       (match go_args fuel' env _UU03a3_ next payloads with
        | Infer_ok p ->
          let (p0, next') = p in
          let (p1, extras) = p0 in
          let (payloads', _) = p1 in
          finish (append_env_fns env extras) (EEnum (enum_name0,
            variant_name, lts, variant_lts, tys, payloads')) extras next'
        | Infer_err err -> Infer_err err)
     | RawMatch (scrut, branches) ->
       (match elaborate_raw_expr_fuel fuel' None env _UU03a9_ n _UU03a3_ next
                scrut with
        | Infer_ok p ->
          let (p0, next1) = p in
          let (p1, extras_scrut) = p0 in
          let (scrut', _UU03a3_1) = p1 in
          let env1 = append_env_fns env extras_scrut in
          (match infer_core_env_state_fuel fuel' env1 _UU03a9_ n _UU03a3_
                   scrut' with
           | Infer_ok p2 ->
             let (t_scrut, _) = p2 in
             (match ty_core t_scrut with
              | TEnum (enum_name0, lts, args) ->
                (match lookup_enum enum_name0 env1 with
                 | Some edef ->
                   let go_branches =
                     let rec go_branches env0 next0 = function
                     | [] -> Infer_ok (([], []), next0)
                     | y :: rest ->
                       let (y0, e_branch) = y in
                       let (variant_name, binders) = y0 in
                       (match lookup_enum_variant variant_name
                                edef.enum_variants with
                        | Some vdef ->
                          (match match_payload_params binders lts args vdef with
                           | Infer_ok ps ->
                             if (&&) (params_names_nodup_b ps)
                                  (ctx_lookup_params_none_b ps _UU03a3_1)
                             then (match elaborate_raw_expr_fuel fuel'
                                           expected env0 _UU03a9_ n
                                           (sctx_add_params ps _UU03a3_1)
                                           next0 e_branch with
                                   | Infer_ok p3 ->
                                     let (p4, next_branch) = p3 in
                                     let (p5, extras_branch) = p4 in
                                     let (e_branch', _) = p5 in
                                     let env_branch =
                                       append_env_fns env0 extras_branch
                                     in
                                     (match go_branches env_branch
                                              next_branch rest with
                                      | Infer_ok p6 ->
                                        let (p7, next_rest) = p6 in
                                        let (rest', extras_rest) = p7 in
                                        Infer_ok (((((variant_name, binders),
                                        e_branch') :: rest'),
                                        (app extras_branch extras_rest)),
                                        next_rest)
                                      | Infer_err err -> Infer_err err)
                                   | Infer_err err -> Infer_err err)
                             else Infer_err ErrContextCheckFailed
                           | Infer_err err -> Infer_err err)
                        | None -> Infer_err (ErrVariantNotFound variant_name))
                     in go_branches
                   in
                   (match go_branches env1 next1 branches with
                    | Infer_ok p3 ->
                      let (p4, next') = p3 in
                      let (branches', extras_branches) = p4 in
                      let extras = app extras_scrut extras_branches in
                      let env' = append_env_fns env extras in
                      (match infer_core_env_state_fuel_elab fuel env'
                               _UU03a9_ n _UU03a3_ (EMatch (scrut',
                               branches')) with
                       | Infer_ok p5 ->
                         let (p6, e_match') = p5 in
                         let (_, _UU03a3_') = p6 in
                         Infer_ok (((e_match', _UU03a3_'), extras), next')
                       | Infer_err err -> Infer_err err)
                    | Infer_err err -> Infer_err err)
                 | None -> Infer_err (ErrEnumNotFound enum_name0))
              | x -> Infer_err (ErrNotAnEnum x))
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
     | RawReplace (p, e1) ->
       let expected_rhs =
         match infer_place_sctx env _UU03a3_ p with
         | Infer_ok t -> Some t
         | Infer_err _ -> None
       in
       (match elaborate_raw_expr_fuel fuel' expected_rhs env _UU03a9_ n
                _UU03a3_ next e1 with
        | Infer_ok p0 ->
          let (p1, next') = p0 in
          let (p2, extras) = p1 in
          let (e1', _) = p2 in
          finish (append_env_fns env extras) (EReplace (p, e1')) extras next'
        | Infer_err err -> Infer_err err)
     | RawAssign (p, e1) ->
       let expected_rhs =
         match infer_place_sctx env _UU03a3_ p with
         | Infer_ok t -> Some t
         | Infer_err _ -> None
       in
       (match elaborate_raw_expr_fuel fuel' expected_rhs env _UU03a9_ n
                _UU03a3_ next e1 with
        | Infer_ok p0 ->
          let (p1, next') = p0 in
          let (p2, extras) = p1 in
          let (e1', _) = p2 in
          finish (append_env_fns env extras) (EAssign (p, e1')) extras next'
        | Infer_err err -> Infer_err err)
     | RawBorrow (rk, p) -> finish env (EBorrow (rk, p)) [] next
     | RawDeref e1 ->
       (match elaborate_raw_expr_fuel fuel' None env _UU03a9_ n _UU03a3_ next
                e1 with
        | Infer_ok p ->
          let (p0, next') = p in
          let (p1, extras) = p0 in
          let (e1', _) = p1 in
          finish (append_env_fns env extras) (EDeref e1') extras next'
        | Infer_err err -> Infer_err err)
     | RawDrop e1 ->
       (match elaborate_raw_expr_fuel fuel' None env _UU03a9_ n _UU03a3_ next
                e1 with
        | Infer_ok p ->
          let (p0, next') = p in
          let (p1, extras) = p0 in
          let (e1', _) = p1 in
          finish (append_env_fns env extras) (EDrop e1') extras next'
        | Infer_err err -> Infer_err err)
     | RawIf (e1, e2, e3) ->
       (match elaborate_raw_expr_fuel fuel' None env _UU03a9_ n _UU03a3_ next
                e1 with
        | Infer_ok p ->
          let (p0, next1) = p in
          let (p1, extras1) = p0 in
          let (e1', _UU03a3_1) = p1 in
          let env1 = append_env_fns env extras1 in
          (match elaborate_raw_expr_fuel fuel' expected env1 _UU03a9_ n
                   _UU03a3_1 next1 e2 with
           | Infer_ok p2 ->
             let (p3, next2) = p2 in
             let (p4, extras2) = p3 in
             let (e2', _) = p4 in
             let env2 = append_env_fns env1 extras2 in
             (match elaborate_raw_expr_fuel fuel' expected env2 _UU03a9_ n
                      _UU03a3_1 next2 e3 with
              | Infer_ok p5 ->
                let (p6, next3) = p5 in
                let (p7, extras3) = p6 in
                let (e3', _) = p7 in
                let extras = app extras1 (app extras2 extras3) in
                finish (append_env_fns env extras) (EIf (e1', e2', e3'))
                  extras next3
              | Infer_err err -> Infer_err err)
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
     | RawClosure (captures, params, ret, body) ->
       (match closure_elab_capture_params env _UU03a9_ _UU03a3_ captures with
        | Infer_ok cap_params ->
          let fname = closure_elab_name next in
          let body_ctx = sctx_of_ctx (params_ctx (app cap_params params)) in
          (match elaborate_raw_expr_fuel fuel' (Some ret) env _UU03a9_ n
                   body_ctx (Big_int_Z.succ_big_int next) body with
           | Infer_ok p ->
             let (p0, next') = p in
             let (p1, body_extras) = p0 in
             let (body', _) = p1 in
             let fdef = { fn_name = fname; fn_lifetimes = n; fn_outlives =
               _UU03a9_; fn_captures = cap_params; fn_params = params;
               fn_ret = ret; fn_body = body'; fn_type_params =
               Big_int_Z.zero_big_int; fn_bounds = [] }
             in
             let env_with_closure =
               append_env_fns env (app body_extras (fdef :: []))
             in
             (match infer_full_env env_with_closure fdef with
              | Infer_ok _ ->
                finish env_with_closure (EMakeClosure (fname, captures))
                  (app body_extras (fdef :: [])) next'
              | Infer_err err -> Infer_err err)
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
     | RawLetRec (captures, rec_fns, body) ->
       (match closure_elab_capture_params env _UU03a9_ _UU03a3_ captures with
        | Infer_ok cap_params ->
          let stubs =
            map (fun rf -> { fn_name = (raw_rec_fn_name rf); fn_lifetimes =
              n; fn_outlives = _UU03a9_; fn_captures = cap_params;
              fn_params = (raw_rec_fn_params rf); fn_ret =
              (raw_rec_fn_ret rf); fn_body = EUnit; fn_type_params =
              Big_int_Z.zero_big_int; fn_bounds = [] }) rec_fns
          in
          let env_stubs = append_env_fns env stubs in
          let go_rec_fns =
            let rec go_rec_fns fuel0 env0 next0 = function
            | [] -> Infer_ok ([], next0)
            | rf :: rest ->
              let body_ctx =
                sctx_of_ctx
                  (params_ctx (app cap_params (raw_rec_fn_params rf)))
              in
              (match elaborate_raw_expr_fuel fuel0 (Some (raw_rec_fn_ret rf))
                       env0 _UU03a9_ n body_ctx next0 (raw_rec_fn_body rf) with
               | Infer_ok p ->
                 let (p0, next1) = p in
                 let (p1, body_extras) = p0 in
                 let (body', _) = p1 in
                 let fdef = { fn_name = (raw_rec_fn_name rf); fn_lifetimes =
                   n; fn_outlives = _UU03a9_; fn_captures = cap_params;
                   fn_params = (raw_rec_fn_params rf); fn_ret =
                   (raw_rec_fn_ret rf); fn_body = body'; fn_type_params =
                   Big_int_Z.zero_big_int; fn_bounds = [] }
                 in
                 let env1 = append_env_fns env0 (app body_extras (fdef :: []))
                 in
                 (match infer_full_env env1 fdef with
                  | Infer_ok _ ->
                    (match go_rec_fns fuel0 env1 next1 rest with
                     | Infer_ok p2 ->
                       let (rest_fns, next2) = p2 in
                       Infer_ok ((app body_extras (fdef :: rest_fns)), next2)
                     | Infer_err err -> Infer_err err)
                  | Infer_err err -> Infer_err err)
               | Infer_err err -> Infer_err err)
            in go_rec_fns
          in
          (match go_rec_fns fuel' env_stubs next rec_fns with
           | Infer_ok p ->
             let (rec_extras, next1) = p in
             let env_rec = append_env_fns env rec_extras in
             (match elaborate_raw_expr_fuel fuel' expected env_rec _UU03a9_ n
                      _UU03a3_ next1 body with
              | Infer_ok p0 ->
                let (p1, next2) = p0 in
                let (p2, body_extras) = p1 in
                let (body', _) = p2 in
                let extras = app rec_extras body_extras in
                finish (append_env_fns env extras) body' extras next2
              | Infer_err err -> Infer_err err)
           | Infer_err err -> Infer_err err)
        | Infer_err err -> Infer_err err)
     | RawCore ecore -> finish env ecore [] next)
     fuel)

(** val elaborate_raw_expr :
    global_env -> outlives_ctx -> Big_int_Z.big_int -> sctx -> raw_expr ->
    (expr * fn_def list) infer_result **)

let elaborate_raw_expr env _UU03a9_ n _UU03a3_ e =
  match elaborate_raw_expr_fuel
          (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) None env
          _UU03a9_ n _UU03a3_ Big_int_Z.zero_big_int e with
  | Infer_ok p ->
    let (p0, _) = p in
    let (p1, extras) = p0 in let (e', _) = p1 in Infer_ok (e', extras)
  | Infer_err err -> Infer_err err

(** val raw_fn_body_ctx : raw_fn_def -> ctx **)

let raw_fn_body_ctx f =
  params_ctx f.raw_fn_params

(** val elaborate_raw_fns_fuel :
    Big_int_Z.big_int -> global_env -> fn_def list -> Big_int_Z.big_int ->
    raw_fn_def list -> (fn_def list * Big_int_Z.big_int) infer_result **)

let rec elaborate_raw_fns_fuel fuel base_env done0 next = function
| [] -> Infer_ok ([], next)
| f :: rest ->
  let env0 = append_env_fns base_env done0 in
  let body_env = global_env_with_local_bounds env0 f.raw_fn_bounds in
  (match elaborate_raw_expr_fuel fuel (Some f.raw_fn_ret) body_env
           f.raw_fn_outlives f.raw_fn_lifetimes
           (sctx_of_ctx (raw_fn_body_ctx f)) next f.raw_fn_body with
   | Infer_ok p ->
     let (p0, next1) = p in
     let (p1, extras) = p0 in
     let (body', _) = p1 in
     let f' = { fn_name = f.raw_fn_name; fn_lifetimes = f.raw_fn_lifetimes;
       fn_outlives = f.raw_fn_outlives; fn_captures = []; fn_params =
       f.raw_fn_params; fn_ret = f.raw_fn_ret; fn_body = body';
       fn_type_params = f.raw_fn_type_params; fn_bounds = f.raw_fn_bounds }
     in
     (match elaborate_raw_fns_fuel fuel base_env
              (app done0 (app extras (f' :: []))) next1 rest with
      | Infer_ok p2 ->
        let (rest', next2) = p2 in
        Infer_ok ((app extras (f' :: rest')), next2)
      | Infer_err err -> Infer_err err)
   | Infer_err err -> Infer_err err)

(** val elaborate_raw_global_env :
    global_env -> raw_fn_def list -> global_env infer_result **)

let elaborate_raw_global_env env fs =
  let stubs = map fn_stub_of_raw fs in
  let base = { env_structs = env.env_structs; env_enums = env.env_enums;
    env_traits = env.env_traits; env_impls = env.env_impls;
    env_local_bounds = []; env_fns = stubs }
  in
  (match elaborate_raw_fns_fuel
           (of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 Nil))))))) base []
           Big_int_Z.zero_big_int fs with
   | Infer_ok p ->
     let (fns, _) = p in
     Infer_ok { env_structs = env.env_structs; env_enums = env.env_enums;
     env_traits = env.env_traits; env_impls = env.env_impls;
     env_local_bounds = []; env_fns = fns }
   | Infer_err err -> Infer_err err)
