
(** val add : int -> int -> int **)

let rec add = (+)

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Pervasives.max 0 (n-m)

(** val lt_eq_lt_dec : int -> int -> bool option **)

let rec lt_eq_lt_dec = fun n m -> if n>m then None else Some (n<m)

(** val le_gt_dec : int -> int -> bool **)

let le_gt_dec = (<=)

type typ =
| Tvar of int
| Top
| Arrow of typ * typ
| All of typ * typ

type term =
| Var of int
| Abs of typ * term
| App of term * term
| Tabs of typ * term
| Tapp of term * typ

(** val tshift : int -> typ -> typ **)

let rec tshift x = function
| Tvar y -> Tvar (if le_gt_dec x y then add (Pervasives.succ 0) y else y)
| Top -> Top
| Arrow (t1, t2) -> Arrow ((tshift x t1), (tshift x t2))
| All (t1, t2) -> All ((tshift x t1), (tshift (add (Pervasives.succ 0) x) t2))

(** val shift : int -> term -> term **)

let rec shift x = function
| Var y -> Var (if le_gt_dec x y then add (Pervasives.succ 0) y else y)
| Abs (t1, t2) -> Abs (t1, (shift (add (Pervasives.succ 0) x) t2))
| App (t1, t2) -> App ((shift x t1), (shift x t2))
| Tabs (t1, t2) -> Tabs (t1, (shift x t2))
| Tapp (t1, t2) -> Tapp ((shift x t1), t2)

(** val shift_typ : int -> term -> term **)

let rec shift_typ x = function
| Var y -> Var y
| Abs (t1, t2) -> Abs ((tshift x t1), (shift_typ x t2))
| App (t1, t2) -> App ((shift_typ x t1), (shift_typ x t2))
| Tabs (t1, t2) -> Tabs ((tshift x t1), (shift_typ (add (Pervasives.succ 0) x) t2))
| Tapp (t1, t2) -> Tapp ((shift_typ x t1), (tshift x t2))

(** val tsubst : typ -> int -> typ -> typ **)

let rec tsubst t x t' =
  match t with
  | Tvar y ->
    (match lt_eq_lt_dec y x with
     | Some s -> if s then Tvar y else t'
     | None -> Tvar (sub y (Pervasives.succ 0)))
  | Top -> Top
  | Arrow (t1, t2) -> Arrow ((tsubst t1 x t'), (tsubst t2 x t'))
  | All (t1, t2) -> All ((tsubst t1 x t'), (tsubst t2 (add (Pervasives.succ 0) x) (tshift 0 t')))

(** val subst : term -> int -> term -> term **)

let rec subst t x t' =
  match t with
  | Var y ->
    (match lt_eq_lt_dec y x with
     | Some s -> if s then Var y else t'
     | None -> Var (sub y (Pervasives.succ 0)))
  | Abs (t1, t2) -> Abs (t1, (subst t2 (add (Pervasives.succ 0) x) (shift 0 t')))
  | App (t1, t2) -> App ((subst t1 x t'), (subst t2 x t'))
  | Tabs (t1, t2) -> Tabs (t1, (subst t2 x (shift_typ 0 t')))
  | Tapp (t1, t2) -> Tapp ((subst t1 x t'), t2)

(** val subst_typ : term -> int -> typ -> term **)

let rec subst_typ t x t0 =
  match t with
  | Var y -> Var y
  | Abs (t1, t2) -> Abs ((tsubst t1 x t0), (subst_typ t2 x t0))
  | App (e1, e2) -> App ((subst_typ e1 x t0), (subst_typ e2 x t0))
  | Tabs (t1, e1) -> Tabs ((tsubst t1 x t0), (subst_typ e1 (add (Pervasives.succ 0) x) (tshift 0 t0)))
  | Tapp (e1, t2) -> Tapp ((subst_typ e1 x t0), (tsubst t2 x t0))

type ctx =
| C_hole
| C_appfun of ctx * term
| C_apparg of term * ctx
| C_typefun of ctx * typ

(** val ctx_app : ctx -> term -> term **)

let rec ctx_app c t =
  match c with
  | C_hole -> t
  | C_appfun (c', t') -> App ((ctx_app c' t), t')
  | C_apparg (t', c') -> App (t', (ctx_app c' t))
  | C_typefun (c', t0) -> Tapp ((ctx_app c' t), t0)

(** val dc_value : term -> bool **)

let dc_value = function
| Abs (_, _) -> true
| Tabs (_, _) -> true
| _ -> false

(** val ctx_inj : term -> (ctx * term) option **)

let ctx_inj = function
| App (t1, t2) ->
  let filtered_var = dc_value t1 in
  if filtered_var then Some ((C_apparg (t1, C_hole)), t2) else Some ((C_appfun (C_hole, t2)), t1)
| Tapp (t1, t2) -> Some ((C_typefun (C_hole, t2)), t1)
| _ -> None

(** val step : term -> term option **)

let rec step x = match x with
| App (t0, t2) ->
  (match t0 with
   | Abs (_, t12) ->
     if dc_value t2
     then Some (subst t12 0 t2)
     else let filtered_var = ctx_inj x in
          (match filtered_var with
           | Some p ->
             let (c', t') = p in
             let filtered_var0 = step t' in
             (match filtered_var0 with
              | Some t'' -> Some (ctx_app c' t'')
              | None -> None)
           | None -> None)
   | _ ->
     let filtered_var = ctx_inj x in
     (match filtered_var with
      | Some p ->
        let (c', t') = p in
        let filtered_var0 = step t' in (match filtered_var0 with
                                        | Some t'' -> Some (ctx_app c' t'')
                                        | None -> None)
      | None -> None))
| Tapp (t0, t2) ->
  (match t0 with
   | Tabs (_, t12) -> Some (subst_typ t12 0 t2)
   | _ ->
     let filtered_var = ctx_inj x in
     (match filtered_var with
      | Some p ->
        let (c', t') = p in
        let filtered_var0 = step t' in (match filtered_var0 with
                                        | Some t'' -> Some (ctx_app c' t'')
                                        | None -> None)
      | None -> None))
| _ ->
  let filtered_var = ctx_inj x in
  (match filtered_var with
   | Some p ->
     let (c', t') = p in
     let filtered_var0 = step t' in (match filtered_var0 with
                                     | Some t'' -> Some (ctx_app c' t'')
                                     | None -> None)
   | None -> None)
