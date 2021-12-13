
val add : int -> int -> int

val sub : int -> int -> int

val lt_eq_lt_dec : int -> int -> bool option

val le_gt_dec : int -> int -> bool

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

val tshift : int -> typ -> typ

val shift : int -> term -> term

val shift_typ : int -> term -> term

val tsubst : typ -> int -> typ -> typ

val subst : term -> int -> term -> term

val subst_typ : term -> int -> typ -> term

type ctx =
| C_hole
| C_appfun of ctx * term
| C_apparg of term * ctx
| C_typefun of ctx * typ

val ctx_app : ctx -> term -> term

val dc_value : term -> bool

val ctx_inj : term -> (ctx * term) option

val step : term -> term option
