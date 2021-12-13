From FSUB Require Import FSub.

(** ** Utils for QuickChick *)
Instance Dec_eq_opt (A : Type) (m n : option A)
         `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.

Inductive result {X : Type} : Type :=
| Result (v : X)
| OutOfFuel
.


