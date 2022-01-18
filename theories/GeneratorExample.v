From FSUB Require Import
     QCLibs
     FSub
     Decidable
     GeneratorSub.

(** Motivation [fetch_good_typs] : 
    ∀ top. ∀ <0>. ∀ <0>. <0> -> ◻ *)
Example env_with_sub :=
  (evar
     (ebound
        (ebound
           (ebound empty
                   top)
           (tvar 0))
        (tvar 1))
     (tvar 0)). 

Eval cbv in fetch_var_typs env_with_sub. 
Eval cbv in fetch_good_typs env_with_sub. 


Example repl_ty :=
  (arrow (tvar 0) (arrow (tvar 1) (all top (arrow (tvar 1) (tvar 0))))).

Sample (gen_replace repl_ty).

