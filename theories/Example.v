From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.
From FSUB Require Import Generator.


Eval cbv in (show (all top (all top
                                (arrow (tvar 0) (arrow (tvar 1) (tvar 0)))))) .
(** 
    {∀Top . {∀Top . (<0> -> (<1> -> <0>))}}
 *)
Sample (gen_exact_term0
          empty
          (all top (all top (arrow (tvar 0) (arrow (tvar 1) (tvar 0)))))).

(** Expected: 
   (Λ Top. (Λ Top. (λ : <0>. (λ : <1>. [id 1]))))
 *)

(** 
    (Λ Top. (Λ Top. (λ : <0>. (λ : <1>. [id 1]))))
 *)

Eval cbv in (show
               (all top (arrow (tvar 0)
                               (all top (arrow (tvar 0) (tvar 0)))))).

Sample (gen_exact_term0
          empty
          (all top (arrow (tvar 0)
                          (all top (arrow (tvar 0) (tvar 0)))))).
(** 
    (Mutant: Lift tvar when get_bound)

    For type
    {∀Top . (<0> -> {∀Top . (<0> -> <0>)})},

    without lifting: 

    [(Λ Top. (λ : <0>. (Λ Top. (λ : <0>. [id 0]))))]
    [(Λ Top. (λ : <0>. (Λ Top. (λ : <0>. [id 1]))))]

    Only 
      [(Λ Top. (λ : <0>. (Λ Top. (λ : <0>. [id 0]))))]
    is correct.
 *)


Sample (gen_exact_term0
          empty
          (all top (arrow (tvar 0)
                          (all top (arrow (tvar 0) (tvar 1)))))).

(**
    Only 
      [(Λ Top. (λ : <0>. (Λ Top. (λ : <0>. [id 1]))))]
    is correct.
 *)

Eval cbv in (show (all top (arrow (arrow (tvar 0) (tvar 0))
                                  (all top (arrow (tvar 0)
                                                  (arrow (tvar 0) (tvar 0))))))).

Sample (gen_exact_term0
          empty
          (all top (arrow ((arrow (tvar 0) (tvar 0)))
                          (all top (arrow (tvar 0)
                                          (arrow (tvar 1) (tvar 1))))))).
(**
   (Λ Top. (λ : (<0> -> <0>). (Λ Top. (λ : <0>. [id 1]))))

   (Λ Top. (λ : (<0> -> <0>). (Λ Top. (λ : <0>. (λ : <1>. [id 0])))))     
 *)



Sample (gen_exact_tvar0
          (ebound (ebound (ebound (ebound empty top) top) top) top)). 


Sample (gen_exact_typ0
          (ebound
             (evar
                (ebound
                   (evar
                      (ebound
                         (evar
                            empty
                            (tvar 0))
                         top)
                      (tvar 1))
                   top)
                (tvar 0))
             top)). 


