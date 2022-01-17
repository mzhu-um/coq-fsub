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


(*  *)

Example ex_sub1_typ :=
  (all top
       (arrow (tvar 0)
              (all top 
                   (arrow (tvar 0)
                          (all (arrow (tvar 0) (tvar 1))
                               (arrow (tvar 0)
                                      (all (tvar 0)
                                           (arrow (tvar 0)
                                                  (arrow (tvar 2) (tvar 3)))))))))). 

Eval cbv in show ex_sub1_typ.


Fixpoint get_env (t : term) : env :=
  match t with
  | abs T t => evar (get_env t) T
  | tabs T t => ebound (get_env t) T
  | _ => empty
  end.

Example ex_sub1_tc :=
  (fun x =>
     (tabs top
           (abs (tvar 0)
                (tabs top 
                      (abs (tvar 0)
                           (tabs (arrow (tvar 0) (tvar 1))
                                 (abs (tvar 0)
                                      (tabs (tvar 0)
                                            (abs (tvar 0) x))))))))).

(** [gen_sub_term 0 empty ex_sub1_typ] 
    is capable of generating all 3 following variants *)
Sample (gen_sub_term 0 empty ex_sub1_typ).

Example ex_sub1_t1 :=
  ex_sub1_tc (var 0).

Example ex_sub1_t2 :=
  ex_sub1_tc (var 1).

Example ex_sub1_t3 :=
  ex_sub1_tc (abs (tvar 2) (var 4)).

Eval cbv in type_check empty ex_sub1_t3 ex_sub1_typ 100.
Eval cbv in type_check empty ex_sub1_t2 ex_sub1_typ 100.
Eval cbv in type_check empty ex_sub1_t1 ex_sub1_typ 100.

(** {∀{∀Top . (<0> -> <0>)} . (<0> -> <0>)} *)
Example ex_t1 :=
  all (all top (arrow (tvar 0) (tvar 0))) (arrow (tvar 0) (tvar 0)). 

(** {∀Top . (<0> -> <0>)} *)
Example ex_t2 :=
  (all top (arrow (tvar 0) (tvar 0))). 


(** [t2] <: [t1] *)
Eval cbv in sub_check' empty ex_t2 ex_t1.

(** test [get_typ]
    ((λ : {∀{∀Top . (<0> -> <0>)} . (<0> -> <0>)}.
      (Λ {∀Top . (<0> -> <0>)}. (λ : <0>. [id 0])))
     (Λ Top. (λ : <0>. [id 0]))) 
*)
Example ex_tm1 :=
  tabs top (abs (tvar 0) (var 0)).

Eval cbv in get_typ empty ex_tm1 10.

Example ex_tm2 :=
  tabs (all top (arrow (tvar 0) (tvar 0))) (abs (tvar 0) (var 0)).

Eval cbv in get_typ empty ex_tm2 10.

Example ex_tm3 :=
  app (abs ex_t1 ex_tm2) ex_tm1.

Eval cbv in (get_typ empty (abs ex_t1 ex_tm2) 10).

Eval cbv in get_typ empty ex_tm3 10.

(** ** More Subtype Examples *)
Example ex_sub2_ty1 :=
  all top (arrow (tvar 0) (tvar 0)). 
Example ex_sub2_ty2 :=
  all (all top (arrow (tvar 0) (tvar 0))) (arrow (tvar 0) (tvar 0)). 

Eval cbv in sub_check' empty ex_sub2_ty1 ex_sub2_ty2. 
(* 
Eval cbv in sub_check' empty
                       (arrow ex_sub2_ty2 ex_sub2_ty2)
                       (arrow ex_sub2_ty1 ex_sub2_ty1).
 *)

(** ** Subsitution Related Examples *)
Definition ex_subst_sub t := all top (all top t).

Example ex_subst_ty1 :=
  ex_subst_sub
    (arrow (tvar 0) (arrow (tvar 1) (arrow (tvar 1) (tvar 0)))).

Sample (gen_exact_term (measure_max_typ ex_subst_ty1) empty ex_subst_ty1).

Example ex_subst_tm1 :=
  let f1 t := tabs top (tabs top t) in
  let f2 t := (abs (tvar 0) (abs (tvar 1) t)) in
  let t3 := (app (abs (tvar 0) (abs (tvar 1) (var 3))) (var 1)) in
  f1 (f2 t3).

Example id_est1 : (G (option term)) :=
  ret ex_subst_tm1.
Example id_esty1 : (G (option typ)) :=
  ret ex_subst_ty1.

Eval cbv in get_typ' empty ex_subst_tm1.
Eval cbv in type_check' empty ex_subst_tm1 ex_subst_ty1.


Example ty2 :=
  all (all top top) (all (tvar 0) (all (tvar 1) top)). 

Example ty2' :=
  (all (tvar 0) (all (tvar 1) top)).

Eval cbv in fetch_candidate_typs ty2'.


Example sub1 :
  sub empty
      (all top (all (all (tvar 0) (tvar 1)) top))
      (all top (all (all (tvar 0) (tvar 0)) top)). 
Proof with intuition.
  constructor. constructor... cbn; apply I.
  constructor.
  - constructor. constructor... cbn...
    eapply SA_Trans_TVar; cbn...
    apply SA_Refl_TVar... cbn... congruence.
  - constructor... cbn... congruence. congruence.
Qed.

Example sub2 :
  sub empty
      (all top (all (tvar 0) (arrow (tvar 1) (tvar 1))))
      (all top (all (tvar 0) (arrow (tvar 0) (tvar 1)))).
Proof with easy.
  constructor. constructor...
  constructor. constructor...
  constructor.
  eapply SA_Trans_TVar. cbn. reflexivity.
  apply SA_Refl_TVar...
  constructor... 
Qed.
