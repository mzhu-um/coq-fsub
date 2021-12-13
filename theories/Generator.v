From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.

Fixpoint count_var (E : env) : nat :=
  match E with
  | empty => 0
  | evar E _ => S (count_var E)
  | ebound E _ => (count_var E)
  end.

Definition gen_typ_from_env (E : env) : G (option typ) :=
  match count_tvar E with
  | O => ret None
  | S n => n' <- choose(0, n);; ret (Some (tvar n'))
  end.

Definition gen_base_typ (E : env) : G typ:=
  oT <- gen_typ_from_env E;;
  match oT with
  | None => ret top
  | Some T => elems [top ; T]
  end.


(** ** Type Generator *)
Fixpoint gen_typ (n : nat) (E : env) : G typ :=
  match n with
  | O => gen_base_typ E
  | S n =>
      let gen_arrow :=
        T1 <- gen_typ n E ;;
        T2 <- gen_typ n (evar E T1) ;;
        ret (arrow T1 T2) in
      let gen_all :=
        T1 <- gen_typ n E ;;
        T2 <- gen_typ n (ebound E T1) ;;
        ret (all T1 T2) in
      oneOf [gen_arrow ; gen_all ; gen_base_typ E]
  end.

Sample (gen_typ 3 empty).

(** Try to generate something, if it fails then use [top] *)
Definition gen_top_comb (g : G (option typ)) : G (option typ) := 
  a <- g ;;
  match a with
  | Some T => returnGen a
  | None => returnGen (Some top)
  end.

(** There's no term of type [top]. Thus, [top] should only be generated 
    in parametric type lambda [all].
  *)   
Fixpoint gen_concrete_typ (n : nat) (E : env) : G (option typ) :=
  match n with
  | O => gen_typ_from_env E
  | S n =>
      (** Chances are that there's is no enough [tvar] to generate [arrow].
       *)
      let gen_arrow :=
        T1 <- gen_concrete_typ n E ;;
        T2 <- gen_concrete_typ n (evar E T1) ;;
        ret (arrow T1 T2) in
      let gen_all :=
        T1 <- gen_top_comb (gen_concrete_typ n E) ;;
        T2 <- gen_concrete_typ n (ebound E T1) ;;
        ret (all T1 T2) in
      backtrack [(1, gen_arrow) ; (2, gen_all) ; (1, gen_typ_from_env E)]
  end.


Fixpoint tlift (X : nat) (T : typ) {struct T} : typ :=
  match T with
  | tvar Y      => tvar (Y + X) (* tvar (if le_gt_dec X Y then 1 + Y else Y) *)
  | top         => top
  | arrow T1 T2 => arrow (tlift X T1) (tlift X T2)
  | all T1 T2   => all (tlift X T1) (tlift (1 + X) T2)
  end.

Fixpoint get_bound_vars (T : typ) (n m : nat) (E : env) : list term :=
  match E with
  | empty => []
  | ebound E _ => get_bound_vars T n (S m) E
  | evar E T' => 
      let T'' := tlift m T' in 
      let rst := get_bound_vars T (S n) m E in 
      if T = T'' ? then (var n) :: rst else rst
  end.

Definition gen_bound_vars (T : typ) (E : env) : G (option term) :=
  elems_ None (map Some (get_bound_vars T 0 0 E)).


Fixpoint gen_concrete_base_typ (E : env) (T : typ) : G (option term) :=
  let g : G (option term) :=
    match T with
    | arrow T1 T2 =>
        liftM (abs T1) (gen_concrete_base_typ (evar E T1) T2)
    | all T1 T2 =>
        liftM (tabs T1)
              (gen_concrete_base_typ (ebound E T1) T2)
    | _ => ret None
    end
  in     
  backtrack [ (1, gen_bound_vars T E) ;
              (1, g) ].


Compute (show (all top (all top
                            (arrow (tvar 0) (arrow (tvar 1) (tvar 0)))))) .
(** 
    {∀Top . {∀Top . (<0> -> (<1> -> <0>))}}
 *)
Sample (gen_concrete_base_typ
          empty
          (all top (all top (arrow (tvar 0) (arrow (tvar 1) (tvar 0)))))).

(** Expected: 
   (Λ Top. (Λ Top. (λ : <0>. (λ : <1>. [id 1]))))
 *)

(** 
    (Λ Top. (Λ Top. (λ : <0>. (λ : <1>. [id 1]))))
 *)

Compute (show
        (all top (arrow (tvar 0)
                          (all top (arrow (tvar 0) (tvar 0)))))).

Sample (gen_concrete_base_typ
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


Sample (gen_concrete_base_typ
          empty
          (all top (arrow (tvar 0)
                          (all top (arrow (tvar 0) (tvar 1)))))).

(**
    Only 
      [(Λ Top. (λ : <0>. (Λ Top. (λ : <0>. [id 1]))))]
    is correct.
 *)

Compute (show (all top (arrow (arrow (tvar 0) (tvar 0))
                              (all top (arrow (tvar 0)
                                              (arrow (tvar 0) (tvar 0))))))).

Sample (gen_concrete_base_typ
          empty
          (all top (arrow ((arrow (tvar 0) (tvar 0)))
                          (all top (arrow (tvar 0)
                                          (arrow (tvar 1) (tvar 1))))))).
(**
   (Λ Top. (λ : (<0> -> <0>). (Λ Top. (λ : <0>. [id 1]))))

   (Λ Top. (λ : (<0> -> <0>). (Λ Top. (λ : <0>. (λ : <1>. [id 0])))))     
*)

(** Generate terms from concrete types *)
Fixpoint gen_concrete_term (n : nat) (E : env) (T : typ) :  :=
  match n with
  | O => gen_concrete_base_typ
  | S n =>
      match T with
      | tvar n => gen_bound_vars
      
Fixpoint gen_sup_typ (fuel : nat) (E : env) (T : typ) : G typ :=

