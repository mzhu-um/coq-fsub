From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.
From FSUB Require Import Reduction.

Fixpoint count_var (E : env) : nat :=
  match E with
  | empty => 0
  | evar E _ => S (count_var E)
  | ebound E _ => (count_var E)
  end.

Fixpoint tlift (T : typ) (m : nat) :=
  match m with
  | O => T
  | S m => tlift (tshift 0 T) m
  end.

(** ** Generate (Almost) SystemF *)
Definition gen_top_comb (g : G (option typ)) : G (option typ) := 
  a <- g ;;
  match a with
  | Some T => returnGen a
  | None => returnGen (Some top)
  end.

Definition gen_exact_tvar0' (E : env) : list (G typ) :=
  match count_tvar E with
  | O => []
  | S n => [n' <- choose(0, n);; ret (tvar n')]
  end.

Definition gen_exact_tvar0 (E : env) : (G (option typ)) :=
  oneOf_ (ret None) (map (fmap Some) (gen_exact_tvar0' E)).

Fixpoint gen_exact_var0' (E : env) : list typ :=
  match E with
  | empty => []
  | ebound E _ => map (tshift 0) (gen_exact_var0' E)
  | evar E T => T :: (gen_exact_var0' E)
  end.

Definition gen_exact_from_var0' (E : env) : list (G typ) :=
  map ret (gen_exact_var0' E).

Definition gen_exact_from_var0 (E : env) : (G (option typ)) :=
  oneOf_ (ret None) (map (fmap Some) (gen_exact_from_var0' E)).

(* There must be another way to write this *)
Definition gen_exact_typ0'  (E : env) : G typ :=
  let gs' := map (fun g => T <- g;; returnGen (arrow T T))
                (gen_exact_tvar0' E) in
  let g'' := returnGen (all top (arrow (tvar 0) (tvar 0))) in
  oneOf_ g'' (gs' ++ (gen_exact_from_var0' E)).

(** There's no term of type [top]. Thus, [top] should only be generated 
    in parametric type lambda [all].
  *)   

Definition gen_exact_typ0 (E : env) : G (option typ) :=
  fmap Some (gen_exact_typ0' E). 

Fixpoint gen_exact_typ (n : nat) (E : env) : G (option typ) :=
  match n with
  | O => gen_exact_typ0 E
  | S n =>
      let gen_all :=
        T1 <- oneOf [ret top;   (* allow top in TVar *)
                     gen_exact_typ (pred (pred n)) E] ;;
        T2 <- gen_exact_typ n (ebound E T1) ;;
        ret (all T1 T2) in
      let gen_arrow :=
        T1 <- oneOf_ (gen_exact_typ (pred (pred n)) E)
                     ((gen_exact_typ (pred (pred n)) E)
                        :: (map (fmap Some) (gen_exact_tvar0' E)));;
        T2 <- gen_exact_typ n (evar E T1) ;;
        ret (arrow T1 T2) in
      (** use [backtrack] since [gen_arrow] could fail *)
      backtrack [(5, gen_arrow) ; (5, gen_all) ; (1, gen_exact_typ0 E)]
  end.

Sample (gen_exact_typ 3 empty).

Fixpoint get_bound_vars (T : typ) (n m : nat) (E : env) : list term :=
  match E with
  | empty => []
  | ebound E _ => get_bound_vars T n (S m) E
  | evar E T' => 
      let rst := get_bound_vars T (S n) m E in 
      if T = (tlift T' m) ? then (var n) :: rst else rst
  end.

Definition gen_bound_vars' (T : typ) (E : env) : list (G term) :=
  map ret (get_bound_vars T 0 0 E).

Definition gen_bound_vars (T : typ) (E : env) : G (option term) :=
  elems_ None (map Some (get_bound_vars T 0 0 E)).

(* FIXME : When meet [tvar n], resolve the type recursively *)
Fixpoint gen_exact_term0 (E : env) (T : typ) : G (option term) :=
  let g : (G (option term)) :=
    match T with
    | arrow T1 T2 =>
        liftM (abs T1) (gen_exact_term0 (evar E T1) T2)
    | all T1 T2 =>
        liftM (tabs T1)
              (gen_exact_term0 (ebound E T1) T2)
    | _ => ret None
    end
  in     
  backtrack [(1, g); (1, (gen_bound_vars T E))].

Fixpoint gen_ftvar0 (n : nat) (E : env) (acc : list typ) : list typ :=
  match E with
  | empty => acc
  | evar E _ => gen_ftvar0 n E acc
  | ebound E _ => gen_ftvar0 (S n) E ((tvar n) :: acc)
  end.

Definition gen_ftvar (E : env) : G (option typ) :=
  elems_ None (map Some (gen_ftvar0 0 E [])).

(** Generate terms from exact types *)
Fixpoint gen_exact_term (n : nat) (E : env) (T : typ) : G (option term) :=
  match n with
  | O => gen_exact_term0 E T
  | S n =>
      let g0 := gen_exact_term0 E T in
      let g1 := 
        match T with
        | arrow T1 T2 =>
            liftM (fun t2 => (abs T1 t2))
                  (gen_exact_term n (evar E T1) T2)
        | all T1 T2 => 
            liftM (fun t2 => (tabs T1 t2))
                  (gen_exact_term n (ebound E T1) T2)
        | _ => returnGen None
        end in
      (** Generate App *)
      let g2 :=
        T1 <- gen_exact_typ (pred n) E;; (* include more context aware generation? *)
        (* t1 <- gen_exact_term n (evar E T1) T;; *)
        t1 <- gen_exact_term (pred n) E (arrow T1 T);;
        t2 <- gen_exact_term n E T1;;
        (* returnGen (Some (app (abs T1 t1) t2)) *)
        returnGen (Some (app t1 t2))
      in
      (** Generate TApp *)
      let g3 :=
        T1 <- gen_exact_typ (pred n) E;; 
        t1 <- gen_exact_term n E (all T1 (tshift 0 T));;
        returnGen (Some (tapp t1 T1))
      in backtrack [(1, g0); (1, g1); (1, g2); (1, g3)]
  end
.      

Definition gen_exact (n : nat) : G (option term) :=
  T <- gen_exact_typ n empty;;
  gen_exact_term n empty T.

Sample (gen_exact 5).

Definition type_check' :=
  fun E t T => type_check E t T 100. 
Definition get_typ' :=
  fun E t => get_typ E t 100. 

(** ** Generate Subtype *)
Definition sub_check' :=
  fun e T1 T2 => sub_check e T1 T2 20. 

(* TODO : Abstraction *)
Definition gen_sub_tvar' (E : env) (T2 : typ) : list typ :=
  let n := count_tvar E in
  let fix f n1 :=
    match n1 with
    | O => []
    | S n1 => 
        match get_bound E n1 with
        | None => []
        | Some T1 => 
            let T' := match sub_check' E T1 T2 with
                      | Result true => [T1]
                      | _ => []
                      end in
            T' ++ (f n1)
        end
    end in
  f n.


Definition gen_sub_tvar (E : env) (T2 : typ) : G typ :=
  elems_ T2 (gen_sub_tvar' E T2). 

Definition gen_sup_tvar' (E : env) (n1 : nat) : list typ :=
  match get_bound E n1 with
  | None => []
  | Some T1 => 
      let n := count_tvar E in
      let fix f n2 :=
        match n2 with
        | O => []
        | S n2 => 
            match get_bound E n2 with
            | None => []
            | Some T2 => 
                let T' := match sub_check' E T1 T2 with
                          | Result true => [tvar n1]
                          | _ => []
                          end in
                T' ++ (f n2)
            end
        end in
      f n
  end.


Definition gen_sup_tvar (E : env) (n1 : nat) : G typ :=
  elems_ (tvar n1) (gen_sup_tvar' E n1). 

Fixpoint gen_sub_typ (n : nat) (E : env) (T : typ) : G typ :=
  match n with
  | O => ret T                  (** [sub] is reflexive *)
  | S n =>
      let g1 :=
        match T with
        | top =>
            (** any <: [top] *)
            T1 <- gen_exact_typ n E ;;
            match T1 with
            | Some T1 => ret T1
            | None => ret top
            end
        | tvar n => ret (tvar n)
        | arrow T1 T2 =>
            (** [S1] :> [T1] -> 
              [S2] <: [T2] ->
              arrow [S1] [S2] <: arrow [T1] [T2] 
             *)
            S1 <- gen_sup_typ n E T1;;
            S2 <- gen_sub_typ n E T2;;
            ret (arrow S1 S2)
        | all T1 T2 =>
            S1 <- gen_sup_typ n E T1;;
            S2 <- gen_sub_typ n (ebound E T1) T2;;
            ret (all S1 S2)
        end in
      let g2 := map ret (gen_sub_tvar' E T) in
      oneOf_ (ret T) ((ret T) :: g1 :: g2)
  end
with
gen_sup_typ (n : nat) (E : env) (T : typ) : G typ :=
  match n with
  | O => ret T                  (** [sup] is reflexive *)
  | S n =>
      let g1 :=
        match T with
        | top => ret top        (** [top] is the top *)
        | tvar n => gen_sup_tvar E n
        | arrow T1 T2 =>
            S1 <- gen_sub_typ n E T1;;
            S2 <- gen_sup_typ n E T2;;
            ret (arrow S1 S2)
        | all T1 T2 =>
            S1 <- gen_sub_typ n E T1;;
            S2 <- gen_sup_typ n (ebound E T1) T2;;
            ret (all S1 S2)
        end in
      oneOf [ret T ; g1]
  end
.

(** ** Generate SystemF Sub *)
(** Idea0: Fixpoint iteration *)

Fixpoint multistep {A}
           (n : nat)
           (step : A -> option A)
           (t : A)
           (is_value : A -> bool) : @result (bool * A) :=
  match n with
  | O => OutOfFuel
  | S n =>
      match step t with
      | Some t => multistep n step t is_value
      | None => Result ((is_value t), t)
      end
  end.

(** TODO : More Type-Parameter-Aware Term Generation
    
    Λ<:top. λ<:<0>. <: (<0> -> <0>). λ <:<0>. [0] [1]
 *)
