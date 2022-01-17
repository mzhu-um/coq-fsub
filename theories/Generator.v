From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.
From FSUB Require Import Reduction.

(** * Generator: System F<: Random Generators *)

Fixpoint tlift (T : typ) (m : nat) :=
  match m with
  | O => T
  | S m => tlift (tshift 0 T) m
  end.

(** ** Generate (Almost) SystemF *)
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
                     gen_exact_typ n E] ;;
        T2 <- gen_exact_typ n (ebound E T1) ;;
        ret (all T1 T2) in
      let gen_arrow :=
        T1 <- oneOf_ (gen_exact_typ n E)
                     ((gen_exact_typ n E)
                        :: (map (fmap Some) (gen_exact_tvar0' E)));;
        T2 <- gen_exact_typ n (evar E T1) ;;
        ret (arrow T1 T2) in
      (** use [backtrack] since [gen_arrow] could fail *)
      backtrack [(5, gen_arrow) ; (5, gen_all) ; (1, gen_exact_typ0 E)]
  end.

(*
Definition fetch_tvar_typs (E : env) :=
  let ntvar := count_tvar E in
  let fix f n :=
    match n with
    | O => []
    | S n =>
        match get_bound E n with
        | Some T => [T]
        | None => []
        end ++ (f n)
    end in
  f ntvar.
*)
   


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
        T1 <- gen_exact_typ n E;;
        t1 <- gen_exact_term n E (arrow T1 T);;
        t2 <- gen_exact_term n E T1;;
        returnGen (Some (app t1 t2))
      in
      (** Generate TApp *)
      let g3 :=
        T1 <- gen_exact_typ n E;; 
        t1 <- gen_exact_term n E (all T1 (tshift 0 T));;
        returnGen (Some (tapp t1 T1))
      in backtrack [(1, g0); (1, g1); (1, g2); (1, g3)]
  end
.      

Definition gen_exact (n : nat) : G (option term) :=
  T <- gen_exact_typ n empty;;
  gen_exact_term n empty T.

(* Sample (gen_exact 5). *)


(** ** Generate Subtype *)

(** Find out super or sub type of the given [typ] in the environment *)
Definition find_sub_tvar  
           (E : env) (T2 : typ) : list typ :=
  let n := count_tvar E in
  let fix f n1 :=
    match n1 with
    | O => []
    | S n1 => 
        match get_bound E n1 with
        | None => []
        | Some T1 => 
            let T' := match sub_check' E T1 T2 with
                      | true => [T1]
                      | _ => []
                      end in
            T' ++ (f n1)
        end
    end in
  f n.
  
Definition gen_sub_tvar (E : env) (T2 : typ) : G typ :=
  elems_ T2 (find_sub_tvar E T2). 

Definition find_sup_tvar (E : env) (n1 : nat) : list typ :=
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
                          | true => [tvar n1]
                          | _ => []
                          end in
                T' ++ (f n2)
            end
        end in
      f n
  end.

Definition gen_sup_tvar (E : env) (n1 : nat) : G typ :=
  elems_ (tvar n1) (find_sup_tvar E n1). 

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
      let g2 := map ret (find_sub_tvar E T) in
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

Definition c_gen_sub_typ g n E : G (option typ) :=
  oT <- (g n E) ;;
  match oT with
  | None => ret None 
  | Some T => liftM Some (gen_sub_typ n E T)
  end.

Definition c_gen_sup_typ g n E : G (option typ) :=
  oT <- (g n E) ;;
  match oT with
  | None => ret None 
  | Some T => liftM Some (gen_sup_typ n E T)
  end.

      
(** ** Generate System F <:
    
    - Generate a type to be used as the super type of the program
    - Widen the type of an exact type step by step
*)

(** Generate a [typ] *)
(** Reworked [gen_typ] : allow bare [top]s and [arrow]s *)
Definition fetch_var_typs (E : env) : list typ :=
  let nvar := count_var E in
  let fix f n :=
    match n with
    | O => []
    | S n =>
        match get_var E n with
        | Some T => [T]
        | None => []
        end ++ (f n)
    end in
  f nvar.



(** for each [var] in the env, "upcasts" can be done to it *)
Definition fetch_good_typs (E : env) : list typ :=
  let vars := fetch_var_typs E in
  let ntvars :=  count_tvar E in
  let fix f n :=
    match n with
    | O => []
    | S n => (tvar n) :: f n
    end in
  let tvars := f ntvars in 
  List.fold_right
    (fun v acc =>
       acc ++ match v with
              | tvar n =>
                  v ::          (** bound var itself *)
                    match get_bound E n with
                    | Some T => (** upcasts to its super type *)
                        List.filter (sub_check' E T) tvars
                    | None => []
                    end
              (** More can be done here: analyze structure of the typ *)
              | _ => [v]
              end)
    [] vars.
    
(** Motivation: 

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

Definition gen_typ0 (E : env) (r : bool) : G typ := 
  if r
  then                          (** Restricted: must be sub bound [var] *)
    freq [(1, ret top);
          let Ts := fetch_good_typs E in
          (List.length Ts, elems_ top Ts)]
  else                          (** Any bound [var] or [tvar] suffice *)
    freq [(1, ret top);
          let n'' := count_tvar E in
          (n'', n' <- choose(0, n'');; ret (tvar n'));
          let vs := fetch_var_typs E in
          (List.length vs, elems_ top vs)].

Fixpoint gen_typ (n : nat) (E : env) (r : bool) {struct n} : G typ :=
  match n with
  | O =>
      gen_typ0 E r
  | S n =>
      freq [(1, gen_typ0 E r) ;
            (1, T1 <- gen_typ (n - 1) E false ;;
                T2 <- gen_typ n (ebound E T1) r ;;
                ret (all T1 T2)) ; 
            (1, T1 <- gen_typ (n - 1) E false ;;
                T2 <- gen_typ n (evar E T1) r ;;
                ret (arrow T1 T2))]
  end.

Sample (gen_typ 4 empty true).

Definition gen_opt_typ (n : nat) (E : env) (r : bool) : G (option typ) :=
  fmap Some (gen_typ n E r).

(** Generate a [term] *)

(** Find a bound var that is of a subtype of [T]  *)
Fixpoint get_bound_sub_vars (T : typ) (E : env) : list term :=
  let n := count_var E in
  let fix f n1 :=
    match n1 with
    | O => []
    | S n1 => 
        match get_var E n1 with
        | None => []
        | Some T1 => 
            let T' := match sub_check' E T1 T with
                      | true => [var n1]
                      | _ => []
                      end in
            T' ++ (f n1)
        end
    end in
  f n.

Fixpoint get_bound_sup_vars (T : typ) (E : env) : list term :=
  let n := count_var E in
  let fix f n1 :=
    match n1 with
    | O => []
    | S n1 => 
        match get_var E n1 with
        | None => []
        | Some T1 => 
            let T' := match sub_check' E T T1 with
                      | true => [var n1]
                      | _ => []
                      end in
            T' ++ (f n1)
        end
    end in
  f n.

Definition gen_bound_sub_vars T E : G (option term) :=
  elems_ None (map Some (get_bound_sub_vars T E)).

Definition gen_bound_sup_vars T E : G (option term) :=
  elems_ None (map Some (get_bound_sup_vars T E)).


Fixpoint gen_sub_term0 (E : env) (T : typ) : G (option term) :=
  let g : (G (option term)) :=
    match T with
    | arrow T1 T2 =>
        liftM (abs T1) (gen_sub_term0 (evar E T1) T2)
    | all T1 T2 =>
        liftM (tabs T1)
              (gen_sub_term0 (ebound E T1) T2)
    | _ => ret None
    end
  in     
  backtrack [(1, g); (1, (gen_bound_sub_vars T E))].

Fixpoint gen_sup_term0 (E : env) (T : typ) : G (option term) :=
  let g : (G (option term)) :=
    match T with
    | arrow T1 T2 =>
        liftM (abs T1) (gen_sup_term0 (evar E T1) T2)
    | all T1 T2 =>
        liftM (tabs T1)
              (gen_sup_term0 (ebound E T1) T2)
    | _ => ret None
    end
  in     
  backtrack [(1, g); (1, (gen_bound_sup_vars T E))].


(** generate operands to functions in the context *)
Definition michalsub (E : env) (T : typ) : list typ :=
  let n := count_var E in
  let fix f2 T' :=
    match T' with
    | arrow T1 T2 =>
        (** don't need to shift type here: no intro of tvar *)
        match sub_check' E T2 T with
        | true => [T1]
        | _ => []
        end ++ f2 T2
    | _ => []
    end in
  let fix f n1 :=
    match n1 with
    | O => []
    | S n1 => 
        match get_var E n1 with
        | Some T' => f2 T'
        | None => []
        end ++ f n1
    end in
  f n.

(** not useful? *)
Definition c_michalsub (g : G (option typ)) (E : env) (T : typ)
  : G (option typ) :=
  oneOf_ g (g :: (map (fun x => ret (Some x)) (michalsub E T))).


(** Generate a term of a subtype of [T] *)
Fixpoint gen_sub_term (n : nat) (E : env) (T : typ) : G (option term) :=
  match n with
  | O => gen_sub_term0 E T
  | S n =>
      let n' := n - 2 in (* n - n / 2 in *)
      (** Base Case *)
      let g0 := gen_sub_term0 E T in
      (** Generate by typ *)
      let g1 := 
        match T with
        | arrow T1 T2 =>
            T1' <- (c_gen_sup_typ (fun _ _ => ret T1) n E) ;;
            t2 <- (gen_sub_term n (evar E T1') T2) ;;
            ret (abs T1' t2)
        | all T1 T2 =>
            T1' <- (c_gen_sup_typ (fun _ _ => ret T1) n E) ;;
            t2 <- (gen_sub_term n (ebound E T1') T2) ;;
            ret (tabs T1' t2)
        | _ => g0
        end in
      (** Generate App *)
      let g2 :=
        (** restricted: to generate the operand term *)
        T1 <- c_michalsub (gen_opt_typ n' E true) E T;;
        (** generate [t1] of a subtype of [T1 -> T] *)
        t1 <- gen_sub_term n' E (arrow T1 T);;
        (** generate [t2] of a subtype of [T1] *)
        t2 <- gen_sub_term n' E T1;;
        returnGen (Some (app t1 t2))
      in
      (** Generate TApp : [t1'] is [(tabs T1 t1) T2] <: [T] *)
      let g3 :=
        (** unrestricted: typ can be any *)
        T1 <- gen_opt_typ n' E false;; 
        T2 <- c_gen_sub_typ (fun _ _ => ret T1) n' E;;
        t1' <- gen_sub_term n' E (all T1 (tshift 0 T)) ;;
        returnGen (Some (tapp t1' T2))
      in backtrack [(1, g0); (1, g1); (1, g2); (1, g3)]
  end
.

Sample (gen_opt_typ 2 empty true).

Sample (gen_sub_term 3 empty top).

Definition max_dec n m : nat :=
  if le_gt_dec n m then m else n.

Fixpoint measure_max_typ (T : typ) : nat :=
  match T with
  | tvar _ => 1 
  | top => 1
  | arrow T1 T2 => 1 + max_dec (measure_max_typ T1) (measure_max_typ T2)
  | all T1 T2 => 1 + max_dec (measure_max_typ T1) (measure_max_typ T2)
  end.

