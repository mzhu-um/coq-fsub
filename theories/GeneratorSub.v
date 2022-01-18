From FSUB Require Import
     QCLibs
     FSub
     Decidable.
(** * Generator: System F<: Random Generators *)
(** ** Generate System F <:
    
    - Generate a type to be used as the super type of the program
    - Narrow the type down to exact subtype terms for termination
*)

(** *** Generate [typ] *)
(** [fetch_var_typs] : 
    collect types of all [var]s in the context 
 *)
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

(** [fetch_good_typs] : 
    collect types of all [vars]s and all [tvar]s that occur as suptype of
    some [var]s

    - for each [var n = T] in the env, check if [T] <: [tvar n]
 *)
Definition fetch_good_typs (E : env) : list typ :=
  let vars := fetch_var_typs E in
  let ntvars :=  count_tvar E in
  let fix f n :=
    match n with
    | O => []
    | S n => (tvar n) :: f n
    end in
  let tvars := f ntvars in 
  List.fold_left
    (fun acc vT =>
       List.filter (sub_check' E vT) tvars ++ vars)
    vars vars .
    
(** Reworked [gen_typ] : allow bare [top]s and [arrow]s *)

(** [gen_typ0] : 
    generate types from the type context
 *)
Definition gen_typ0 (E : env) (r : bool) : G typ :=
  let g' :=
    if r
    then                        (** Restricted: must be sub bound [var] *)
      freq [(1, ret top);
            let n'' := count_tvar E in
            (n'', n' <- choose(0, n'' - 1);; ret (arrow (tvar n') (tvar n')));
            let Ts := fetch_good_typs E in
            (List.length Ts, elems_ top Ts)]
    else                        (** Any bound [var] or [tvar] suffice *)
      freq [(1, ret top);
            let n'' := count_tvar E in
            (n'', n' <- choose(0, n'' - 1);; ret (tvar n'));
            let vs := fetch_var_typs E in
            (List.length vs, elems_ top vs)] in
  T <- g' ;; elems [T; (arrow T T)].

(** [gen_typ0] : 
    generate types from the type context
 *)
Fixpoint gen_typ (n : nat) (E : env) (r : bool) {struct n} : G typ :=
  match n with
  | O =>
      gen_typ0 E r
  | S n =>
      freq [(1, gen_typ0 E r) ;
            (1, T1 <- gen_typ n E false ;;
                T2 <- gen_typ n (ebound E T1) r ;;
                ret (all T1 T2)) ; 
            (1, T1 <- gen_typ n E false ;;
                T2 <- gen_typ n (evar E T1) r ;;
                ret (arrow T1 T2))]
  end.

Sample (gen_typ 4 empty true).

Definition gen_opt_typ (n : nat) (E : env) (r : bool) : G (option typ) :=
  fmap Some (gen_typ n E r).

Definition find_sub_var_typs (E : env) (T : typ) : list typ :=
  List.filter (fun T' => sub_check' E T' T) (fetch_var_typs E). 

Definition find_sup_var_typs (E : env) (T : typ) : list typ :=
  List.filter (sub_check' E T) (fetch_var_typs E). 

Definition find_sub_tvar_typs (E : env) (T : typ) : list typ :=
  let ntvars :=  count_tvar E in
  let fix f n :=
    match n with
    | O => []
    | S n => n :: f n
    end in
  map tvar
      (List.filter
         (fun n =>
            match get_bound E n with
            | Some T' => sub_check' E T' T
            | _ => false
            end)
         (f ntvars)).

Fixpoint gen_sub_typ (n : nat) (E : env) (T : typ) {struct n} : G typ :=
  match n with
  | O => ret T                  (** [sub] is reflexive *)
  | S n =>
      let g1 :=
        match T with
        | top =>                
            gen_typ n E true
        | tvar n => ret (tvar n)
        | arrow T1 T2 => 
            S1 <- gen_sup_typ n E T1;;
            S2 <- gen_sub_typ n E T2;;
            ret (arrow S1 S2)
        | all T1 T2 =>
            S1 <- gen_sup_typ n E T1;;
            S2 <- gen_sub_typ n (ebound E T1) T2;;
            ret (all S1 S2)
        end in
      let g2 :=
        elems_ T ((find_sub_var_typs E T) ++ (find_sub_tvar_typs E T)) in
      let g2' := T <- g2 ;; gen_sub_typ n E T in
      oneOf [ret T; g1; g2; g2']
  end
with
gen_sup_typ (n : nat) (E : env) (T : typ) {struct n} : G typ :=
  match n with
  | O => ret T                  (** [sup] is reflexive *)
  | S n =>
      let g1 :=
        match T with
        | top => ret top        (** [top] is the top *)
        | tvar n' =>
            match get_bound E n' with
            | Some T => gen_sup_typ n E T
            | _ => ret (tvar n')
            end
        | arrow T1 T2 =>
            S1 <- gen_sub_typ n E T1;;
            S2 <- gen_sup_typ n E T2;;
            ret (arrow S1 S2)
        | all T1 T2 =>
            S1 <- gen_sub_typ n E T1;;
            S2 <- gen_sup_typ n (ebound E T1) T2;;
            ret (all S1 S2)
        end in
      let g2 := elems_ top (find_sup_var_typs E T) in
      let g2' := T <- g2 ;; gen_sup_typ n E T in 
      oneOf [ret T; g1; g2; g2']
  end
.

Definition gen_opt_sub_typ (n : nat) (E : env) (T : typ) : G (option typ) :=
  fmap Some (gen_sub_typ n E T).

Definition gen_opt_sup_typ (n : nat) (E : env) (T : typ) : G (option typ) :=
  fmap Some (gen_sup_typ n E T).

(** Generate a [term] *)
(** Fetch bound vars that are <: [T]  *)
Definition fetch_sub_vars (E : env) (T : typ) : list term :=
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

Definition gen_sub_vars E T : G (option term) :=
  elems_ None (map Some (fetch_sub_vars E T)).

(** [michalsub] :

    generate good operands when generating [app]
    - generate arguments for functions in the context
    - generate arguments for the type to appear in [T]
*)
Definition michalsub (E : env) (T : typ) : list typ :=
  let n := count_var E in
  let fix g0 T :=
    match T with
    | arrow T1 T2 => T2 :: g0 T2
    (* all _ T2 => ? *)
    | _ => []
    end in
  let fix f2 T' :=
    match T' with
    | arrow T1 T2 =>
        (* don't need to shift type here: no intro of [tvar] *)
        (* ??? : is [T'] <: [T2] correct? *)
        if sub_check' E T' T2 then [T1] else f2 T2
        (* match f2 T2 with *)
        (* | [] => if sub_check' E T2 T then [T1] else [] *)
        (* | rst => T1 :: rst *)
        (* end *)
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
  (g0 T) ++ (f n).

(** not useful? *)
Definition c_michalsub (g : G (option typ)) (E : env) (T : typ)
  : G (option typ) :=
  oneOf_ g (g :: (map (fun x => ret (Some x)) (michalsub E T))).

(** Replace free/constant [typ's] in [t] with a new [typ] *)

(** fetch_candidate_typs : 
    list of free/constant [typ] in [T] under the context [E] 
 *)
Definition fetch_candidate_typs (T : typ) : list typ :=
  let fix fetch_p T n :=
    match T with
    | top => true
    | tvar n' => (** Check if it's free *)
        n <=? n'
    | arrow T1 T2 =>
        ((fetch_p T1 n) && (fetch_p T2 n))%bool
    | all T1 T2 =>
        (** not precise here *)
        ((fetch_p T1 n) && (fetch_p T2 (S n)))%bool
    end in
  let fix tunshift T n :=
    match T with
    | top => top
    | tvar n' => tvar (n' - n)
    | arrow T1 T2 => arrow (tunshift T1 n) (tunshift T2 n)
    | all T1 T2 => all (tunshift T1 n) (tunshift T2 (S n))
    end
  in
  let fix f T nbound :=
    (if fetch_p T nbound then [tunshift T nbound] else [])
      ++
      (match T with
       | arrow T1 T2 =>
           (f T1 nbound) ++ (f T2 nbound)
       | all T1 T2 =>
           (f T1 nbound) ++ (f T2 (S nbound))
       | _ => []
       end) in
  f T 0.  

Definition gen_cand (T : typ) : G (option typ) :=
  elems_ None (map Some (fetch_candidate_typs T)).

(** 2 strategies here: 
    - [replace_typ T T' n] :
      replace part of type [T] equal to T'  with [tvar n]
      (without considering sub)
    - [mutate_typ E T] :
      replace part of type [T] by consulting bound types in [E] 
      (considerng sub typing)

    Which one is better?
 *)


Fixpoint replace_typ T T' n : G typ :=
  (** more likely to generate replacement *)
  let g1 := (if T = T' ? then [(2 + n, ret (tvar n))] else [(1, ret T)])  in
  let g2 :=
    match T with
    | arrow T1 T2 =>
        T1' <- replace_typ T1 T' n ;;
        T2' <- replace_typ T2 T' n ;;
        ret (arrow T1' T2')
    | all T1 T2 => 
        T1' <- replace_typ T1 T' n ;;
        T2' <- replace_typ T2 (tshift 0 T') (S n) ;;
        ret (all T1' T2')
    | _ => freq_ (ret T) g1
    end in
   freq_ (ret T) ((2 + n, g2) :: g1).

Definition gen_replace T : G (option (typ * typ)) :=
  oT1 <- gen_cand T ;;
  match oT1 with
  | Some T1 =>
    T2 <- replace_typ (tshift 0 T) (tshift 0 T1) 0 ;;
    (ret (Some (T1, T2)))
  | None => ret None
  end. 


(** [gen_sub_term] *)
Fixpoint gen_sub_term0' (E : env) (T : typ) : G (option term) :=
  let g : (G (option term)) :=
    match T with
    | arrow T1 T2 =>
        liftM (abs T1) (gen_sub_term0' (evar E T1) T2)
    | all T1 T2 =>
        liftM (tabs T1)
              (gen_sub_term0' (ebound E T1) T2)
    | tvar n =>                 (** guarded by [gen_typ] *)
        gen_sub_vars E T
    | top =>
        (** random stuff *)
        elems
          [Some (abs top (var 0));
           Some (tabs top (abs (tvar 0) (var 0))) ] 
    end
  in     
  freq [(1, g); 
        let vars := fetch_sub_vars E T in
        (List.length vars, elems_ None (map Some vars))].

Definition gen_sub_term0 (E : env) (T : typ) : G (option term) :=
  let g := 
    match T with
    | top => 
        T' <- gen_opt_typ 0 E true;; gen_sub_term0' E T
    | _ => gen_sub_term0' E T
    end in
  freq [(1, g); 
        let vars := fetch_sub_vars E T in
        (List.length vars, elems_ None (map Some vars))].



(** Generate a term of a subtype of [T] *)
Fixpoint gen_sub_term (n : nat) (E : env) (T : typ) : G (option term) :=
  match n with
  | O => gen_sub_term0 E T
  | S n =>
      let n' := n in
      (** Base Case *)
      let g0 := gen_sub_term0 E T in
      (** Generate by [typ] *)
      let g1 := 
        match T with
        | arrow T1 T2 =>
            T1' <- gen_opt_sup_typ n E T1 ;;
            t2 <- gen_sub_term n (evar E T1') T2 ;; (* change back to [T1] ? *)
            ret (abs T1' t2)
        | all T1 T2 =>
            T1' <- gen_opt_sup_typ n E T1 ;;
            t2 <- gen_sub_term n (ebound E T1') T2 ;;
            ret (tabs T1' t2)
        | _ => g0
        end in
      (** Generate [app] *)
      let g2 :=
        (** restricted: generate the operand term *)
        T1 <- c_michalsub (gen_opt_typ n' E true) E T;;
        (** generate [t1] of a subtype of [T1 -> T] *)
        t1 <- gen_sub_term n' E (arrow T1 T);;
        (** generate [t2] of a subtype of [T1] *)
        t2 <- gen_sub_term n' E T1;;
        returnGen (Some (app t1 t2))
      in
      (** Generate [tapp] : [t1'] is [(tabs T1 t1) T2] <: [T] *)
      let g3 :=
        (** unrestricted: typ can be any *)
        T1 <- gen_opt_typ n' E false;; 
        T2 <- gen_opt_sub_typ n' E T1;;
        t1' <- gen_sub_term n' E (all T1 (tshift 0 T)) ;;
        returnGen (Some (tapp t1' T2))
      in
      (** Generate [tapp] by replacing some types with a new [tvar] *)
      let g4 :=
        (** unrestricted: typ can be any *)
        '(T2, T12) <- gen_replace T ;;
        T11 <- gen_opt_sup_typ n' E T2 ;;
        t1' <- gen_sub_term n' E (all T11 T12) ;;
        returnGen (Some (tapp t1' T2))
      in
      (** introduce more [app] and  [tapp] at beginning *)
      backtrack [(1, g0); (1, g1); (n', g2); (n', g3); (n', g4)]
  end
.

(*
Definition max_dec n m : nat :=
  if le_gt_dec n m then m else n.

Fixpoint measure_max_typ (T : typ) : nat :=
  match T with
  | tvar _ => 1 
  | top => 1
  | arrow T1 T2 => 1 + max_dec (measure_max_typ T1) (measure_max_typ T2)
  | all T1 T2 => 1 + max_dec (measure_max_typ T1) (measure_max_typ T2)
  end.


*)
