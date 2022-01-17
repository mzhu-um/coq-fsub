From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.
From FSUB Require Import Reduction.

(** * Generator: System F<: Random Generators *)

(** ** Utilities *)
(** Shorthands : only care about true or false. *)
Definition type_check' :=
  fun E t T =>
    match type_check E t T 100 with
    | Result true => true
    | _ => false
    end. 

Definition get_typ' :=
  fun E t =>
    match get_typ E t 100 with
    | Result o => o
    | _ => None
    end. 

Definition sub_check' :=
  fun e T1 T2 => match sub_check e T1 T2 100 with
                 | Result true => true
                 | _ => false
                 end.


Fixpoint count_tvar (e : env) : nat :=
  match e with
  | empty => O
  | evar e _ => count_tvar e
  | ebound e _ => S (count_tvar e)
  end.

Fixpoint count_var (E : env) : nat :=
  match E with
  | empty => 0
  | evar E _ => S (count_var E)
  | ebound E _ => (count_var E)
  end.

(** ** Generate System F <:
    
    - Generate a type to be used as the super type of the program
    - Narrow the type down to exact subtype terms for termination
*)

(** *** Generate [typ] *)

(** collect all bound var typs *)
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

(** collect super bound var types 
    - for each [var] in the env, perform "upcast" to it 
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
  List.fold_right
    (fun v acc =>
       acc ++ match v with
              | tvar n =>
                  v ::          (** bound var itself *)
                    match get_bound E n with
                    | Some T => (** upcast to its super *)
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

(** Reworked [gen_typ] : allow bare [top]s and [arrow]s *)
Definition gen_typ0 (E : env) (r : bool) : G typ := 
  if r
  then                          (** Restricted: must be sub bound [var] *)
    freq [(1, ret top);
          let Ts := fetch_good_typs E in
          (List.length Ts, elems_ top Ts)]
  else                          (** Any bound [var] or [tvar] suffice *)
    freq [(1, ret top);
          let n'' := count_tvar E in
          (n'', n' <- choose(0, n'' - 1);; ret (tvar n'));
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
      oneOf [ret T; g1; g2']
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
      oneOf [ret T; g1; g2']
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

(** generate operands to functions in the context *)
Definition michalsub (E : env) (T : typ) : list typ :=
  let n := count_var E in
  let fix f2 T' :=
    match T' with
    | arrow T1 T2 =>
        (** don't need to shift type here: no intro of tvar *)
        match f2 T2 with
        | [] => if sub_check' E T2 T then [T1] else []
        | rst => T1 :: rst
        end
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
  let g1 := (if T = T' ? then [(3, ret (tvar n))] else [(1, ret T)])  in
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
    | _ => ret T
    end in
   freq_ (ret T) ((2, g2) :: g1).

Definition gen_replace T : G (option (typ * typ)) :=
  oT1 <- gen_cand T ;;
  match oT1 with
  | Some T1 =>
    T2 <- replace_typ (tshift 0 T) (tshift 0 T1) 0 ;;
    (ret (Some (T1, T2)))
  | None => ret None
  end. 


Example repl_ty :=
  (arrow (tvar 0) (arrow (tvar 1) (all top (arrow (tvar 1) (tvar 0))))).

Sample (gen_replace repl_ty).

Fixpoint gen_sub_term0 (E : env) (T : typ) : G (option term) :=
  let g : (G (option term)) :=
    match T with
    | arrow T1 T2 =>
        liftM (abs T1) (gen_sub_term0 (evar E T1) T2)
    | all T1 T2 =>
        liftM (tabs T1)
              (gen_sub_term0 (ebound E T1) T2)
    | tvar n =>                 (** guarded by [gen_typ] *)
        gen_sub_vars E T
    | top => ret (abs top (var 0)) (** random stuff *)
    end
  in     
  backtrack [(1, g); (1, (gen_sub_vars E T))].


(** Generate a term of a subtype of [T] *)
Fixpoint gen_sub_term (n : nat) (E : env) (T : typ) : G (option term) :=
  match n with
  | O => gen_sub_term0 E T
  | S n =>
      (* let n' := n - 2 in (* n - n / 2 in *) *)
      (** Mutate the type based on bound [typ]'s *)
      
      let n' := n in
      (** Base Case *)
      let g0 := gen_sub_term0 E T in
      (** Generate by typ *)
      let g1 := 
        match T with
        | arrow T1 T2 =>
            T1' <- gen_opt_sup_typ n E T1 ;;
            t2 <- gen_sub_term n (evar E T1') T2 ;;
            ret (abs T1' t2)
        | all T1 T2 =>
            T1' <- gen_opt_sup_typ n E T1 ;;
            t2 <- gen_sub_term n (ebound E T1') T2 ;;
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
        T2 <- gen_opt_sub_typ n' E T1;;
        t1' <- gen_sub_term n' E (all T1 (tshift 0 T)) ;;
        returnGen (Some (tapp t1' T2))
      in
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
