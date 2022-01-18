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
(* collect all tvars  *)
Definition gen_exact_tvar0' (E : env) : list (G typ) :=
  match count_tvar E with
  | O => []
  | S n => [n' <- choose(0, n);; ret (tvar n')]
  end.

Definition gen_exact_tvar0 (E : env) : (G (option typ)) :=
  oneOf_ (ret None) (map (fmap Some) (gen_exact_tvar0' E)).

(* collect all vars *)
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

(* collect all vars and tvars in [E] *)
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
        returnGen (Some (tapp t1 T1)) in
      let g4 :=
        (** unrestricted: typ can be any *)
        '(T2, T12) <- gen_replace T ;;
        t1' <- gen_exact_term n E (all T2 T12) ;;
        returnGen (Some (tapp t1' T2))
      in backtrack [(1, g0); (1, g1); (1, g2); (1, g3); (1, g4)]
  end
.      

Definition gen_exact (n : nat) : G (option term) :=
  T <- gen_exact_typ n empty;;
  gen_exact_term n empty T.

(* Sample (gen_exact 5). *)


(** ** Generate Subtype *)

(** Find out super or sub type of the given [typ] in the environment *)
(* Definition find_sub_tvar   *)
(*            (E : env) (T2 : typ) : list typ := *)
(*   let n := count_tvar E in *)
(*   let fix f n1 := *)
(*     match n1 with *)
(*     | O => [] *)
(*     | S n1 =>  *)
(*         match get_bound E n1 with *)
(*         | None => [] *)
(*         | Some T1 =>  *)
(*             let T' := match sub_check' E T1 T2 with *)
(*                       | true => [T1] *)
(*                       | _ => [] *)
(*                       end in *)
(*             T' ++ (f n1) *)
(*         end *)
(*     end in *)
(*   f n. *)
  
(* Definition gen_sub_tvar (E : env) (T2 : typ) : G typ := *)
(*   elems_ T2 (find_sub_tvar E T2).  *)

(* (* This is actually incorrect! *) *)
(* Definition find_sup_tvar (E : env) (n1 : nat) : list typ := *)
(*   match get_bound E n1 with *)
(*   | None => [] *)
(*   | Some T1 =>  *)
(*       let n := count_tvar E in *)
(*       let fix f n2 := *)
(*         match n2 with *)
(*         | O => [] *)
(*         | S n2 =>  *)
(*             match get_bound E n2 with *)
(*             | None => [] *)
(*             | Some T2 =>  *)
(*                 let T' := match sub_check' E T1 T2 with *)
(*                           | true => [tvar n1] *)
(*                           | _ => [] *)
(*                           end in *)
(*                 T' ++ (f n2) *)
(*             end *)
(*         end in *)
(*       f n *)
(*   end. *)

(* Definition gen_sup_tvar (E : env) (n1 : nat) : G typ := *)
(*   elems_ (tvar n1) (find_sup_tvar E n1).  *)

(* Fixpoint gen_sub_typ (n : nat) (E : env) (T : typ) : G typ := *)
(*   match n with *)
(*   | O => ret T                  (** [sub] is reflexive *) *)
(*   | S n => *)
(*       let g1 := *)
(*         match T with *)
(*         | top => *)
(*             T1 <- gen_exact_typ n E ;; *)
(*             match T1 with *)
(*             | Some T1 => ret T1 *)
(*             | None => ret top *)
(*             end *)
(*         | tvar n => ret (tvar n) *)
(*         | arrow T1 T2 => *)
(*             S1 <- gen_sup_typ n E T1;; *)
(*             S2 <- gen_sub_typ n E T2;; *)
(*             ret (arrow S1 S2) *)
(*         | all T1 T2 => *)
(*             S1 <- gen_sup_typ n E T1;; *)
(*             S2 <- gen_sub_typ n (ebound E T1) T2;; *)
(*             ret (all S1 S2) *)
(*         end in *)
(*       let g2 := map ret (find_sub_tvar E T) in *)
(*       oneOf_ (ret T) ((ret T) :: g1 :: g2) *)
(*   end *)
(* with *)
(* gen_sup_typ (n : nat) (E : env) (T : typ) : G typ := *)
(*   match n with *)
(*   | O => ret T                  (** [sup] is reflexive *) *)
(*   | S n => *)
(*       let g1 := *)
(*         match T with *)
(*         | top => ret top        (** [top] is the top *) *)
(*         | tvar n => gen_sup_tvar E n *)
(*         | arrow T1 T2 => *)
(*             S1 <- gen_sub_typ n E T1;; *)
(*             S2 <- gen_sup_typ n E T2;; *)
(*             ret (arrow S1 S2) *)
(*         | all T1 T2 => *)
(*             S1 <- gen_sub_typ n E T1;; *)
(*             S2 <- gen_sup_typ n (ebound E T1) T2;; *)
(*             ret (all S1 S2) *)
(*         end in *)
(*       oneOf [ret T ; g1] *)
(*   end *)
(* . *)

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
            oT <- gen_exact_typ n E;;
            ret (match oT with None => top | Some t => t end)
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

Definition max_dec n m : nat :=
  if le_gt_dec n m then m else n.

Fixpoint measure_max_typ (T : typ) : nat :=
  match T with
  | tvar _ => 1 
  | top => 1
  | arrow T1 T2 => 1 + max_dec (measure_max_typ T1) (measure_max_typ T2)
  | all T1 T2 => 1 + max_dec (measure_max_typ T1) (measure_max_typ T2)
  end.
