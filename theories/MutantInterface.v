From FSUB Require Import
     QCLibs
     FSub
     Decidable.

(** * Mutant: Bug Injection and Reduction Strategies *)

(** ** Mutants *)
Inductive Mutant :=
| NoMutant
(** [tshift] bugs *)
| TShiftTVarAll
| TShiftTVarNoIncr
| TShiftAllNoIncr
(** [shift] bugs *)
| ShiftVarAll
| ShiftVarNoIncr
| ShiftAbsNoIncr
(** [shift_typ] bugs *)
| ShiftTypTAbsNoIncr
(** [tsubst] bugs *)
| TSubstTVarFlip
| TSubstTVarNoShift
| TSubstTVarOverShift
| TSubstAllNoTShift  
(** [subst] bugs *)
| SubstVarFlip
| SubstVarNoDecr
| SubstAbsNoShift
| SubstAbsNoIncr
| SubstTAbsNoShift
(** [subst_typ] bugs *)
| SubstTypTAbsNoIncr
| SubstTypTAbsNoShift
(** [get_bound] bugs *)
(** [get_var] bugs *)
.

Instance dec_eq_Mutant (m1 m2 : Mutant) : Dec (m1 = m2).
Proof. dec_eq. Defined.

Fixpoint mut {A} (c : Mutant) (x : A)
                 (my : list (Mutant * A)) : A :=
  match my with
  | [] => x
  | (m,y) :: my' => if c = m? then y else mut c x my'
  end.


(** ** Bug Injection *)
Fixpoint tshift' (c : Mutant) (X : nat) (T : typ) {struct T} : typ :=
  let tshift := tshift' c in 
  match T with
  | tvar Y      => mut c (tvar (if le_gt_dec X Y then 1 + Y else Y))
                       [(TShiftTVarAll, tvar (1 + Y));
                        (TShiftTVarNoIncr, tvar Y)]
  | top         => top
  | arrow T1 T2 => arrow (tshift X T1) (tshift X T2)
  | all T1 T2   => mut c (all (tshift X T1) (tshift (1 + X) T2))
                       [(TShiftAllNoIncr, all (tshift X T1) (tshift X T2))]
  end.

Fixpoint shift' (c : Mutant) (x : nat) (t : term) {struct t} : term :=
  let shift := shift' c in
  match t with
  | var y      => mut c (var (if le_gt_dec x y then 1 + y else y))
                      [(ShiftVarAll, var (1 + y));
                       (ShiftVarNoIncr, var y)]
  | abs T1 t2  => mut c (abs T1 (shift (1 + x) t2))
                      [(ShiftAbsNoIncr, (abs T1 (shift x t2)))]
  | app t1 t2  => app (shift x t1) (shift x t2)
  | tabs T1 t2 => tabs T1 (shift x t2)
  | tapp t1 T2 => tapp (shift x t1) T2
  end.

Fixpoint shift_typ' (c : Mutant) (X : nat) (t : term) {struct t} : term :=
  let shift_typ := shift_typ' c in 
  let tshift := tshift' c in 
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tshift X T1) (shift_typ X t2)
  | app t1 t2  => app (shift_typ X t1) (shift_typ X t2)
  | tabs T1 t2 => mut c (tabs (tshift X T1) (shift_typ (1 + X) t2))
                      [(ShiftTypTAbsNoIncr, tabs (tshift X T1)
                                                 (shift_typ X t2))]
  | tapp t1 T2 => tapp (shift_typ X t1) (tshift X T2)
  end.

Fixpoint tsubst' (c : Mutant) (T : typ) (X : nat) (T' : typ) {struct T} : typ :=
  let tsubst := tsubst' c in
  let tshift := tshift' c in
  match T with
  | tvar Y =>
      mut c 
          (match lt_eq_lt_dec Y X with
           | inleft (left _)  => tvar Y
           | inleft (right _) => T'
           | inright _        => tvar (Y - 1)
           end)
          [(TSubstTVarFlip,
             (match lt_eq_lt_dec Y X with
              | inleft (left _)  => tvar (Y - 1)
              | inleft (right _) => T'
              | inright _        => tvar Y
              end));
           (TSubstTVarNoShift,
             (match lt_eq_lt_dec Y X with
              | inleft (left _)  => tvar Y
              | inleft (right _) => T'
              | inright _        => tvar Y
              end));
           (TSubstTVarOverShift,
             (match lt_eq_lt_dec Y X with
              | inleft (left _)  => tvar (Y - 1)
              | inleft (right _) => T'
              | inright _        => tvar (Y - 1)
              end))]
  | top         => top
  | arrow T1 T2 => arrow (tsubst T1 X T') (tsubst T2 X T')
  | all T1 T2   =>
      mut c
          (all (tsubst T1 X T') (tsubst T2 (1 + X) (tshift 0 T')))
          [(TSubstAllNoTShift,
             all (tsubst T1 X T') (tsubst T2 (1 + X) T'))]
  end.

Fixpoint subst' (c : Mutant) (t : term) (x : nat) (t' : term) {struct t} : term :=
  let subst := subst' c in
  let shift := shift' c in
  let shift_typ := shift_typ' c in
  match t with
  | var y =>
      mut c 
          (match lt_eq_lt_dec y x with
           (* x > y : does not affect *)
           | inleft (left _)  => var y 
           (* x = y : target for substitution *)
           | inleft (right _) => t'    
           (* x < y : var disappears, shift by 1 *)
           | inright _        => var (y - 1)
           end)
          [(SubstVarFlip,
             (match lt_eq_lt_dec y x with
              | inleft (left _)  => var (y - 1) 
              | inleft (right _) => t'    
              | inright _        => var y
              end));
           (SubstVarNoDecr,
             (match lt_eq_lt_dec y x with
              | inleft (left _)  => var y 
              | inleft (right _) => t'    
              | inright _        => var y
              end))]
  | abs T1 t2  =>
      mut c 
          (abs T1 (subst t2 (1 + x) (shift 0 t')))
          [(SubstAbsNoShift, abs T1 (subst t2 (1 + x) t'));
           (SubstAbsNoIncr, (abs T1 (subst t2 x (shift 0 t'))))]
  | app t1 t2  => app (subst t1 x t') (subst t2 x t')
  | tabs T1 t2 =>
      mut c
          (tabs T1 (subst t2 x (shift_typ 0 t')))
          [(SubstTAbsNoShift, (tabs T1 (subst t2 x t')))]
  | tapp t1 T2 => tapp (subst t1 x t') T2
  end.

Fixpoint subst_typ' (c : Mutant) (t : term) (X : nat) (T : typ) {struct t} :
  term :=
  let subst_typ := subst_typ' c in
  let subst := subst' c in
  let tshift := tshift' c in
  let tsubst := tsubst' c in
  match t with
  | var y      => var y
  | abs T1 t2  => abs (tsubst T1 X T) (subst_typ t2 X T)
  | app e1 e2  => app (subst_typ e1 X T) (subst_typ e2 X T)
  | tabs T1 e1 =>
      mut c
          (tabs (tsubst T1 X T) (subst_typ e1 (1 + X) (tshift 0 T)))
          [(SubstTypTAbsNoIncr,
             tabs (tsubst T1 X T) (subst_typ e1 X (tshift 0 T)));
           (SubstTypTAbsNoShift,
             tabs (tsubst T1 X T) (subst_typ e1 (1 + X) T))]
  | tapp e1 T2 => tapp (subst_typ e1 X T) (tsubst T2 X T)
  end.

(** ** Mutated Reduction *)
(** TODO : use [Section] *)
(** *** Alternative Smallstep Semantics *)
Fixpoint step'' (m : Mutant) (t : term) : option term :=
  let step' := step'' m in
  let subst := subst' m in 
  let subst_typ := subst_typ' m in 
  
  let appfun' t1 t2 :=
    t1' <- step' t1;; ret (app t1' t2) in 

  let apparg' t1 t2 :=
    t2' <- step' t2;; ret (app t1 t2') in

  let typefun' t1 T2 :=
    t1' <- step' t1;; ret (tapp t1' T2) in 

  match t with
  | app t1 t2 =>
      match t1 with
      |  abs t11 t12 => 
           if dc_value t2 
           then ret (subst t12 0 t2) (* appabs *)
           else apparg' t1 t2
      | _ =>
          if dc_value t1
          then apparg' t1 t2
          else appfun' t1 t2
      end
  | tapp t1 T2 =>
      match t1 with
      | tabs t11 T12 => ret (subst_typ T12 0 T2)
      | _ => typefun' t1 T2            
      end
  | _ => None
  end.


(** *** Parallel Reduction 
    Support reduction to normal form.
 *)
Fixpoint pstep' (m : Mutant) (t : term) : option term :=
  let pstep := pstep' m in
  let subst := subst' m in 
  let subst_typ := subst_typ' m in 
  match t with
  | var _ => ret t 
  | abs T t =>  liftM (abs T) (pstep t)
  | app t1 t2 =>
      match t1 with
      | abs _ t1 => ret (subst t1 0 t2)
      | _ => liftM2 app (pstep t1) (pstep t2)
      end
  | tabs T t => liftM (tabs T) (pstep t)
  | tapp t T =>
      match t with
      | tabs _ t => ret (subst_typ t 0 T)
      | _ => liftM (fun t => tapp t T) (pstep t)
      end
  end.

Fixpoint is_nf (t : term) :=
  match t with
  | var _ => true
  | abs _ t => is_nf t
  | app (abs _ _) t2 => false
  | app t1 t2 => is_nf t1 && is_nf t2
  | tabs _ t => is_nf t
  | tapp (tabs _ _) _ => false
  | tapp t _ => is_nf t
  end.


(** *** Multistep Closure *)
Fixpoint multistep' {A}
         (m : Mutant)
         (n : nat)
         (step : Mutant -> A -> option A)
         (t : A)
         (is_value : A -> bool) : @result (bool * A) :=
  match n with
  | O => OutOfFuel
  | S n =>
      if (is_value t) then Result (true, t)
      else match step m t with
           | Some t => multistep' m n step t is_value
           | None => Result ((is_value t), t)
           end
  end.

