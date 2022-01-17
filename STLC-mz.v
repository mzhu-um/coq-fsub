
(** 838 Midterm:

In this file, you will find an implementation of a simply typed
lambda calculus with unit and integer types that uses DeBruijn
indices to represent variables (more detail and explanations
follow). 

Your main task will be to write a generator for terms that given
a fuel, a type, and an environment, generates well-typed terms.
Look at the TODO at the bottom of this file. But you should
probably also take a look at everything in between to understand
what you will be testing :) 

 *)

(* Imports. 
   If these don't work, make sure you have quickchick installed!
  
     opam install coq-quickchick 
 
   should do the trick. I've tested this with coq 8.12 + 8.13.
 *)
Require Import Arith List String.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad ListMonad.
Import QcNotation.

Import MonadNotation.
Import ListNotations.

Open Scope string.

(*** STLC with DeBruijn indices *)

(* This midterm focuses on the simply typed lambda calculus 
   where binders are represented using DeBruijn indices. 
   DeBruijn indices are used to make the semantic notion of 
   α-equivalence syntactically visible. 

   Consider the identity function. In a traditional
   name-based representation, λx.x and λy.y are two syntactic
   forms representing the same function --- the names don't matter!
   But that can be a bit annoying to deal with formally, as 
   a lot of theorems hold up to α-equivalence. DeBruijn indices
   are a way of ensuring that two such α-equivalent terms are 
   _syntactically_ equal.

   When using DeBruijn indices, instead of using names as variables,
   we use natural numbers, which represent _the number of binders that
   are in scope between an occurence of the variable and its 
   corresponding binding_. For example, the identity function is now
   represented as λ.0, while the Church representations of true (λx.λy.x)
   and false (λx.λy.y) become λ.λ.1 and λ.λ.0 respectively. 

   For a longer reference, a good tutorial is the first section of 
   Cornell's relevant lecture : 

   https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf 
 *)

(** Types *)
(* A standard STLC with unit and integer types. *)

Inductive Typ :=
| TBase   : Typ
| TInt    : Typ
| TFun    : Typ -> Typ -> Typ.

Notation "%" := TBase.
Notation "x :-> y" := (TFun x y) (at level 50).

Instance dec_eq_Typ (τ1 τ2 : Typ) : Dec (τ1 = τ2).
Proof. dec_eq. Defined.

(** Terms *)
(* A standard STLC with unit, integer constants,
   a predecessor function, and addition. 

   Variables are represented using DeBruijn indices.
   Quick Reference: https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf 
*)

Inductive Term :=
| Unit  : Term
| Const : nat -> Term
| Pred  : Term -> Term 
| Plus  : Term -> Term -> Term 
| Var   : nat -> Term
| Lam   : Typ -> Term -> Term
| App   : Term -> Term -> Term.

Notation "#" := Unit.

Instance dec_eq_Term (e1 e2 : Term) : Dec (e1 = e2).
Proof. dec_eq. Defined.

(** Mutants *)
(* This is a mini-framework for injecting bugs in definitions. *)

Inductive Mutant :=
| NoMutant
| SubstNoLift
| SubstNoIncr
| SubstNoDecr
| LiftAllVar
| LiftLamNoIncr
| LiftLamNoLift
| SubstNoPred
| PlusBottom
.

Instance dec_eq_Mutant (m1 m2 : Mutant) : Dec (m1 = m2).
Proof. dec_eq. Defined.

(* The expression 
     
     mut c e [(M_1, e_1);...(M_n, e_n)] 

   evaluates to e_i if c = M_i and e otherwise
*)
    
Fixpoint mut {A} (c : Mutant) (x : A)
                 (my : list (Mutant * A)) : A :=
  match my with
  | [] => x
  | (m,y) :: my' => if c = m? then y else mut c x my'
  end.

(* Lifting and substitution *)
(* Standard DeBruijn index lifting.
   Reference: https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture15.pdf *)

(* Lifting - lots of opportunities for bugs! *)
Fixpoint lift (c : Mutant) (n : nat) (e : Term) : Term :=
  match e with
  | Unit      => Unit
  | Const n   => Const n
  | Pred e    => Pred (lift c n e)
  | Plus e1 e2 => Plus (lift c n e1) (lift c n e2)
  | Var x     => mut c (Var (if x <? n then x else x+1))
                       [(LiftAllVar, Var (x+1))]
  | Lam τ e'  => mut c (Lam τ (lift c (n+1) e'))
                       [ (LiftLamNoIncr, Lam τ (lift c n e'))
                       ; (LiftLamNoLift, Lam τ e') ]
  | App e1 e2 => App (lift c n e1) (lift c n e2)
  end.


(* Substitution - lots of opportunities for bugs! *)
Fixpoint subst (c : Mutant) (n : nat) (s : Term) (e : Term) : Term :=
  match e with
  | Unit  => Unit
  | Const n => Const n
  | Pred e => Pred (mut c (subst c n s e)
                        [(SubstNoPred, Pred e)])
  | Plus e1 e2 => Plus (subst c n s e1) (subst c n s e2)
  | Var x =>
    if Nat.eqb x n then s
    else if n <? x then mut c (Var (x-1))
                              [ (SubstNoDecr, Var x) ]
    else Var x
  | Lam τ e' => mut c (Lam τ (subst c (n+1) (lift c 0 s) e'))
                      [ (SubstNoIncr, Lam τ (subst c n (lift c 0 s) e'))
                      ; (SubstNoLift, Lam τ (subst c (n+1) s e')) ]
  | App e1 e2 => App (subst c n s e1) (subst c n s e2)
  end.

(** Typing *)
(* Standard typing. 
   Variables are just the index into the environment. *)

Definition env := list Typ.

Fixpoint typeOf (Γ : env) (e : Term) : option Typ :=
  match e with
  | Unit => Some TBase
  | Const n => Some TInt
  | Pred e =>
      match typeOf Γ e with
      | Some TInt => Some TInt
      | _ => None
      end
  | Plus e1 e2 =>
      match typeOf Γ e1, typeOf Γ e2 with
      | Some TInt, Some TInt => Some TInt
      | _, _ => None
      end
  | Var x => nth_error Γ x
  | Lam τ e' =>
     τ' <- typeOf (τ :: Γ) e';;
     Some (τ :-> τ')
  | App e1 e2 => τ12 <- typeOf Γ e1;;
                 τ1 <- typeOf Γ e2;;
                 match τ12 with
                 | τ1' :-> τ2 =>
                   if τ1 = τ1' ? then Some τ2
                   else None
                 | _ => None
                 end
  end.

Definition well_typed (e : Term) : bool :=
  match typeOf [] e with
  | Some _ => true
  | _ => false
  end.

(* A twist on evaluation. 

   Parallel reduction instead of small-step:
   Reduce every redex at once, including under lambdas! 
   That gives us more opportunities for things to go wrong :) 

   Note that this is _not_ a big step relation, it does not
   fully evaluate things to a value! Rather it leaves values
   unaffected (see e.g. Unit or Const) and reduces things further
   if it can.
*)
Fixpoint pstep (c : Mutant) (e : Term) : Term :=
  match e with
  | Unit  => Unit
  | Const n => Const n
  | Pred e =>
      match pstep c e with
      | Const n => Const (pred n)
      | e' => Pred e'
      end
  | Plus e1 e2 =>
      match pstep c e1, pstep c e2 with
      | Const n1, Const n2 => Const (n1 + n2)
      | e1', e2' =>
          mut c (Plus e1' e2')
               [(PlusBottom, Unit)]
      end
  | Var x => Var x
  | Lam τ e'  => Lam τ (pstep c e')
  | App e1 e2 => let e1' := pstep c e1 in
                 let e2' := pstep c e2 in
                 match e1' with
                 | Lam τ body =>
                     subst c 0 e2' body
                 | _ => App e1' e2'
                 end
  end.

(** To encode multiple steps of this relation, we can use the
    following function to construct a complete trace of the
    evaluation. We take multiple steps, until either the fuel runs
    out, or until pstep "stutters", producing the input term. *)
Fixpoint multistep_aux (n : nat) (c : Mutant) (e : Term)
         (tr : list Term) :
  bool * list Term :=
  match n with
  | O => (false, tr) 
  | S n' =>
      let e' := pstep c e in
      if e = e' ? then
        (true, tr)
      else
        multistep_aux n' c e' (e' :: tr)
  end.

Definition multistep (n : nat) (c : Mutant) (e : Term) :=
  multistep_aux n c e [e].

(* Units, Numbers, and Lambdas are values. *)
Definition is_value (e : Term) : bool :=
  match e with
  | Unit => true
  | Lam _ _ => true
  | Const _ => true
  | _ => false
  end.

(* This is missing from QuickChick's standard library! *)
Instance Dec_eq_opt (A : Type) (m n : option A)
  `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.

(* The property of interest: Well typed programs don't go wrong! 

   That is, given a well typed term, if we take as many steps as 
   we can from that term either evaluation will terminate and 
   produce a value of the same type, or we haven't provided 
   enough fuel (but the final term of the trace still has the 
   same type as the original).
*)
Definition soundness (n : nat) (c : Mutant) (e : Term) :=
  match multistep n c e with
  | (true, (v::_)) =>
      andb (is_value v)
           (typeOf [] e = typeOf [] v ?)
  | (false, (e'::_)) =>
      typeOf [] e = typeOf [] e' ?
  | _ => false
  end.

(** Printing *)
(* To help out, I provided the following functions for pretty
   printing which I incorporated into the Show typeclass. *)

Inductive Prec := POuter | PApp | PInner.

Definition ltp (p1 p2 : Prec) :=
  match p1, p2 with
  | POuter, PApp => true
  | POuter, PInner => true
  | PApp  , PInner => true
  | _, _ => false
  end.

Definition parens outer inner s := if ltp inner outer then "(" ++ s ++ ")" else s.

Fixpoint showTyp' prec (τ : Typ) :=
  match τ with
  | TBase => "()"
  | TInt  => "N"
  | TFun τ1 τ2 => parens prec PApp (showTyp' PInner τ1 ++ "->" ++ showTyp' PApp τ2)
  end.

Instance show_Typ : Show Typ :=
  { show := showTyp' POuter }.

Fixpoint showExpr' prec (e : Term) :=
  match e with
  | Unit => "#"
  | Const n => show n
  | Pred e' =>
      parens prec POuter ("P " ++ showExpr' POuter e')
  | Plus e1 e2 =>
      parens prec PApp (showExpr' PApp e1 ++ "+" ++ showExpr' PInner e2)
  | Var x => "ID" ++ show x
  | Lam τ e' => parens prec POuter ("λ" ++ show τ ++ ". " ++ showExpr' POuter e')
  | App e1 e2 => parens prec PApp (showExpr' PApp e1 ++ " " ++ showExpr' PInner e2)
  end.

Instance show_Term : Show Term :=
  { show := showExpr' POuter }.

Fixpoint show_trace (tr : list (Term)) :=
  match tr with
  | [] => ""
  | (e)::tr' => 
      show e ++ " : " ++ show (typeOf [] e) ++ nl ++
      show_trace tr'
  end.

(** If you want to do shrinking, you can use the default 
    derived shrinkers, but make sure you filter the ill-typed
    candidates! *)
Derive Shrink for Typ.
Derive Shrink for Term.

Fixpoint shrink_expr (τ : Typ) (t : Term) : list Term :=
  List.filter (fun t' => typeOf [] t' = Some τ?)
              (shrink t ++ List.concat (List.map shrink (shrink t))).

(** Given a size, generate a type.  *)

(* Axiom gen_type : nat -> G Typ. *)
Fixpoint gen_type (n : nat) {struct n} : G Typ :=
  match n with
  | O => oneOf [ret TBase; ret TInt]
  | S n' => freq
             [
               (1, oneOf [ret TBase; ret TInt]); 
               (2, liftM2 TFun (gen_type n') (gen_type n'))
             ]
  end.

(** Given a size, a type environment, and a type, generate a term of the given
    type. You can allow this to fail if you want to backtrack. *)    
(* Axiom gen_expr : nat -> env -> Typ -> G (option Term). *)


Fixpoint get_var (t : Typ) (ρ : env) (n : nat) : list (G (option Term))  :=
  match ρ with
  | [] => []
  | t' :: ρ' =>
      let cand := get_var t ρ' (S n) in
      if (t' = t)? then (ret (Var n)) :: cand else cand
  end.


(* It's super annoying here that type error leads to infinite loop in type *)
(* checker *) 
Fixpoint gen_simple (ρ : env) (t : Typ) : G (option Term) :=
  let gen_var := get_var t ρ 0 in
  let gen_case := 
    match t with
    | TBase => ret (Some Unit)
    | TInt => i <- choose (0, 20);; ret (Some (Const i))
    | TFun t1 t2 =>
        (* any better way to do this? *)
        liftM (fun oe2 =>
                 match oe2 with
                 | Some e2 => Some (Lam t1 e2)
                 | None => None
                 end)
              (gen_simple (t1 :: ρ) t2)
    end in
  oneOf_ (ret None) (gen_case :: gen_var).

Definition liftOption {A B} (f : A -> B)  (o : option A) : option B :=
  match o with
  | Some x => Some (f x) 
  | _ => None
  end. 


Definition liftOption2 {A B} (f : A -> A -> B)  (o1 o2 : option A) : option B :=
  match o1, o2 with
  | Some x1, Some x2 => Some (f x1 x2)
  | _, _ => None
  end. 

Fixpoint gen_expr (n : nat) (ρ : env) (t : Typ) : G (option Term) :=
  let gen_sim := gen_simple ρ t in
  match n with
  | O => gen_sim
  | S n' =>
      let gen_app := 
            t' <- gen_type n';;
            oe1 <- gen_expr n' ρ (TFun t' t);; (* Operator *)
            oe2 <- gen_expr n' ρ t';;          (* Operand *)
            ret (liftOption2 App oe1 oe2) in
      match t with
      | TInt =>
          let gen_plus :=
                oi1 <- gen_expr n' ρ TInt;;
                oi2 <- gen_expr n' ρ TInt;;
                ret (liftOption2 Plus oi1 oi2) in
          let gen_pred :=
                oi <- gen_expr n' ρ TInt;;
                ret (liftOption Pred oi) in 
          freq [(1, gen_sim); (1, gen_pred); (2, gen_plus) ; (2, gen_app)]
      | TBase => oneOf [gen_sim; gen_app]
      | TFun t1 t2 =>
          let gen_fun :=
            oe1 <- gen_expr n' (t1 :: ρ) t2;;
            ret (liftOption (Lam t1) oe1) in
          freq [(1, gen_sim); (2, gen_fun); (1, gen_app)]
      end
  end.

(* Here is a sample way of using these, assuming you 
   have the generators implemented. You are welcome to 
   change the above signatures, but you'd have to change
   the invocation below accordingly: *)

Definition prop_soundness (c : Mutant) :=
  (* Feel free to change the fuel constants based on the 
     behavior of your generator! These represent my choices
     for reasonable "depth" limits for the generated
     types and terms. *)
  let type_fuel := 3 in
  let expr_fuel := 7 in
  forAll (gen_type type_fuel) (fun τ =>
  forAllMaybe (gen_expr expr_fuel [] τ) (fun e =>
  whenFail ("Type was: " ++ show τ ++ nl ++
            "Term was: " ++ show e ++ nl ++
            "With Type: " ++ show (typeOf [] e) ++ nl ++
            show_trace (snd (multistep 37 c e)))
           (soundness 37 c e))).


(* This should succeed *)
QuickChick (prop_soundness NoMutant).

(* These should fail *)

QuickChick (prop_soundness SubstNoLift).

QuickChick (prop_soundness SubstNoIncr).

QuickChick (prop_soundness SubstNoDecr).

QuickChick (prop_soundness SubstNoPred).

QuickChick (prop_soundness PlusBottom).

QuickChick (prop_soundness LiftAllVar).

QuickChick (prop_soundness LiftLamNoIncr).

QuickChick (prop_soundness LiftLamNoLift).

