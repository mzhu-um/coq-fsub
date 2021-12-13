From FSUB Require Import QCLibs.
From FSUB Require Import FSub.

(** ** Printer *)

Fixpoint show_typ' (T : typ) :=
  match T with
  | tvar n => ("<" ++ show n ++ ">")%string
  | top => "Top"%string
  | arrow T1 T2 =>
      ("(" ++ show_typ' T1 ++ " -> " ++ show_typ' T2 ++ ")")%string
  | all T1 T2 => ("{∀" ++ show_typ' T1 ++ " . " ++ show_typ' T2 ++ "}")%string
  end.

Instance show_typ : Show typ :=
  { show := show_typ' }.

Fixpoint show_term' (t : term) :=
  match t with
  | var n => ("[id " ++ show n ++  "]")%string
  | abs T t => ("(λ : " ++ show T ++". " ++ show_term' t ++ ")")%string
  | app t1 t2 => ("(" ++ show_term' t1 ++ " " ++ show_term' t2 ++ ")")%string
  | tabs T1 t2 => ("(Λ " ++  show T1 ++ ". " ++ show_term' t2 ++ ")")%string
  | tapp t1 T2 => ("(" ++ show_term' t1 ++ " " ++ show T2 ++ ")")%string
  end.

Instance show_term : Show term :=
  { show := show_term' }.

(** ** Decidable Equality *)
Instance Dec_eq_opt (A : Type) (m n : option A)
         `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.
Instance dec_eq_typ (T1 T2 : typ) : Dec (T1 = T2).
Proof. dec_eq. Defined.

Instance dec_eq_term (t1 t2 : term) : Dec (t1 = t2).
Proof. dec_eq. Defined.




Inductive result {X : Type} : Type :=
| Result (v : X)
| OutOfFuel
.


(** ** Well Formedness *)
Fixpoint dc_wf_typ (e : env) (T : typ) {struct T} : bool :=
  match T with
  | tvar X      => ((get_bound e X) <> None ?)
  | top         => true
  | arrow T1 T2 => (dc_wf_typ e T1) && (dc_wf_typ e T2)
  | all T1 T2   => (dc_wf_typ e T1) && (dc_wf_typ (ebound e T1) T2)
  end.

Lemma dc_wf_typ_correct (e : env) (T : typ) :
  wf_typ e T <-> dc_wf_typ e T = true.
Proof with intuition.
  split; intro; cbn. 
  - generalize dependent e.
    induction T; intros; cbn in *...
    + destruct (get_bound e n) eqn:E; try congruence. 
      destruct t... 
  - generalize dependent e.
    induction T; intros; cbn in *;
      try solve [apply andb_prop in H; intuition]. 
    + destruct (get_bound e n)... destruct t; cbv in H; congruence.
    + trivial.
Qed. 


Fixpoint dc_wf_term (e : env) (t : term) {struct t} : bool :=
  match t with
  | var x      => get_var e x <> None ?
  | abs T1 t2  => dc_wf_typ e T1  && dc_wf_term (evar e T1) t2
  | app t1 t2  => dc_wf_term e t1 && dc_wf_term e t2
  | tabs T1 t2 => dc_wf_typ e T1  && dc_wf_term (ebound e T1) t2
  | tapp t1 T2 => dc_wf_term e t1 && dc_wf_typ e T2
  end.

Hint Resolve -> dc_wf_typ_correct : code.
Hint Resolve <- dc_wf_typ_correct : code.

Lemma dc_wf_term_correct (e : env) (t : term) :
  wf_term e t <-> dc_wf_term e t = true.
Proof with intuition. 
  split; intros; cbn. 
  - generalize dependent e.
    induction t; intros; cbn in *...
    + destruct (get_var e n) eqn:E; try congruence. 
      destruct t...
  - generalize dependent e.
    induction t; intros; cbn in *;
      try solve [apply andb_prop in H; intuition]...
    + destruct (get_var e n)... 
      destruct t; cbv in H; congruence.
Qed. 

Fixpoint dc_wf_env (e : env) : bool :=
  match e with
    empty      => true
  | evar e T   => dc_wf_typ e T && dc_wf_env e
  | ebound e T => dc_wf_typ e T && dc_wf_env e
  end.

Lemma dc_wf_env_correct (e : env) :
  wf_env e <-> dc_wf_env e = true.
Proof with intuition.
  split; intros.
  - induction e; cbn in *...
  - induction e; cbn in *; auto; split; apply andb_prop in H...
Qed.

(** ** Type Checking *)
Fixpoint count_tvar (e : env) : nat :=
  match e with
  | empty => O
  | evar e _ => count_tvar e
  | ebound e t => S (count_tvar e)
  end.

Fixpoint sub_check (e : env) (T1 T2 : typ) (n : nat)
  : @result bool :=
  match n with
  | O => OutOfFuel 
  | S n =>  
      match T1, T2 with
      | _, top => Result (dc_wf_env e && dc_wf_typ e T1)%bool
      | tvar X1, tvar X2 =>
          Result (dc_wf_env e && (X1 = X2 ?) && dc_wf_typ e (tvar X1))%bool
      | tvar X1, _ =>
          match get_bound e X1 with
          | None => Result false 
          | Some T1' =>
              sub_check e T1' T2 n
          end
      | arrow S1 S2, arrow T1 T2 =>
          match sub_check e T1 S1 n with
          | Result b1 => match sub_check e S2 T2 n with
                         | Result b2 => Result (b1 && b2)%bool
                         | _ => OutOfFuel
                         end
          | _ => OutOfFuel
          end
      | all S1 S2, all T1 T2 => 
          match sub_check e T1 S1 n with
          | Result b1 => match sub_check  (ebound e T1) S2 T2 n with
                       | Result b2 => Result (b1 && b2)%bool
                       | _ => OutOfFuel
                       end
          | _ => OutOfFuel
          end
      | _, _ => Result false
      end
  end.

Fixpoint get_typ (e : env) (t : term) (fuel : nat) : @result (option typ) :=
  match t with
  | var x => Result (get_var e x)
  | abs T1 t2 =>
      match get_typ (evar e T1) t2 fuel with
      | Result (Some T2) => Result (Some (arrow T1 T2))
      | rst => rst
      end
  | app t1 t2 =>
      match get_typ e t1 fuel with
      | Result (Some (arrow T11 T12)) =>
          match get_typ e t2 fuel with
          | Result (Some T2) => Result (if T11 = T2 ? then Some T12 else None)
          | rst => rst
          end
      | rst => rst
      end
  | tabs T1 t2 =>
      match get_typ (ebound e T1) t2 fuel with
      | Result (Some T2) => Result (Some (all T1 T2))
      | rst => rst
      end
  | tapp t1 T2 => 
      match get_typ e t1 fuel with
      | Result (Some (all T11 T12)) =>
          match sub_check e T2 T11 fuel with
          | Result true => Result (Some (tsubst T12 0 T2))
          | Result false => Result None
          | _ => OutOfFuel
          end
      | rst => rst
      end
  end.


Definition type_check (e : env) (t : term) (T : typ) (fuel : nat) :
  @result bool :=
  match get_typ e t fuel with
  | Result (Some T') => sub_check e T' T fuel 
  | Result None => Result false
  | _ => OutOfFuel
  end.


(** ** Value *)
Definition dc_value (t : term) : bool :=
  match t with
  | abs _ _  => true
  | tabs _ _ => true
  | _        => false
  end.

Lemma dc_value_implies_value : forall t, dc_value t = true -> value t.
Proof. intros t. destruct t; cbn; auto. Qed.

Lemma value_implies_dc_value : forall t, value t -> dc_value t = true. 
Proof. intros t. destruct t; cbn; auto. Qed.

Lemma dc_value_correct (t : term) :
  dc_value t = true <-> value t.
Proof.
  split. exact (dc_value_implies_value _). exact (value_implies_dc_value _).
Qed.


