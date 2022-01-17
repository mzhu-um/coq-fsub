From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.

(** * Reduction: Computatble Reduction Semantics *)

(** ** Computable Reduction Semantics *)
Definition ctx_inj (t : term) : option (ctx * term).
  refine
    (match t with
     | app t1 t2 => _
     | tapp t1 T2 =>
         Some (c_typefun c_hole T2, t1)
     | _ => None
     end).
  destruct (dc_value t1) eqn: Evalue.
  - refine (Some (@c_apparg t1 _ c_hole, t2)).
    apply (dc_value_implies_value _ Evalue).
  - refine (Some (c_appfun c_hole t2, t1)).
Defined.

Eval cbn in (ctx_inj (tapp (var 0) top)).

Fixpoint measure_term (t : term) : nat :=
  match t with
  | var _ => 1 
  | abs _ t' => 1 + measure_term t'
  | app t1 t2 => 1 + measure_term t1 + measure_term t2
  | tabs _ t2 => 1 + measure_term t2
  | tapp t1 _ => 1 + measure_term t1
  end.

Lemma measure_term_le_ctx_inj : forall c t t',
    Some (c, t') = ctx_inj t -> measure_term t' < measure_term t.
Proof.
  intros until t. destruct t; intros; cbn in *; try congruence. 
  - destruct t1; cbn in *; inversion H; clear H; subst; cbn; lia.
  - inversion H; clear H; subst; lia. 
Qed.

Program Fixpoint step (t : term) {measure (measure_term t)} : option term :=
  match t with
  | app (abs _ t12) t2 =>
      if dc_value t2 then Some (subst t12 0 t2) else
        step_other t
  | tapp (tabs T11 t12) T2 => Some (subst_typ t12 0 T2)
  | _ => step_other t 
  end
with
step_other t {measure (measure_term t)} :=
  match ctx_inj t with
  | None => None
  | Some (c', t') => 
      match step t' with
      | Some t'' => Some (ctx_app c' t'')
      | None => None
      end
  end .

Next Obligation.
  cbn; lia.
Qed.
Next Obligation.
  eapply measure_term_le_ctx_inj. eauto.
Qed.
Solve All Obligations with easy.

Compute (step (app
                 (abs top (var 0))
                 (abs top (var 0)))).
Compute (step (abs top (var 0))).

(* Require Extraction. *)
(* Extraction "step.ml" step. *)

Lemma step_app_value : forall T t1 t2,
    dc_value t2 = true -> step (app (abs T t1) t2) = Some (subst t1 0 t2).
Proof.
Admitted.  

(** ** Equivalence in Reduction Semantics *)
Lemma step_is_red : forall t t', step t = Some t' -> red t t'.
Proof with intuition. 
  induction t; intros t'; simpl; intros.
  - cbn in H; congruence.
  - cbn in H; congruence.
  - destruct t1.
    + cbn in H. congruence.
    + destruct (dc_value t2) eqn:Et2.
      * pose proof Et2 as Et2'.
        apply dc_value_implies_value in Et2.
        rewrite step_app_value in H. inversion H; subst. constructor.
        assumption.
        assumption.
      * move: H.
Admitted.

Lemma red_is_step : forall t t', red t t' -> step t = Some t'.
Admitted.
    
Lemma red_iff_step : forall t t', red t t' <-> step t = Some t'.
Proof.
  split. apply red_is_step. apply step_is_red.
Qed.


(** Fixpoint iteration *)
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

