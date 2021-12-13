From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.

(** ** Computable Reduction Semantics *)
Program Definition ctx_inj (t : term) : option (ctx * term) :=
  match t with
  | app t1 t2 =>
      match dc_value t1 with
        true => Some (@c_apparg t1 _ c_hole, t2)
      | false => Some (c_appfun c_hole t2, t1)
      end
  | tapp t1 T2 =>
      Some (c_typefun c_hole T2,  t1)
  | _ => None
  end.
Next Obligation.
  apply dc_value_implies_value. auto.
Qed.
Solve All Obligations with easy.

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

Fixpoint step' (n : nat) (t : term) {struct n} : option (option term) :=
  let f :=
    fun n t =>
      match ctx_inj t with
      | None => Some None
      | Some (c', t') => 
          match step' n t' with
          | Some (Some t'') => Some (Some (ctx_app c' t''))
          | r => r
          end
      end
  in
  match n with
  | 0 => None
  | S n => 
      match t with
      | app (abs _ t12) t2 =>
          if dc_value t2
          then Some (Some (subst t12 0 t2))
          else f n t
      | tapp (tabs T11 t12) T2 => Some (Some (subst_typ t12 0 T2))
      | _ => f n t
      end
  end.

Theorem step'_terminate :
  forall t, exists o, step' (measure_term t) t = Some o.
Proof.
  induction t; try solve [cbn; eauto].
  - destruct t1; try solve [simpl; eauto].
    + destruct (dc_value t2) eqn:Et2. simpl. rewrite Et2. eauto. 
      destruct (ctx_inj (app (abs t t1) t2)) eqn:Ct.
      eexists. cbn. 
          
Definition step (t : term) : option term.
  match step (measure_term t)
  
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
      * cbn in H.
    + 
      

Lemma red_is_step : forall t t', red t t' -> step t = Some t'.
Admitted.
    
Lemma red_iff_step : forall t t', red t t' <-> step t = Some t'.
Proof.
  split. apply red_is_step. apply step_is_red.
Qed.

