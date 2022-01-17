From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.
 
(** * ReductionN: Computatble Reduction Semantics with Fuel *)

(** ** Computable Reduction Semantics *)

Fixpoint ctx_inj (t : term) : option (ctx * term).
  refine
    (match t with
     | app t1 t2 => _
     | tapp t1 T2 =>
         if dc_value t1 then ret (c_hole, t)
         else '(c1, t1) <- ctx_inj t1;; ret (c_typefun c1 T2, t1)
     | _ => ret (c_hole, t)
     end).
  destruct (reflect_value t1).
  - (* [t1] is a value, inject context on [t2] *)
    refine ('(c2, t2) <- ctx_inj t2;; ret (c_apparg v c2, t2)).
  - (* [t1] is not a value, inject context on [t1] *)
    refine ('(c1, t1) <- ctx_inj t1;; ret (c_appfun c1 t2, t1)).
Defined.

Eval cbn in (ctx_inj (app (app (abs top (var 0)) (abs top (var 0)))
                          (abs top (var 0)))).

Eval cbn in (ctx_inj (app (abs top (var 0))
                          (app (abs top (var 0)) (abs top (var 0))))).

Eval cbn in (ctx_inj (tapp (var 0) top)).

Fixpoint step (n : nat) (t : term) {struct n} : result :=
  match n with
  | O => OutOfFuel
  | S n =>            
      match t with
      | app (abs _ t12) t2 =>
          if dc_value t2 then Result (Some (subst t12 0 t2))
          else step_ctx n t
      | tapp (tabs T11 t12) T2 => Result (Some (subst_typ t12 0 T2))
      | _ => step_ctx n t
      end
  end
with
step_ctx n t {struct n} :=
  match n with
  | O => OutOfFuel
  | S n =>            
      match ctx_inj t with
      | None => Result None
      | Some (c', t') => 
          match step n t' with
          | Result (Some t'') => Result (Some (ctx_app c' t''))
          | rst => rst
          end
      end
  end.

Fixpoint step' (n : nat) (t : term) {struct n} : result :=
  let step_ctx' n t :=
    match ctx_inj t with
    | None => Result None
    | Some (c', t') => 
        match step' n t' with
        | Result (Some t'') => Result (Some (ctx_app c' t''))
        | rst => rst
        end
    end in
  match n with
  | O => OutOfFuel
  | S n =>            
      match t with
      | app (abs _ t12) t2 =>
          if dc_value t2 then Result (Some (subst t12 0 t2))
          else step_ctx' n t
      | tapp (tabs T11 t12) T2 => Result (Some (subst_typ t12 0 T2))
      | _ => step_ctx' n t
      end
  end.

Print step'.

Fixpoint measure_term (t : term) : nat :=
  3 +
    match t with
    | var _ => 0
    | abs _ t' => measure_term t'
    | app t1 t2 => measure_term t1 + measure_term t2
    | tabs _ t2 => measure_term t2
    | tapp t1 _ => measure_term t1
    end.


(* 
Lemma measure_term_le_ctx_inj : forall c t t',
    c <> c_hole ->
    ctx_inj t = Some (c, t') ->
    S (S (measure_term t')) <= measure_term t.
Proof.
  intros until t. induction t; cbn; intros *;
    try solve[intros * Hctx; inv0; done].
  - destruct (reflect_value t').
    + solveR ctx_inj. destruct p. intros. inversion H; subst.
      specialize IHt1 with t'.
      specialize IHt2 with t'.

Qed.
 *)

Ltac caseN n1 n2 :=
  destruct n1, n2; try lia; try solve[cbn; congruence].

Ltac caseNs n1 n2 := 
  caseN n1 n2; cbn; solveR step.

Ltac rewriteL H :=
  rewrite H; try lia; try exact.

Ltac solveSp IH n1 v :=
  match goal with
  | [ |- context [(step ?n2 ?t)]] =>
      let H := fresh "Hrewrite" in
      specialize IH with n1 n2 t v as H;
      rewrite H; try lia; try exact
  end.

Ltac solveRSp f IH n1 v :=
  solveR f; solveSp IH n1 v.

Lemma step_widen :
  forall  n1 n2 t o,
    n1 <= n2 -> step n1 t = Result o -> step n2 t = Result o.
Proof. (* This one is boring without [Ltac] *)
  intros n1. induction (lt_wf n1) as [n1 _ IHn1]; intros * Hle.
  destruct n1. {destruct n2. 1:exact. cbn; congruence.}
  destruct n2. 1:lia. cbn.
  destruct t; try solve [caseNs n1 n2; solveSp IHn1 n1 v].
  - destruct t1; try solveVR; 
      try solve
          [caseN n1 n2; unfold step_ctx; fold step;
           solveR ctx_inj; destruct p; solveRSp step IHn1 n1 v].
  - destruct t;
      try solve
          [caseN n1 n2; unfold step_ctx; fold step;
           solveR ctx_inj; destruct p; solveRSp step IHn1 n1 v].
Qed.

(*

Ltac solveCtx :=
  match goal with
  | [ |- context [(ctx_inj ?t')]] =>
      let Hctx := fresh "Hctx" in
      let c := fresh "c" in
      let t := fresh "t" in
      destruct (ctx_inj t') as [[c t]|] eqn:Hctx; try eauto;
      apply measure_term_le_ctx_inj in Hctx
  end.

Ltac solveSp2 IH :=
  match goal with
  | [ |- context [(step ?n ?t)]] =>
      let H := fresh "Hrewrite" in
      let x := fresh "x" in
      specialize IH with n t;
      destruct IH as [x H]; try lia; rewrite H; destruct x; eauto
  end.

Theorem step_terminates :
  forall n t, (n >= (measure_term t)) -> exists o, step n t = Result o.
Proof with eauto.
  intros n. induction (lt_wf n) as [n _ IH]; intros;
    try solve[cbn; eauto].
  destruct n. { destruct t; cbn in H; try lia. } cbn. 
  destruct n. { destruct t; cbn in H; try lia. } cbn.
  destruct t; try solveCtx; try (solveSp2 IH).
  - destruct t1; try solveDv; try solveCtx; try (solveSp2 IH); eauto.
  - destruct t; try solveDv; try solveCtx; try (solveSp2 IH); eauto.
Qed.
*)

Ltac solveRctx :=
  solveR ctx_inj;
  match goal with
  | [p: ctx * term |- _] => destruct p
  end.

Lemma ctx_inj_implies_ctx_app :
  forall t t' c, ctx_inj t = Some(c, t') -> ctx_app c t' = t.
Proof.
  induction t; cbn; intros *; inv0; auto; move: H1.
  - destruct (reflect_value t1); solveRctx; inv0; cbn;
      [rewrite IHt2 | rewrite IHt1]; exact.
  - solveVR. 1:inv0; reflexivity.
    + solveRctx. inv0. cbn. rewrite IHt; auto.
Qed.
      
Lemma ctx_app_implies_ctx_inj :
  forall t t' c, ctx_app c t = t' -> ctx_inj t' = Some(c, t). 
Proof.
  induction c; cbn; inv0; auto.
Abort.

(** ** Equivalence in Reduction Semantics *)
Theorem red_implies_step :
  forall t t',
    red t t' -> 
    exists n, step n t = Result (Some t').
Proof.
  intros * H. exists (measure_term t). induction H; step measure_term.
  (* use [remember] to control # of the step I reduce! *)
  - remember (3 + measure_term t12 + measure_term t2) as n; cbn. solveVI.
  - cbn. reflexivity.
  - induction c.
    + (* c_hole *)
      cbn. exact.
    + (* c_appfun *)
      step ctx_app. step measure_term.
      remember (3 + (measure_term (ctx_app c t1) + measure_term t)) as n.
      remember (2 + (measure_term (ctx_app c t1) + measure_term t)) as n'.
      replace n with (S n') by lia. cbn. unfold step_ctx.
      
      cbn. destruct (ctx_app c t1).
      * remember (S (measure_term (var n0) + measure_term t)) as n'.
        replace n with (S n') by lia. cbn.

Abort.

ctx_inj (ctx_app c t1) = Some (t1, c).
      
Lemma step_ctx_app_ctx :
  forall n c t1 t,
    step (measure_term t1) t1 = Result (Some t1') ->
    step_ctx n (app (ctx_app c t1) t) = Result (Some )



Lemma step_implies_red :
  forall t t',
    step (measure_term t) t = Result (Some t') ->
    red t t'.
Proof.
  induction t; intros t'.
  - discriminate.
  - discriminate.
  - destruct t1.
Abort.
  

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

