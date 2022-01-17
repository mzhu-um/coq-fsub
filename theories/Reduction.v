From FSUB Require Import
     QCLibs
     FSub
     Decidable.
(** * Reduction: Semantics *)

(** ** Alternative Semantics
    
    The equivalence between reduction relation and its computable function is
    hard to prove. 

 *)         
Fixpoint step' (t : term) : option term :=
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

Lemma red'_not_value :
  forall t1 t2, red' t1 t2 -> ~ value t1.
Proof.
  intros * Hred Hcontra.
  destruct t1; cbn in Hcontra; intuition; inversion Hred.
Qed.

Lemma red'_implies_step' :
  forall t1 t2, red' t1 t2 -> step' t1 = Some t2.
Proof.
  intros * H; induction H; cbn.
  - solveVI.
  - reflexivity.
  - rewrite IHred'.
    destruct t1; try solve [inversion IHred']; solveVR; inversion v.
  - rewrite IHred'. destruct t1; try solve[solveVI].
    apply red'_not_value in H0.
    destruct (reflect_value t2); [congruence | reflexivity].
  - rewrite IHred'.
    destruct t1; try reflexivity.
    apply red'_not_value in H.
    cut (value (tabs t t1)); [congruence | exact].
Qed.

Lemma step'_implies_red' :
  forall t1 t2, step' t1 = Some t2 -> red' t1 t2.
Proof.
  intros t1.
  induction t1; intros *; try solve[inv0]; cbn;
    [destruct t1_1 | destruct t1]; try solveVR;
    try solve[solveR step'; inv0; constructor; cbn ; intuition];
    try solve[inv0; constructor; auto].
Qed.

Theorem step'_correct :
  forall t1 t2, step' t1 = Some t2 <-> red' t1 t2.
Proof.
  intros. split; [apply step'_implies_red' | apply red'_implies_step'].
Qed. 
