From FSUB Require Import
     QCLibs
     FSub.

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
  | var n => ("[" ++ show n ++  "]")%string
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

(** ** Fuel Result *)
Inductive result {X : Type} : Type :=
| Result (v : X)
| OutOfFuel
.
Instance Dec_eq_result (A : Type) (m n : @result A)
         `{_ : forall (x y : A), Dec (x = y)} : Dec (m = n).
Proof. dec_eq. Defined.

Definition show_result' {A} `{Show A} (r : @result A) : string :=
  match r with
  | Result v => show v
  | _ => "Out Of Fuel"%string
  end.

Instance show_result : Show result :=
  { show := show_result' }.

(** ** Well Formedness *)
Fixpoint dc_wf_typ (e : env) (T : typ) {struct T} : decidable (wf_typ e T). 
  refine
    (match T with
     | tvar X      => _
     | top         => left I
     | arrow T1 T2 => _
     | all T1 T2   => _
     end); cbn.
  - destruct ((get_bound e X)) eqn:Hbound.
    + left. intros H. inversion H.
    + right. exact.
  - destruct (dc_wf_typ e T1). 2: right;intuition.
    destruct (dc_wf_typ e T2); [left | right]; intuition.
  - destruct (dc_wf_typ e T1). 2: right;intuition.
    destruct (dc_wf_typ (ebound e T1) T2); [left | right]; intuition.
Defined.

Fixpoint dc_wf_term (e : env) (t : term) {struct t} : decidable (wf_term e t).
  destruct t; cbn.
  - destruct (get_var e n); [left | right].
    + discriminate.
    + congruence.
  - destruct (dc_wf_typ e t). 2:right; intuition.
    destruct (dc_wf_term (evar e t) t0); [left | right]; intuition.
  - destruct (dc_wf_term e t1). 2:right; intuition.
    destruct (dc_wf_term e t2); [left | right]; intuition.
    Show Proof.
  - destruct (dc_wf_typ e t). 2:right; intuition.
    destruct (dc_wf_term (ebound e t) t0); [left | right]; intuition.
  - destruct (dc_wf_term e t). 2:right; intuition.
    destruct (dc_wf_typ e t0); [left | right]; intuition.
Defined.

Fixpoint dc_wf_env (e : env) : decidable (wf_env e).
  refine
    (match e with
     | empty      => left I
     | evar e T
     | ebound e T =>
         _
     end); cbn.
  - destruct (dc_wf_typ e T). 2: right; intuition.
    + destruct (dc_wf_env e); [left | right]; intuition.
  - destruct (dc_wf_typ e T). 2: right; intuition.
    + destruct (dc_wf_env e); [left | right]; intuition.
Defined.

(** ** Subtyping *)
Fixpoint sub_check (e : env) (T1 T2 : typ) (n : nat)
  : @result bool :=
  match n with
  | O => OutOfFuel 
  | S n =>  
      match T1, T2 with
      | _, top =>               (** SA_Top *)
          Result (dc_wf_env e && dc_wf_typ e T1)%bool
      | tvar X1, _ =>           (** SA_Refl_TVar  *)
          if (tvar X1 = T2) ?
          then Result (dc_wf_env e && dc_wf_typ e (tvar X1))%bool
          else 
            match get_bound e X1 with
            | None => Result false 
            | Some T1' =>
                sub_check e T1' T2 n
            end
      | arrow S1 S2, arrow T1 T2 =>
          match sub_check e T1 S1 n with
          | Result true => sub_check e S2 T2 n
          | r => r
          end
      | all S1 S2, all T1 T2 => 
          match sub_check e T1 S1 n with
          | Result true => sub_check (ebound e T1) S2 T2 n
          | r => r
          end
      | _, _ => Result false
      end
  end.

(** Convert boolean result equivalence to relation *)
Ltac invR :=
  match goal with
  | [H : Result ?P = Result true |- _] =>
      let H' := fresh "Hconj" in
      (destruct P eqn:H' ; try congruence; try (apply andb_prop in H'))
  | [|- (Result ?P = Result true) -> _] =>
      let H' := fresh "Hconj" in
      (destruct P eqn:H'; try congruence; try (apply andb_prop in H'); intros)
  | [H : Result ?P = Result ?Q |- _] =>
      (inversion H; clear H; subst)
  | [|- Result ?P = Result ?Q -> _] =>
      let H' := fresh "HinvR" in (move=> H'; inversion H'; clear H'; subst)
  | [|- ?P = Result ?Q -> _] =>
      let H' := fresh "HinvR" in (destruct P eqn:H'; try exact; try congruence)
  end.



Definition reflect_wf_term e t : reflect (wf_term e t) (dc_wf_term e t).
  apply sumboolP.
Defined.

Definition reflect_wf_typ e T : reflect (wf_typ e T) (dc_wf_typ e T).
  apply sumboolP.
Defined.

Definition reflect_wf_env e : reflect (wf_env e) (dc_wf_env e).
  apply sumboolP.
Defined.

Ltac solveWfE :=
  intuition;
  match goal with
  | [ |- (wf_typ ?E ?T)] =>
      apply (elimT (reflect_wf_typ E T)); auto
  | [ |- (wf_term ?E ?T)] =>
      apply (elimT (reflect_wf_term E T)); auto
  | [ |- (wf_env ?E)] =>
      apply (elimT (reflect_wf_env E)); auto
  end.

Ltac solveWfI' :=
  match goal with
  | [ |- context [dc_wf_env ?E]] => 
      rewrite (introT (reflect_wf_env E)); auto
  | [ |- context[dc_wf_typ ?E ?T]] => 
      rewrite (introT (reflect_wf_typ E T)); auto
  | [ |- context[dc_wf_term ?E ?t]] => 
      rewrite (introT (reflect_wf_term E t)); auto
  | _ => fail
  end; repeat solveWfI'.
  
Ltac solveWfI :=
  intuition; solveWfI'.

Theorem sub_check_implies_sub :
  forall n E T1 T2,
    sub_check E T1 T2 n = Result true ->
    sub E T1 T2. 
Proof with solveWfE.
  induction n; intros *. cbn; congruence.
  - destruct T1.
    unfold sub_check; destruct dec as [Hdec | Hdec].
    + inversion Hdec; subst. invR; constructor...
    + fold sub_check.
      destruct T2; intros;
        try solve
            [ destruct (get_bound E n0) eqn:H3;
              [ rename t into T1; apply SA_Trans_TVar with T1; intuition
              | congruence ]].
      invR. constructor...
    + destruct T2; cbn; try congruence. invR. constructor...
    + destruct T2 eqn:E2; try solve [cbn; congruence].
      * unfold sub_check; invR. constructor...
      * destruct (sub_check E t1 T1_1 n) as [[|]|] eqn:E3; cbn; rewrite E3;
          try congruence. constructor...
    + destruct T2 eqn:E2; try solve [cbn; congruence].
      * unfold sub_check; invR. constructor...
      * destruct (sub_check E t1 T1_1 n) as [[|]|] eqn:E3; cbn; rewrite E3;
          try congruence. constructor...
Qed.        

Ltac solveR f :=
  match goal with
  | [ |- context [(f ?x ?y ?z ?a)]] =>
      let H1 := fresh "Hslv" in
      (destruct (f x y z a) as [[|]|] eqn:H1;
       try solve [intros; congruence])
  | [ |- context [(f ?x ?y ?z)]] =>
      let H1 := fresh "Hslv" in
      let T := fresh "T" in
      (destruct (f x y z) as [[T|]|] eqn:H1;
       try solve [intros; congruence])
  | [ |- context [(f ?x ?y)]] =>
      let H1 := fresh "Hslv" in
      (destruct (f x y) as [|] eqn:H1;
       try solve [intros; congruence])
  | [ |- context [(f ?x)]] =>
      let H1 := fresh "Hslv" in
      (destruct (f x) as [|] eqn:H1;
       try solve [intros; congruence])
  | _ => fail
  end.

Lemma sub_check_fuel_widen :
  forall n1 n2 E T1 T2,
    n1 <= n2 ->
    sub_check E T1 T2 n1 = Result true ->
    sub_check E T1 T2 n2 = Result true.
Proof.
  induction n1; intros * Hle. 1: cbn; congruence.
  destruct n2 as [|n2]. 1: lia.
  unfold sub_check. fold sub_check.
  destruct T1; try exact.
  - destruct T2; try intuition;
      try solve [destruct dec as [Hdec | Hdec]; try exact;
                 destruct (get_bound E n); try congruence; intuition].
  - destruct T2; try intuition.
    move: H. solveR sub_check. apply (IHn1 n2) in Hslv. 2:lia.
    intros. rewrite Hslv. apply (IHn1 n2). lia. exact.
  - destruct T2; try intuition.
    move: H. solveR sub_check. apply (IHn1 n2) in Hslv. 2:lia.
    intros. rewrite Hslv. apply (IHn1 n2). lia. exact.
Qed.

Theorem sub_implies_sub_check :
  forall E T1 T2,
    sub E T1 T2 -> 
    exists n, sub_check E T1 T2 n = Result true. 
Proof with solveWfI.
  intros * H. apply sub_wf in H as Hwf. induction H.
  - exists 1. unfold sub_check. 
    destruct S...
  - exists 1. unfold sub_check. destruct dec; try congruence...
  - apply sub_wf in H0. destruct IHsub as [n' IHsub]; intuition.
    exists (S n'). unfold sub_check. destruct dec as [Hdec | Hdec].
    + inversion Hdec; subst... 
    + fold sub_check. destruct T; try solve [rewrite H; auto]...
  - intuition. cbn in H3, H4; intuition. 
    destruct (H2, H5) as [[n1 Hsub1] [n2 Hsub2]].
    exists (S (n1 + n2)). cbn.
    apply (sub_check_fuel_widen _ (n1 + n2)) in Hsub1. 2: lia.
    apply (sub_check_fuel_widen _ (n1 + n2)) in Hsub2. 2: lia.
    rewrite Hsub1. exact.
  - apply sub_wf in H0. intuition. cbn in H2, H6. intuition.
    destruct (H3, H7) as [[n1 Hsub1] [n2 Hsub2]].
    exists (S (n1 + n2)). cbn.
    apply (sub_check_fuel_widen _ (n1 + n2)) in Hsub1. 2: lia.
    apply (sub_check_fuel_widen _ (n1 + n2)) in Hsub2. 2: lia.
    rewrite Hsub1. exact.
Qed.

Theorem sub_check_correct :
  forall e T1 T2,
    sub e T1 T2 <-> exists n, sub_check e T1 T2 n = Result true.
Proof.
  intros. split.
  - apply sub_implies_sub_check.
  - intros [n H].  apply sub_check_implies_sub with n. exact.
Qed.

(** ** Type Checking *)
Fixpoint promote_tvar (e : env) (T : typ) (fl : nat) : result :=
  if dc_wf_env e && dc_wf_typ e T then 
    match T with
    | tvar n =>
        match get_bound e n with
        | Some T =>
            match fl with
            | O => OutOfFuel
            | S fl => promote_tvar e T fl
            end
        | _ => Result None
        end
    | _ => Result (Some T)
    end
  else Result None.

Ltac solveWfR :=
  match goal with
  | [ |- context [dc_wf_env ?E]] => 
      destruct (reflect_wf_env E); auto
  | [ |- context[dc_wf_typ ?E ?T]] => 
      destruct (reflect_wf_typ E T); auto
  | [ |- context[dc_wf_term ?E ?t]] => 
      destruct (reflect_wf_term E t); auto
  | _ => fail
  end; repeat solveWfR.

  
Lemma promote_tvar_implies_sub :
  forall fl e T T',
    promote_tvar e T fl = Result (Some T') -> sub e T T'.
Proof with (solveWfR; cbn; try congruence).
  induction fl; intros *.
  - (* O *)
    unfold promote_tvar...
    destruct T; try solve [intros; invR; apply sub_reflexivity; intuition].
    destruct (get_bound e n); congruence.
  - (* S fl *)
    unfold promote_tvar... fold promote_tvar.
    destruct T; try solve [invR ; apply sub_reflexivity; intuition].
    destruct (get_bound e n) eqn:Hbound. 2: congruence.
    intros. apply IHfl in H.
    apply SA_Trans_TVar with t; intuition.
Qed.  

Fixpoint get_typ (e : env) (t : term) (fuel : nat) : @result (option typ) :=
  match t with
  | var x =>
      if dc_wf_env e
      then Result (get_var e x)
      else Result None
  | abs T1 t2 =>
      match get_typ (evar e T1) t2 fuel with
      | Result (Some T2) => Result (Some (arrow T1 T2))
      | rst => rst
      end
  | app t1 t2 =>
      match get_typ e t1 fuel with
      | Result (Some T1) =>
          match promote_tvar e T1 fuel with
          | Result (Some (arrow T11 T12)) =>
              match get_typ e t2 fuel with
              | Result (Some T2) => 
                  match sub_check e T2 T11 fuel with
                  | Result true => Result (Some T12)
                  | Result false => Result None
                  | _ => OutOfFuel
                  end
              | rst => rst
              end
          | Result _ => Result None
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
      | Result (Some T1) =>
          match promote_tvar e T1 fuel with
          | Result (Some (all T11 T12)) =>
              match sub_check e T2 T11 fuel with
              | Result true => Result (Some (tsubst T12 0 T2))
              | Result false => Result None
              | _ => OutOfFuel
              end
          | Result _ => Result None
          | rst => rst
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

Hint Resolve sub_check_implies_sub : code. 

Theorem get_typ_implies_typing :
  forall t e T n, get_typ e t n = Result (Some T) -> typing e t T.
Proof.
  induction t; intros *; cbn.
  - solveWfR. 2:congruence.
    intros. inversion H. constructor; intuition.
  - solveR get_typ. invR. constructor. eauto. 
  - solveR get_typ. rename Hslv into Htyp.
    solveR promote_tvar. rename Hslv into Htyp0.
    destruct T1; try congruence.
    solveR get_typ. rename Hslv into Htyp1.
    solveR sub_check; intros. invR. rename Hslv into Hsub.
    (* convert all dec to relations  *)
    apply promote_tvar_implies_sub in Htyp0.
    apply sub_check_implies_sub in Hsub. 
    apply IHt1 in Htyp. apply IHt2 in Htyp1.
    apply T_App with T1_1.
    apply T_Sub with T0; exact. 
    apply T_Sub with T1; exact.
  - solveR get_typ. invR. constructor. eauto.
  - solveR get_typ. rename Hslv into Htyp.
    solveR promote_tvar. rename Hslv into Htyp0.
    destruct T1; try congruence.
    solveR sub_check. rename Hslv into Hsub. invR.
    apply IHt in Htyp. apply promote_tvar_implies_sub in Htyp0.
    apply sub_check_implies_sub in Hsub.
    econstructor. 2: exact Hsub. eapply T_Sub. exact Htyp. exact. 
Qed.

Hint Resolve get_typ_implies_typing : code.

Theorem type_check_implies_typing :
  forall n t e T, type_check e t T n = Result true -> typing e t T.
Proof with intuition. 
  intros *. unfold type_check. solveR get_typ.
  intros. apply T_Sub with T0.
  exact (get_typ_implies_typing _ _ _ _ Hslv).
  exact (sub_check_implies_sub _ _ _ _ H).
Qed.

Lemma promote_tvar_fuel_widen :
  forall n1 n2 E T1 T2,
    n1 <= n2 ->
    promote_tvar E T1 n1 = Result (Some T2) ->
    promote_tvar E T1 n2 = Result (Some T2).
Proof with (solveWfR; cbn; try congruence).
  induction n1; intros * Hle.
  - destruct n2. exact.
    unfold promote_tvar... fold promote_tvar.
    destruct T1; try exact.
    destruct (get_bound E n); congruence.
  - destruct n2. lia.
    unfold promote_tvar... fold promote_tvar.
    destruct T1; try exact.
    destruct (get_bound E n). 2:congruence.
    intuition.
Qed.
Hint Rewrite sub_check_fuel_widen : code.

Ltac solveRe f H n1 n2 :=
  solveR f; 
  match goal with 
  | [ Htyp : _ |- _ ] =>
      apply (H n1 n2) in Htyp; try lia; rewrite Htyp; clear Htyp
  | [ Hsub : _ |- _ ] =>
      apply (H n1 n2) in Hsub; try lia; rewrite Hsub; clear Hsub
  end.

Lemma get_typ_fuel_widen :
  forall t n1 n2 E T,
    n1 <= n2 ->
    get_typ E t n1 = Result (Some T) ->
    get_typ E t n2 = Result (Some T).
Proof.
  induction t; intros * Hle. 
  - exact.
  - cbn. solveR get_typ. invR.
    apply (IHt _ n2) in Hslv. 2: lia.
    rewrite Hslv. exact.
  - cbn.
    solveRe get_typ IHt1 n1 n2.
    solveRe promote_tvar promote_tvar_fuel_widen n1 n2.
    destruct T1; try congruence.
    solveRe get_typ IHt2 n1 n2.
    solveRe sub_check sub_check_fuel_widen n1 n2.
    exact.
  - destruct n1, n2. 1:exact. 2:lia.
    + cbn. solveRe get_typ IHt 0 (S n2). exact.
    + cbn. solveRe get_typ IHt (S n1) (S n2). exact.
  - destruct n1, n2. 1:exact. 2:lia.
    + unfold get_typ. fold get_typ.
      solveRe get_typ IHt 0 (S n2).
      solveRe promote_tvar promote_tvar_fuel_widen 0 (S n2).
      case T1; exact.
    + unfold get_typ. fold get_typ.
      solveRe get_typ IHt (S n1) (S n2).
      solveRe promote_tvar promote_tvar_fuel_widen (S n1) (S n2).
      case T1; try exact. intros *.
      solveRe sub_check sub_check_fuel_widen (S n1) (S n2).
      exact.
Qed.

Ltac solve_left n T :=
  exists n, T; split; [(try exact; try apply sub_reflexivity); intuition | idtac].

Ltac appWS H :=
      let Hsub' := fresh "Hsub" in
      let HwfE := fresh "HwfE" in
      let HwfT := fresh "HwfT" in
      let HwfU := fresh "HwfU'" in
      pose proof H as Hsub';
      apply sub_wf in Hsub' as [HwfE [HwfT HwfU]]
. 

Ltac appWT H :=
  let Htyp' := fresh "Htyp" in
  let HwfE := fresh "HwfE" in
  let Hwft := fresh "Hwft" in
  let HwfU := fresh "HwfU'" in
  pose proof H as Htyp';
  apply typing_wf in Htyp' as [HwfE [Hwft HwfU]]
.

Ltac step H :=
  unfold H; fold H.

Lemma sub_arrow_implies_promote_tvar_arrow :
  forall e T1 T21 T22,
    sub e T1 (arrow T21 T22) -> exists fl T31 T32,
      promote_tvar e T1 fl = Result (Some (arrow T31 T32)) /\
        sub e T21 T31 /\ sub e T32 T22.
Proof with (solveWfI; cbn).
  intros * Hsub. appWS Hsub. 
  remember (arrow T21 T22) as Tarrow.
  dependent induction Hsub; inversion HeqTarrow; clear HeqTarrow; subst.
  - appWS Hsub. 
    destruct IHHsub as [fl [T41 [T42 [Hprom [Hsub1 Hsub2]]]]]; try exact.
    exists (S fl), T41, T42. split. 2: exact.
    step promote_tvar... rewrite H. exact.
  - exists 0, S1, S2. step promote_tvar... 
Qed.

Lemma sub_all_implies_promote_tvar_all :
  forall e T1 T21 T22,
    sub e T1 (all T21 T22) -> exists fl T31 T32,
      promote_tvar e T1 fl = Result (Some (all T31 T32)) /\
        sub e T21 T31 /\ sub (ebound e T21) T32 T22.
Proof with (solveWfI; cbn).
  intros * Hsub. appWS Hsub. 
  remember (all T21 T22) as Tarrow.
  dependent induction Hsub; inversion HeqTarrow; clear HeqTarrow; subst.
  - appWS Hsub. 
    destruct IHHsub as [fl [T41 [T42 [Hprom [Hsub1 Hsub2]]]]]; try exact.
    exists (S fl), T41, T42. split. 2: exact.
    step promote_tvar... rewrite H. exact.
  - exists 0, S1, S2. step promote_tvar... 
Qed.

Theorem typing_implies_get_typ :
  forall t e T,
    typing e t T ->
    exists n T', sub e T' T /\ get_typ e t n = Result (Some T').
Proof.
  intros * H. appWT H. induction H.
  - (* T_Var *)
    solve_left 1 T. cbn. solveWfI. f_equal. exact.
  - (* T_Abs *)
    appWT H. destruct IHtyping as [n [T [Hsub Htyp]]]; intuition.
    exists n, (arrow T1 T). cbn in HwfU'.
    split. 2: cbn; rewrite Htyp; reflexivity.
    constructor.
    + apply sub_reflexivity. exact. intuition.
    + replace (sub e T T2) with (sub (remove_var (evar e T1) 0) T T2)
        by reflexivity.
      apply sub_strengthening_var. exact.
  - (* T_App *)
    appWT H. appWT H0.
    (** construct all fuels  *)
    destruct IHtyping1 as [n1 [T1 [Hsub1 Htyp1]]]; try solve [intuition].
    destruct IHtyping2 as [n2 [T2 [Hsub2 Htyp2]]]; try solve [intuition].
    destruct (sub_arrow_implies_promote_tvar_arrow e T1 T11 T12) as
      [n11 [T11' [T12' [Hprom1 [Hpsub1 Hpsub2]]]]]. { exact. }
    destruct (sub_implies_sub_check e T2 T11') as [n3 Hsub3].
    { apply sub_transitivity with T11; exact. }
    (** clear up environment *)
    clear HwfE1 HwfE0.
    pose (n1 + n2 + n11 + n3) as n. solve_left (S n) T12'.
    (** rewrite *)
    step get_typ. 
    apply (get_typ_fuel_widen _ _ (S n)) in Htyp1. 2:lia. rewrite Htyp1.
    apply (promote_tvar_fuel_widen n11 (S n)) in Hprom1. 2:lia. rewrite Hprom1.
    apply (get_typ_fuel_widen _ _ (S n)) in Htyp2. 2:lia. rewrite Htyp2.
    apply (sub_check_fuel_widen _ (S n)) in Hsub3. 2:lia. rewrite Hsub3.
    reflexivity.
  - (* T_Tabs *)
    appWT H.
    destruct IHtyping as [n [T2' [Hsub Htyp]]]; intuition.
    cbn in HwfU'.
    exists n, (all T1 T2').
    split. { constructor. 2:exact. apply sub_reflexivity; intuition. }
    cbn. rewrite Htyp. reflexivity. 
  - (* T_Tapp *)
    appWT H.
    (** construct all fuels  *)
    destruct IHtyping as [n1 [T1 [Hsub1 Htyp1]]]; intuition.
    destruct (sub_all_implies_promote_tvar_all e T1 T11 T12) as
      [n2 [T11' [T12' [Hprom1 [Hpsub1 Hpsub2]]]]]. { exact. }
    destruct (sub_implies_sub_check e T2 T11') as [n3 Hsub3].
    { apply sub_transitivity with T11; exact. }
    pose (n1 + n2 + n3) as n. exists (S n),  (tsubst T12' 0 T2).
    split. { apply tsubst_preserves_subtyping with (ebound e T11).
             constructor. exact. exact. }
    step get_typ.
    rewrite (get_typ_fuel_widen _ _ (S n) _ _ _ Htyp1). 2:lia.
    apply (promote_tvar_fuel_widen n2 (S n)) in Hprom1. 2:lia. rewrite Hprom1.
    apply (sub_check_fuel_widen _ (S n)) in Hsub3. 2:lia. rewrite Hsub3.
    reflexivity.
  - appWT H. 
    destruct IHtyping as [n1 [U [Hsub1 Htyp1]]]; intuition.
    exists n1, U. split. { apply sub_transitivity with T1; exact. } exact.
Qed.

Theorem typing_implies_type_check :
  forall t e T, typing e t T -> exists n, type_check e t T n = Result true.
Proof. 
  intros * H. 
  destruct (typing_implies_get_typ t e T) as [n1 [U [Hsub Htyp]]]; intuition.
  destruct (sub_implies_sub_check e U T) as [n2 Hsub2]. 1:exact.
  pose (n1 + n2) as n. exists (S n). unfold type_check.
  rewrite (get_typ_fuel_widen _ _ (S n) _ _ _ Htyp). 2:lia.
  rewrite (sub_check_fuel_widen _ (S n) _ _ _ _ Hsub2). 2:lia.
  reflexivity.
Qed.    

Theorem type_check_correct :
  forall t e T,
    typing e t T <-> exists n, type_check e t T n = Result true.
Proof.
  intros; split.
  - apply typing_implies_type_check.
  - intros [n H]. apply type_check_implies_typing with n. exact.
Qed.

(** * Q: What's the Tactics for fold -> unfold? *)
(** ** Value *)
Definition dc_value t : decidable (value t).
  refine
    (match t with 
     | abs _ _  => left I
     | tabs _ _ => left I
     | _        => right id
     end).
Defined.

Theorem reflect_value : forall t, reflect (value t) (dc_value t).
  intros; destruct t; cbn; try solve[right; elim]; try solve[left; apply I].
Qed.

Ltac solveVE :=
  intuition;
  match goal with
  | [ |- (value ?v)] =>
      apply (elimT (reflect_value v)); auto
  end.

Ltac solveVI :=
  match goal with
  | [ |- context [value ?v]] => 
      rewrite (introT (reflect_value v)); auto
  end.

Ltac solveVR :=
  match goal with
  | [ |- context [dc_value ?v]] => 
      destruct (reflect_value v); auto
  end.

(** ** Shorthands : unwrap unnecessary fuels *)
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
