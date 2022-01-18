From FSUB Require Import
     QCLibs
     FSub
     Decidable
     MutantInterface.

(** * MutantExample: Debug Mutants *)
(** ** TSubstAllNoTShift *)
Module TSubstAllNoTShift. 
  Example tm1 :=
    tabs top
         (tabs top
               (tapp (tabs top
                           (tabs top
                                 (abs (all (tvar 0)
                                           (arrow (arrow (tvar 0) (tvar 1))
                                                  (arrow (tvar 2) (tvar 3))))
                                      (var 0))))
                     (arrow (tvar 0) (tvar 1)))).
  Eval cbv in get_typ' empty tm1.

  (* Already in value form *)
  Eval cbn in step'' (TSubstAllNoTShift) tm1.

  (* But not in normal form *)
  Example otm2 :=
    pstep' (NoMutant) tm1.

  Example otm2' :=
    pstep' (TSubstAllNoTShift) tm1.

  Example TSubstAllNoTShift_tm_diff :
    otm2 <> otm2'.
  Proof. cbn. easy. Qed.


  Example TSubstAllNoTShift_diff' :
    (tm2 <- otm2;; get_typ' empty tm2) <> (tm2' <- otm2';; get_typ' empty tm2').
  Proof. cbn. easy. Qed.
End TSubstAllNoTShift.
