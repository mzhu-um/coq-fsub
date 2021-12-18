From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.
From FSUB Require Import Generator.
From FSUB Require Import Reduction.


Definition type_check' :=
  fun E t T => type_check E t T 100. 
Definition get_typ' :=
  fun E t => get_typ E t 100. 

(** ** [C1] generated exact [typ]s are well-formed *)
Definition prop_gen_exact_typ_wf :=
  forAllMaybe (gen_exact_typ 5 empty) (fun T =>
  whenFail ("Type is: " ++ show T ++ nl)
           (dc_wf_typ empty T)).

QuickChick prop_gen_exact_typ_wf.


(** ** [C2-0] generated exact [term]s (base case) are well-typed *)
Definition prop_gen_exact0_wt :=
  let fuel_type := 4 in
  let fuel_expr := 4 in
  forAllMaybe (gen_exact_typ fuel_type empty) (fun T =>
  forAllMaybe (gen_exact_term0 empty T) (fun t => 
  whenFail ("Gened Type is" ++ show T ++ nl ++ 
            "Gened Term is" ++ show t ++ nl ++
            "Checked Type is" ++ show_result' (get_typ' empty t)
           )
           ((type_check' empty t T) = (Result true) ?))).

QuickChick prop_gen_exact0_wt.

(** ** [C2] generated exact [term]s are well-typed *)
Definition prop_gen_exact_wt :=
  let fuel_type := 6 in
  let fuel_expr := 6 in
  forAllMaybe (gen_exact_typ fuel_type empty) (fun T =>
  forAllMaybe (gen_exact_term fuel_expr empty T) (fun t => 
  whenFail ("Gened Type is" ++ show T ++ nl ++ 
            "Gened Term is" ++ show t ++ nl ++
            "Type of Term is" ++ show_result' (get_typ' empty t)
           )
           ((type_check' empty t T) = (Result true) ?))).


QuickChick prop_gen_exact_wt.



(** ** [C3] generated subtype [term]s are well-formed *)
Definition prop_gen_sub_typ_wf :=
  let fuel_type := 6 in
  forAllMaybe (gen_exact_typ fuel_type empty) (fun T =>
  forAll (gen_sub_typ fuel_type empty T) (fun S =>
  whenFail ("Gened Type is" ++ show T ++ nl ++ 
            "Gened SubT is" ++ show S ++ nl)
           (dc_wf_typ empty T))).

QuickChick prop_gen_sub_typ_wf.


(** ** [C4] generated sub [typ]s are subtypes *)
Definition prop_gen_sub_typ_sub :=
  let fuel_type := 5 in
  forAllMaybe (gen_exact_typ fuel_type empty) (fun T =>
  forAll (gen_sub_typ fuel_type empty T) (fun S =>
  whenFail ("Gened Type is" ++ show T ++ nl ++ 
            "Gened SubT is" ++ show S ++ nl)
           ((sub_check' empty S T) = (Result true) ?))).

QuickChick prop_gen_sub_typ_sub.

(** ** [C5] generated super [typ]s are super types *)
Definition prop_gen_sup_typ_sup :=
  let fuel_type := 5 in
  forAllMaybe (gen_exact_typ fuel_type empty) (fun T =>
  forAll (gen_sup_typ fuel_type empty T) (fun S =>
  whenFail ("Gened Type is" ++ show T ++ nl ++ 
            "Gened SupT is" ++ show S ++ nl)
           ((sub_check' empty T S) = (Result true) ?))).

QuickChick prop_gen_sup_typ_sup.

(** ** [C6] Subtype Transitivity  *)
Definition prop_gen_sub_trans :=
  let fuel_type := 6 in
  forAllMaybe (gen_exact_typ fuel_type empty) (fun T =>
  forAll (gen_sub_typ fuel_type empty T) (fun S =>
  forAll (gen_sub_typ fuel_type empty S) (fun R =>
  whenFail ("Gened Typ [T] is " ++ show T ++ nl ++ 
            "Gened Sub [S] is " ++ show S ++ nl ++ 
            "Gened Sub [R] is " ++ show R ++ nl)
           ((((sub_check' empty R S) = (Result true) ?)
             && ((sub_check' empty S T) = (Result true) ?))%bool)))).

QuickChick prop_gen_sub_trans.

