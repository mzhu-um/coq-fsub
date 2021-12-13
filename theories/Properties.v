From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.
From FSUB Require Import Generator.
From FSUB Require Import Reduction.


Definition sub_check_100 (e : env) (T1 T2 : typ) : bool :=
  match sub_check e T1 T2 100 with
  | Result true => true
  | _ => false
  end.

Definition prop_gen_wt :=
  let fuel_type := 4 in
  let fuel_expr := 4 in
  forAll (gen_typ fuel_type) (fun T =>
  forAllMaybe (gen_expr fuel_expr [] T) (fun t => 
  whenFail ("Type was " ++ show T ++ nl ++ 
            "Term was " ++ show t ++ nl ++
            "With Type" ++ show (typeOf [] t) ++))
           (typeOf [] t = Some T ?)).

(** ** [C1] generated concrete [typ]s are well-formed *)
Definition prop_gen_concrete_typ_wf :=
  forAllMaybe (gen_concrete_typ 5 empty) (fun T =>
  whenFail ("Type is: " ++ show T ++ nl)
           (dc_wf_typ empty T)).

QuickChick prop_gen_concrete_typ_wf.

Locate "elems".

Check (Some var).

