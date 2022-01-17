From FSUB Require Import
     QCLibs
     FSub
     Decidable
     MutantInterface
     GeneratorSub
.

(** * MutantSub : Testing Properties with (New) GeneratorSub *)
(** ** Properties *)
(** ** [C7'] Weak Progress NF
    Only support parallel reduction!
 *)
Definition prop_gen_progress_nf_f  (fuel_type : nat) (m : Mutant) :=
  let step' := pstep' in
  forAllMaybe (gen_opt_typ fuel_type empty true) (fun T =>
  forAllMaybe (gen_sub_term fuel_type empty T) (fun t =>
  forAll (gen_sup_typ fuel_type empty T) (fun T =>
  whenFail ("Generated" ++ nl ++
            "[T]: " ++ show T ++ nl ++ 
            "[t]: " ++ show t ++ nl ++
            "FailWith" ++ nl ++
            "[T]: " ++ show (get_typ' empty t) ++ nl ++
            match (multistep' m 40 step' t is_nf) with
            | Result (true, t) => 
                "[T']: " ++ show (get_typ' empty t) ++ nl ++
                "[t]: " ++ show t ++ nl
            | rst => show_result' rst
            end)
           ((type_check' empty t T) &&
              (match multistep' m 40 step' t is_nf with
               | Result (true, t) => (type_check' empty t T)
               | _ => false
               end))%bool))).


Definition prop_gen_progress_nf := prop_gen_progress_nf_f 5.
(* QuickChick (prop_gen_progress_nf NoMutant). (* Correct ! *) *)

(** Okay for WHNF *)
(* QuickChick (prop_gen_progress_nf TShiftTVarAll).       (* 4 *) *)
(* QuickChick (prop_gen_progress_nf TSubstTVarFlip).      (* 4 *) *)
(* QuickChick (prop_gen_progress_nf TSubstTVarOverShift). (* 4 *) *)
(* QuickChick (prop_gen_progress_nf SubstVarFlip).        (* 4 *) *)
(* QuickChick (prop_gen_progress_nf SubstAbsNoIncr).      (* 4 *) *)
(* QuickChick (prop_gen_progress_nf ShiftVarAll).         (* 4 *) *)
(* QuickChick (prop_gen_progress_nf ShiftAbsNoIncr).      (* 4 *) *)
(* QuickChick (prop_gen_progress_nf ShiftTypTAbsNoIncr).  (* 4 *) *)

(** Okay for NF *)
(* QuickChick (prop_gen_progress_nf TShiftTVarNoIncr).  (* 4 *) *)
(* QuickChick (prop_gen_progress_nf TSubstTVarNoShift). (* 4 *) *)
(* QuickChick (prop_gen_progress_nf SubstVarNoDecr).    (* 4 *) *)

(* Definition prop_gen_progress_nf' := prop_gen_progress_nf_f 6. *)
(** Need Luck for NF *)
(* QuickChick (prop_gen_progress_nf SubstAbsNoShift).   (* 4 *) *)
(* QuickChick (prop_gen_progress_nf TShiftAllNoIncr).   (* 4 *) *)
(* QuickChick (prop_gen_progress_nf ShiftVarNoIncr).    (* 4 *) *)
(* QuickChick (prop_gen_progress_nf SubstTAbsNoShift).  (* 4 *) *)
(* QuickChick (prop_gen_progress_nf TSubstAllNoTShift). (* Nope *) *)


(** ** [C7] Weak Progress *)
Definition prop_gen_progress (m : Mutant) :=
  let fuel_type := 5 in
  let step' := step'' in
  forAllMaybe (gen_opt_typ fuel_type empty true) (fun T =>
  forAllMaybe (gen_sub_term fuel_type empty T) (fun t =>
  forAll (gen_sup_typ fuel_type empty T) (fun T =>
  whenFail ("Generated" ++ nl ++
            "[T]: " ++ show T ++ nl ++ 
            "[t]: " ++ show t ++ nl ++
            "FailWith" ++ nl ++
            "[T]: " ++ show (get_typ' empty t) ++ nl ++
            match (multistep' m 40 step' t dc_value) with
            | Result (true, t) => 
                "[T']: " ++ show (get_typ' empty t) ++ nl ++
                "[t]: " ++ show t ++ nl
            | rst => show_result' rst
            end)
           ((type_check' empty t T) &&
              (match multistep' m 40 step' t dc_value with
               | Result (true, t) => (type_check' empty t T)
               | _ => false
               end))%bool))).

(* QuickChick (prop_gen_progress NoMutant). (* Correct ! *) *)

(** Should be detectable *)
(* QuickChick (prop_gen_progress TShiftTVarAll).       (* 5 *) *)
(* QuickChick (prop_gen_progress TSubstTVarFlip).      (* 5 *) *)
(* QuickChick (prop_gen_progress TSubstTVarOverShift). (* 5 *) *)
(* QuickChick (prop_gen_progress SubstVarFlip).        (* 5 *) *)
(* QuickChick (prop_gen_progress SubstAbsNoIncr).      (* 5 *) *)
(* QuickChick (prop_gen_progress ShiftVarAll).         (* 5 *) *)
(* QuickChick (prop_gen_progress ShiftAbsNoIncr).      (* 5 *) *)
(* QuickChick (prop_gen_progress ShiftTypTAbsNoIncr).  (* 5 *) *)
(* QuickChick (prop_gen_progress TShiftAllNoIncr).     (* 5 *) *)

(** Should only work under NF *)
(* QuickChick (prop_gen_progress TShiftTVarNoIncr).  (* Nope *) *)
(* QuickChick (prop_gen_progress SubstTAbsNoShift).  (* Nope *) *)
(* QuickChick (prop_gen_progress TSubstTVarNoShift). (* Nope *) *)
(* QuickChick (prop_gen_progress SubstVarNoDecr).    (* Nope *) *)
(* QuickChick (prop_gen_progress TSubstAllNoTShift). (* Nope *) *)
(* QuickChick (prop_gen_progress SubstAbsNoShift).   (* Nope *) *)
(* QuickChick (prop_gen_progress ShiftVarNoIncr).    (* Nope *) *)
