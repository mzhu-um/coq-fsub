From FSUB Require Import QCLibs.
From FSUB Require Import FSub.
From FSUB Require Import Decidable.

(** * ReductionP: Parallel Reduction *)

Fixpoint pstep (t : term) : term :=
  match t with
  | var _ => t 
  | abs T t =>  abs T (pstep t)
  | app t1 t2 =>
      match t1 with
      | abs _ t1 => subst t2 0 t1
      | _ => app (pstep t1) (pstep t2)
      end
  | tabs T t => tabs T (pstep t)
  | tapp t T =>
      match t with
      | tabs _ t => subst_typ t 0 T
      | _ => tapp t T
      end
  end.

