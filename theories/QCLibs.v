From Coq Require Export
     Arith Lia List String Program.Wf Program.Equality.
From Coq Require Export
     Recdef ssreflect ssrfun ssrbool.
From QuickChick Require Export QuickChick.
From ExtLib Require Export Monad OptionMonad ListMonad.
Export QcNotation MonadNotation ListNotations.

(* Set Implicit Arguments. *)
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

Ltac inv0 :=
  let H := fresh "H" in
  intros H; inversion H; clear H; subst.

Ltac inv H :=
  inversion H; clear H; subst.
