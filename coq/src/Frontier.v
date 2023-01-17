From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Misc. Import Misc.
Require Import Ninfty. Import Ninfty.

Module Frontier.

  Definition Frontier := total_map Ninfty.

  Example frontier_fin_0 : Frontier := fun _ => fin 0.
  Example frontier_fin_1 : Frontier := fun _ => fin 1.
  Example frontier_fin_2 : Frontier := fun _ => fin 2.
  Example frontier_infty : Frontier := fun _ => infty.

  Lemma frontier_lambda (f : Frontier) :
    (fun v : string => f v) = f.
  Proof. apply functional_extensionality. intros. reflexivity. Qed.

End Frontier.
