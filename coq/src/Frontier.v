From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Lists.ListSet.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Misc. Import Misc.
Require Import Sets. Import Sets.
Require Import Ninfty. Import Ninfty.

Module Frontier.

  Definition Frontier := string -> Ninfty.

  Example frontier_fin_0 : Frontier := fun _ => fin 0.
  Example frontier_fin_1 : Frontier := fun _ => fin 1.
  Example frontier_fin_2 : Frontier := fun _ => fin 2.
  Example frontier_infty : Frontier := fun _ => infty.

  Lemma frontier_lambda (f : Frontier) :
    (fun v : string => f v) = f.
  Proof. apply functional_extensionality. intros. reflexivity. Qed.

  Definition update_infty_V (V : set string) (f : Frontier) : Frontier :=
    fun x : string => if set_mem string_dec x V then infty else f x.

End Frontier.
