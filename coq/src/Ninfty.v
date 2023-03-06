From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.

Module Ninfty.

  Inductive Ninfty : Type :=
    | infty : Ninfty
    | fin   : nat -> Ninfty.

  Definition ninfty_geq (x y : Ninfty) : bool :=
    match x with
    | infty => true
    | fin n =>
        match y with
        | infty => false
        | fin n' => n' <=? n
        end
    end.

  Example ninfty_geq_test1 :
    forall n, ninfty_geq infty (fin n) = true.
  Proof. reflexivity. Qed.

  Example ninfty_geq_test2 :
    forall n, ninfty_geq (fin n) infty = false.
  Proof. reflexivity. Qed.

  Example ninfty_geq_test3 :
    forall n, ninfty_geq (fin n) (fin n) = true.
  Proof. simpl. intros. apply leb_refl. Qed.

  Example ninfty_geq_test4 :
    forall n n', ninfty_geq (fin n) (fin n') = (n' <=? n).
  Proof. simpl. intros. reflexivity. Qed.

  Example ninfty_geq_test5 :
    ninfty_geq infty infty = true.
  Proof. reflexivity. Qed.

  Definition Sinfty (x : Ninfty) : Ninfty :=
    match x with
    | infty => infty
    | fin n => fin (S n)
    end.

  Definition is_infty (ninf : Ninfty) : bool :=
    match ninf with
    | infty => true
    | _     => false
    end.

End Ninfty.
