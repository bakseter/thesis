From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lists.ListSet.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
Require Import Frontier. Import Frontier.
Require Import Ninfty. Import Ninfty.

Module Atom.

  Inductive Atom : Type :=
    | atom : string -> nat -> Atom.

  Notation "x & k" := (atom x k) (at level 80).

  Definition x_str := "x"%string.
  Definition y_str := "y"%string.
  Definition z_str := "z"%string.
  Definition u_str := "u"%string.

  Example atom_x0 : Atom := "x" & 0.
  Example atom_x1 : Atom := "x" & 1.
  Example atom_x2 : Atom := "x" & 2.
  Example atom_y0 : Atom := "y" & 0.
  Example atom_y1 : Atom := "y" & 1.
  Example atom_y2 : Atom := "y" & 2.
  Example atom_z0 : Atom := "z" & 0.
  Example atom_z1 : Atom := "z" & 1.
  Example atom_z2 : Atom := "z" & 2.
  Example atom_u0 : Atom := "u" & 0.
  Example atom_u1 : Atom := "u" & 1.
  Example atom_u2 : Atom := "u" & 2.

  Definition atom_true (a : Atom) (f : Frontier) : bool :=
    match a with
    | (x & k) =>
      match f x with
      | infty => true
      | fin n => k <=? n
      end
    end.

  Definition shift_atom (n : nat) (a : Atom)  : Atom :=
    match a with
    | (x & k) => (x & (n+k))
    end.

  Lemma shift_atom_0 (a : Atom) :
    shift_atom 0 a = a.
  Proof. induction a. reflexivity. Qed.

  Lemma shift_atom_twice (a : Atom) (n m : nat) :
    shift_atom (n + m) a = shift_atom n (shift_atom m a).
  Proof.
    destruct a as [x k]. simpl.
    rewrite add_assoc. reflexivity.
  Qed.

  Lemma map_shift_atom_0 (s : set Atom) :
    map (shift_atom 0) s = s.
  Proof.
    induction s as [| h t IHl]; try reflexivity.
    simpl. rewrite IHl. rewrite shift_atom_0. reflexivity.
  Qed.

  Lemma map_shift_atom_twice (s : set Atom) (n m : nat) :
    map (shift_atom (n + m)) s =
    map (shift_atom n) (map (shift_atom m) s).
  Proof.
    induction s; try reflexivity.
    simpl. rewrite shift_atom_twice, IHs. reflexivity.
  Qed.

  Lemma atom_false_shift_atom_false (a : Atom) (f : Frontier) (n : nat) :
    atom_true a f = false -> atom_true (shift_atom n a) f = false.
  Proof.
    intros. induction n.
    - rewrite shift_atom_0. assumption.
    - destruct a as [x k].
      induction k; simpl; simpl in H, IHn;
      destruct (f x); try assumption;
      destruct n0; try reflexivity;
      apply leb_nle; apply leb_nle in IHn; lia.
  Qed.

End Atom.
