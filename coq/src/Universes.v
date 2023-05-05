From Coq Require Import Extraction.
From Coq Require Import Lists.List. Import ListNotations.

Definition prop_ex {A : Type} (l : list A) : Prop :=
  exists x, In x l.

Definition set_ex {A : Set} (l : list A) : Set :=
  sig (fun x : A => In x l).

Definition type_ex {A : Type} (l : list A) : Type :=
  sig (fun x : A => In x l).

Extraction Language Haskell.

Extraction "/home/andreas/univ.hs"
  prop_ex
  set_ex
  type_ex.
