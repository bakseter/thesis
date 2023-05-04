From Coq Require Import Extraction.
From Coq Require Import Lists.List. Import ListNotations.

Definition prop_ex {A : Type} (l : list A) : Prop :=
  exists x, In x l.

Check sig.
Check prod.
Check sigT.

Check fun (A : Type) (l : list A) => sig (fun x : A => In x l).

Definition set_ex {A : Type} (l : list A) : Type :=
  sig (fun x : A => In x l).

Definition type_ex : Type := forall (A : Type) (x : A), x = x.

Extraction Language Haskell.

Extraction "/home/andreas/bruh.hs"
  prop_ex
  set_ex
  type_ex.
