From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
From Coq Require Import Lia.
Require Import Frontier. Import Frontier.
Require Import Clause. Import Clause.
Require Import Atom. Import Atom.
Require Import Geq. Import Geq.
Require Import Vars. Import Vars.
Require Import Sets. Import Sets.
Require Import Main. Import Main.

Example Cs := [
  ["a" & 0] ~> "b" & 1;
  ["b" & 1] ~> "c" & 2
].
Example f := frontier_fin_0.
Example vars' := nodup string_dec (vars Cs).

Example thm_32_example :=
  thm_32
    (Datatypes.length vars')
    (Datatypes.length vars')
    Cs
    vars'
    []
    f.

Extraction Language Haskell.

Extract Constant map => "Prelude.map".
Extract Constant fold_right => "Prelude.foldr".

Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extraction "/home/andreas/Projects/thesis/coq/extr/latex_ex.hs"
  thm_32_example.
