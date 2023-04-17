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

Module Alf.

  (*
     ---- Fails for Cs with this def.: ----

    Example Cs := [
      ["a" & 0] ~> "b" & 1;
      ["b" & 1] ~> "c" & 2;
      ["c" & 2] ~> "d" & 3
    ].

   --- Works for Cs with (at most) this def.:
    Example Cs := [
      ["a" & 0] ~> "b" & 1;
      ["b" & 1] ~> "c" & 2
    ].
  *)

  Example Cs := [
    ["a" & 0] ~> "c" & 2;
    ["c" & 2] ~> "d" & 3
  (*
    ["d" & 3] ~> "e" & 4;
    ["e" & 4] ~> "f" & 5;
    ["f" & 5] ~> "g" & 6;
    ["g" & 6] ~> "h" & 7;
    ["h" & 7] ~> "i" & 8;
    ["i" & 8] ~> "j" & 9;
    ["j" & 9] ~> "k" & 10;
    ["k" & 10] ~> "l" & 11;
    ["l" & 11] ~> "m" & 12;
    ["m" & 12] ~> "n" & 13;
    ["n" & 13] ~> "o" & 14;
    ["o" & 14] ~> "p" & 15;
    ["p" & 15] ~> "q" & 16;
    ["q" & 16] ~> "r" & 17;
    ["r" & 17] ~> "s" & 18;
    ["s" & 18] ~> "t" & 19;
    ["t" & 19] ~> "u" & 20;
    ["u" & 20] ~> "v" & 21;
    ["v" & 21] ~> "w" & 22;
    ["w" & 22] ~> "x" & 23;
    ["x" & 23] ~> "y" & 24;
    ["y" & 24] ~> "z" & 25
   *)
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_alf :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_alf :=
    ex_lfp_geq_empty Cs f.

  Lemma a1 : incl [] vars'.
  Proof. apply incl_nil_l. Qed.

  Lemma a2 : Datatypes.length (nodup string_dec vars') <= Datatypes.length vars'.
  Proof. apply nodup_length. Qed.

  Lemma a3 : Datatypes.length
    (set_diff string_dec (nodup string_dec vars')
       (nodup string_dec [])) <= Datatypes.length vars' <=
      Datatypes.length vars'.
  Proof. unfold vars'. simpl. lia. Qed.

  Compute ex_alf a1 a2 a3 ex_lfp_geq_empty_alf.

End Alf.

Module Alf2.

  Example Cs := [
    ["a" & 0] ~> "b" & 1;
    ["b" & 0] ~> "c" & 1;
    ["c" & 0] ~> "d" & 1;
    ["d" & 0] ~> "e" & 1;
    ["e" & 0] ~> "f" & 1;
    ["f" & 0] ~> "g" & 1;
    ["g" & 0] ~> "h" & 1;
    ["h" & 0] ~> "i" & 1;
    ["i" & 0] ~> "j" & 1;
    ["j" & 0] ~> "k" & 1;
    ["k" & 0] ~> "l" & 1;
    ["l" & 0] ~> "m" & 1;
    ["m" & 0] ~> "n" & 1;
    ["n" & 0] ~> "o" & 1;
    ["o" & 0] ~> "p" & 1;
    ["p" & 0] ~> "q" & 1;
    ["q" & 0] ~> "r" & 1;
    ["r" & 0] ~> "s" & 1;
    ["s" & 0] ~> "t" & 1;
    ["t" & 0] ~> "u" & 1;
    ["u" & 0] ~> "v" & 1;
    ["v" & 0] ~> "w" & 1;
    ["w" & 0] ~> "x" & 1;
    ["x" & 0] ~> "y" & 1;
    ["y" & 0] ~> "z" & 1
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_alf2 :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_alf2 :=
    ex_lfp_geq_empty Cs f.

End Alf2.

Module Fla.

  Example Cs := [
    ["y" & 0] ~> "z" & 1;
    ["x" & 0] ~> "y" & 1;
    ["w" & 0] ~> "x" & 1;
    ["v" & 0] ~> "w" & 1;
    ["u" & 0] ~> "v" & 1;
    ["t" & 0] ~> "u" & 1;
    ["s" & 0] ~> "t" & 1;
    ["r" & 0] ~> "s" & 1;
    ["q" & 0] ~> "r" & 1;
    ["p" & 0] ~> "q" & 1;
    ["o" & 0] ~> "p" & 1;
    ["n" & 0] ~> "o" & 1;
    ["m" & 0] ~> "n" & 1;
    ["l" & 0] ~> "m" & 1;
    ["k" & 0] ~> "l" & 1;
    ["j" & 0] ~> "k" & 1;
    ["i" & 0] ~> "j" & 1;
    ["h" & 0] ~> "i" & 1;
    ["g" & 0] ~> "h" & 1;
    ["f" & 0] ~> "g" & 1;
    ["e" & 0] ~> "f" & 1;
    ["d" & 0] ~> "e" & 1;
    ["c" & 0] ~> "d" & 1;
    ["b" & 0] ~> "c" & 1;
    ["a" & 0] ~> "b" & 1
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_fla :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_fla :=
    ex_lfp_geq_empty Cs f.

End Fla.

Module Note.

  Example Cs := [
    ["a" & 0; "b" & 0] ~> "b" & 1;
    ["b" & 0] ~> "c" & 3;
    ["c" & 1] ~> "d" & 0;
    ["b" & 0; "d" & 2] ~> "e" & 0;
    ["e" & 0] ~> "a" & 0
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_note :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_note :=
    ex_lfp_geq_empty Cs f.

End Note.

Module Xy.

  Example Cs := [
    ["x" & 0; "y" & 1] ~> "x" & 1;
    ["x" & 1; "y" & 0] ~> "y" & 1
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_xy :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_xy :=
    ex_lfp_geq_empty Cs f.

End Xy.

Module Xyz0.

  Example Cs := [
    ["x" & 1] ~> "y" & 0;
    ["y" & 0] ~> "z" & 1;
    ["z" & 0] ~> "x" & 1
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_xyz0 :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_xyz0 :=
    ex_lfp_geq_empty Cs f.

End Xyz0.

Module Fail0.
  Example Cs := [
    ["a" & 0] ~> "b" & 2;
    ["b" & 2] ~> "c" & 1
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_fail0 :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_fail0 :=
    ex_lfp_geq_empty Cs f.
End Fail0.

Module Fail1.
  Example Cs := [
    ["a" & 0] ~> "b" & 3;
    ["b" & 2] ~> "c" & 3
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_fail1 :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_fail1 :=
    ex_lfp_geq_empty Cs f.
End Fail1.

Module Fail2.
  Example Cs := [
    ["a" & 0] ~> "b" & 3;
    ["b" & 4] ~> "c" & 1
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_fail2 :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_fail2 :=
    ex_lfp_geq_empty Cs f.
End Fail2.

Module Fail3.
  Example Cs := [
    ["a" & 0] ~> "b" & 2;
    ["b" & 2] ~> "a" & 1
  ].
  Example f := frontier_fin_0.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_fail3 :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_fail3 :=
    ex_lfp_geq_empty Cs f.
End Fail3.

Module Fail4.
  Example Cs := [
    ["a" & 0] ~> "b" & 0;
    ["b" & 3] ~> "c" & 3
  ].
  Example f := frontier_infty.
  Example vars' := nodup string_dec (vars Cs).
  Example ex_fail4 :=
    thm_32
      (Datatypes.length vars')
      (Datatypes.length vars')
      Cs
      vars'
      []
      f.
  Example ex_lfp_geq_empty_fail4 :=
    ex_lfp_geq_empty Cs f.
End Fail4.

Extraction Language Haskell.

Extract Constant map => "Prelude.map".
Extract Constant fold_right => "Prelude.foldr".

Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extraction "/home/andreas/Projects/thesis/coq/extr/ex.hs"
  Fail0.ex_fail0 Fail0.ex_lfp_geq_empty_fail0
  Fail1.ex_fail1 Fail1.ex_lfp_geq_empty_fail1
  Fail2.ex_fail2 Fail2.ex_lfp_geq_empty_fail2
  Fail3.ex_fail3 Fail3.ex_lfp_geq_empty_fail3
  Fail4.ex_fail4 Fail4.ex_lfp_geq_empty_fail4.
