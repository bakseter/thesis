Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.Minus.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
From Coq Require Import Setoids.Setoid.
From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellNatNum.
From Coq Require Import ExtrHaskellString.
Require Import Sets. Import Sets. Import StringSetsNotation.
Require Import Clause. Import Clause.
Require Import Atom. Import Atom.
Require Import Frontier. Import Frontier.
Require Import Vars. Import Vars.
Require Import VarsImp. Import VarsImp.
Require Import Misc. Import Misc.
Require Import Forward. Import Forward.
Require Import Geq. Import Geq.
Require Import Model. Import Model.
Require Import Ninfty. Import Ninfty.

Definition pred_P (Cs : set Clause) (n m : nat) : Type :=
  forall f : Frontier, forall V W : set string,
    incl W V ->
    Datatypes.length V <= n ->
    Datatypes.length (set_diff string_dec V W) <= m <= n ->
    ex_lfp_geq Cs W W f -> ex_lfp_geq Cs V V f.

Lemma pred_P_downward (Cs : set Clause) :
  forall n m n' m',
    pred_P Cs n m ->
    n' <= n ->
    m' <= m ->
    pred_P Cs n' m'.
Proof.
Admitted.

Definition lem_33 (Cs : set Clause) (V W : set string) (f : Frontier) :
  (* subject to change *)
  incl W V ->
  ex_lfp_geq Cs W W f ->
  ex_lfp_geq Cs V W f.
Proof.
Admitted.

Definition thm_32 (Cs : set Clause) :
  forall n m, pred_P Cs n m.
Proof.
  induction n as [|n IHn].
  - intros. unfold pred_P. intros. unfold ex_lfp_geq in *.
    exists f. split. apply geq_refl. apply le_0_r in H0.
    apply length_zero_iff_nil in H0. rewrite H0.
    apply sub_model_W_empty.
  - induction m as [|m IHm].
    + unfold pred_P in *. intros. apply (ex_lfp_geq_incl Cs V W);
      try assumption. destruct H1. apply le_0_r in H1.
      apply length_zero_iff_nil in H1.
      apply set_diff_nil_incl in H1. assumption.
    + unfold pred_P in *. intros.
      inversion H1. apply le_lt_eq_dec in H3. destruct H3.
      * apply (IHm f V W); try assumption. lia.
      * apply (ex_lfp_geq_nodup_iff) in H2.
        assert (Datatypes.length (nodup string_dec W) <= n).
        { 
           eapply (set_diff_succ string_dec) in H; try apply H3.
           apply succ_le_mono. eapply le_trans.
           apply H. assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
           - eapply NoDup_incl_length. apply NoDup_nodup.
             rewrite <- nodup_incl2. apply incl_refl.
           - eapply le_trans in H0. apply H0. assumption.
           - apply e.
         }
         assert (ex_lfp_geq Cs (nodup string_dec W) (nodup string_dec W) f).
         {
            apply (IHn n f (nodup string_dec W) []);
            try assumption; try apply incl_nil_l.
            - eapply (set_diff_succ string_dec) in H; try apply H3.
              rewrite set_diff_nil. apply conj; lia. apply e.
            - unfold ex_lfp_geq. exists f. split.
              apply geq_refl. apply sub_model_W_empty.
          }
          assert (H': incl W V) by assumption.
          apply (nodup_incl2 string_dec) in H.
          apply (lem_33 Cs V (nodup string_dec W) f) in H;
          try assumption. elim H. intros h [H8 H9].
          destruct (sub_forward Cs V V h) as [U h'] eqn:Hforward.
          assert (sub_forward Cs V V h = (U, h')) by assumption.
          assert (sub_forward Cs V V h = (U, h')) by assumption.
          apply (sub_forward_incl_set_diff Cs h h' V (nodup string_dec W) U) in H9; try apply Hforward.
          inversion Hforward. apply sub_forward_incl in Hforward.
          destruct U as [|u U'] eqn:Hu.
          -- apply sub_forward_empty in H7.
             destruct H7. unfold ex_lfp_geq. exists h. split;
             try assumption.
          -- destruct (incl_dec string_dec V (nodup string_dec (set_union string_dec W U))).
             ++ unfold ex_lfp_geq. exists (update_infty_V V f). split.
                ** apply geq_update_infty_V.
                ** apply sub_model_update_infty_V.
             ++ assert (incl (nodup string_dec (set_union string_dec W U)) V).
                {
                  apply nodup_incl2. eapply incl_set_union; subst; assumption.
                }
                assert (Datatypes.length (nodup string_dec (set_union string_dec W U)) < Datatypes.length (nodup string_dec V)).
                {
                  assert (Datatypes.length (nodup string_dec (set_union string_dec W U)) <= Datatypes.length (nodup string_dec V)).
                  {
                    eapply NoDup_incl_length. apply NoDup_nodup.
                    apply nodup_incl. assumption.
                  }
                  apply le_lt_eq_dec in H13. destruct H13; try assumption.
                  assert (strict_subset (nodup string_dec (set_union string_dec W U)) (nodup string_dec V)).
                  {
                    unfold strict_subset. split.
                    - apply nodup_incl. assumption.
                    - unfold not. intros. apply n0.
                      apply nodup_incl2 in H13. assumption.
                  }
                  apply (strict_subset_lt_length string_dec).
                  unfold strict_subset in H13.
                  destruct H13. unfold strict_subset. split.
                  - apply nodup_incl in H13.
                    apply nodup_incl2 in H13. assumption.
                  - unfold not. intros. apply n0.
                    apply nodup_incl. assumption.
                }
                assert (Datatypes.length (set_diff string_dec V (set_union string_dec (nodup string_dec W) U)) < Datatypes.length (set_diff string_dec V (nodup string_dec W)) <= S m).
                {
                  apply conj.
                  - rewrite Hu. apply set_diff_incl_lt_length;
                    try assumption. apply nodup_incl2. assumption.
                  - rewrite <- set_diff_nodup_length. rewrite e.
                    lia.
                }
                apply (ex_lfp_geq_monotone Cs V h' f).
                eapply (IHm h' V (set_union string_dec W U)).
                ** apply nodup_incl2 in H10. assumption.
                ** assumption.
                ** apply conj; try lia. inversion H14.
                   apply le_lt_eq_dec in H16. destruct H16.
                   --- apply Arith_prebase.lt_n_Sm_le_stt in l.
                       assert (Datatypes.length (set_diff string_dec V (set_union string_dec W U)) <= Datatypes.length (set_diff string_dec V (set_union string_dec (nodup string_dec W) U))).
                       rewrite asd. apply le_refl.
                       apply lt_le_incl in H15.
                       eapply le_trans. apply H16.
                       eapply le_trans. apply H15. assumption.
                   --- rewrite e0 in H15. 
                       assert (Datatypes.length (set_diff string_dec V (set_union string_dec W U)) <= Datatypes.length (set_diff string_dec V (set_union string_dec (nodup string_dec W) U))).
                       rewrite asd. apply le_refl. lia.
                ** apply (IHn n h' (set_union string_dec W U) []).
                   --- apply incl_nil_l.
                   --- assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
                       { 
                         apply NoDup_incl_length. apply NoDup_nodup.
                         apply nodup_incl2. apply incl_refl.
                       }
                       assert (Datatypes.length (set_union string_dec W U) <= Datatypes.length (nodup string_dec (set_union string_dec W U))).
                       rewrite asd4. apply le_refl.
                       apply lt_le_pred in H13. eapply le_trans.
                       apply H16. eapply le_trans. apply H13.
                       apply le_n_Sm_pred_n_m in H0.
                       assert (pred (Datatypes.length (nodup string_dec V)) <= pred (Datatypes.length V)).
                       {
                         apply Nat.pred_le_mono. assumption.
                       }
                       eapply le_trans. apply H17. assumption.
                   --- apply conj; try lia.
                       assert (Datatypes.length (set_diff string_dec (set_union string_dec W U) []) <= Datatypes.length (set_union string_dec W U)).
                       apply (set_diff_nil_length string_dec).
                       assert (Datatypes.length (set_union string_dec W U) <= Datatypes.length (nodup string_dec (set_union string_dec W U))).
                       rewrite asd4. apply le_refl.
                       eapply le_trans. apply H15. apply lt_le_pred in H13.
                       eapply le_trans. apply H16. eapply le_trans. apply H13.
                       assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
                       { 
                         apply NoDup_incl_length. apply NoDup_nodup.
                         apply nodup_incl2. apply incl_refl.
                       }
                       assert (pred (Datatypes.length (nodup string_dec V)) <= pred (Datatypes.length V)).
                       {
                         apply Nat.pred_le_mono. assumption.
                       }
                       apply le_n_Sm_pred_n_m in H0.
                       eapply le_trans. apply H18. assumption.
                   --- unfold ex_lfp_geq. exists h'.
                       split. apply geq_refl.
                       apply sub_model_W_empty.
                ** eapply geq_trans with h; try assumption.
                   rewrite <- H12. apply geq_Sinfty_f2.
Defined.

(* a -> a *)

Example Cs_ex_1 := [([atom_x0] ~> atom_x0)].
Example f_ex_1 := frontier_fin_0.
Example thm_32_example1 :=
    thm_32
      Cs_ex_1
      1
      1
      f_ex_1
      [x_str]
      [].
Example ex_lfp_geq_empty_1 :=
  ex_lfp_geq_empty Cs_ex_1 f_ex_1.

(* a -> a+1 *)

Example Cs_ex_2 := [([atom_x0] ~> atom_x1)].
Example f_ex_2 := frontier_fin_0.
Example thm_32_example2 :=
  thm_32
    Cs_ex_2
    1
    1
    f_ex_2
    [x_str]
    [].
Example ex_lfp_geq_empty_2 :=
  ex_lfp_geq_empty Cs_ex_2 f_ex_2.

(* a -> b+1 *)

Example Cs_ex_3 := [([atom_x0] ~> atom_y1)].
Example f_ex_3 := frontier_fin_0.
Example thm_32_example3 :=
  thm_32
    Cs_ex_3
    2
    2
    f_ex_3
    [x_str; y_str]
    [].
Example ex_lfp_geq_empty_3 :=
  ex_lfp_geq_empty Cs_ex_3 f_ex_3.

(* a -> b+1 og c -> a+1 *)

Example Cs_ex_4 := [([atom_x0] ~> atom_y1); ([atom_z0] ~> atom_x1)].
Example f_ex_4 := frontier_fin_0.
Example thm_32_example4 :=
  thm_32
    Cs_ex_4
    3
    3
    f_ex_4
    [x_str; y_str; z_str]
    [].
Example ex_lfp_geq_empty_4 :=
  ex_lfp_geq_empty Cs_ex_4 f_ex_4.

(* a,b -> a+1 og a,b -> b+1 *)

Example Cs_ex_5 := [([atom_x0; atom_y0] ~> atom_x1); ([atom_x0; atom_y0] ~> atom_y1)].
Example f_ex_5 := frontier_fin_0.
Example thm_32_example5 :=
  thm_32
    Cs_ex_5
    2
    2
    f_ex_5
    [x_str; y_str]
    [].
Example ex_lfp_geq_empty_5 :=
  ex_lfp_geq_empty Cs_ex_5 f_ex_5.

(* a -> b+1 og b,c -> c+1 *)

Example Cs_ex_6 := [([atom_x0] ~> atom_y1); ([atom_y0; atom_z0] ~> atom_z1)].
Example f_ex_6 := frontier_fin_0.
Example thm_32_example6 :=
  thm_32
    Cs_ex_6
    3
    3
    f_ex_6
    [x_str; y_str; z_str]
    [].
Example ex_lfp_geq_empty_6 :=
  ex_lfp_geq_empty Cs_ex_6 f_ex_6.

Example Cs_ex_7 := [([atom_x0] ~> atom_x1); ([atom_y0] ~> atom_z1); ([atom_z0] ~> atom_u1)].
Example f_ex_7 := frontier_fin_0.
Example thm_32_example7 :=
  thm_32
    Cs_ex_7
    4
    4
    f_ex_7
    [x_str; y_str; z_str; u_str]
    [].
Example ex_lfp_geq_empty_7 :=
  ex_lfp_geq_empty Cs_ex_7 f_ex_7.

Extraction Language Haskell.

Extract Constant map => "Prelude.map".
Extract Constant fold_right => "Prelude.foldr".

Extract Inductive nat => "Prelude.Integer" ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extraction "/home/andreas/Projects/thesis/coq/thm_32.hs"
  thm_32
  thm_32_example1
  thm_32_example2
  thm_32_example3
  thm_32_example4
  thm_32_example5
  thm_32_example6
  thm_32_example7
  x_str
  y_str
  z_str
  u_str
  atom_x0
  atom_x1
  atom_y0
  atom_y1
  atom_z0
  atom_z1
  atom_u0
  atom_u1
  ex_lfp_geq_empty_1
  ex_lfp_geq_empty_2
  ex_lfp_geq_empty_3
  ex_lfp_geq_empty_4
  ex_lfp_geq_empty_5
  ex_lfp_geq_empty_6
  ex_lfp_geq_empty_7.
