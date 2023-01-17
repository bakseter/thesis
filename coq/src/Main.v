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

Definition pred_P (Cs : set Clause) (n m : nat) : Prop :=
  forall f, forall V W, incl W V ->
  Datatypes.length V <= n ->
  Datatypes.length (set_diff string_dec V W) <= m <= n ->
  ex_lfp_geq Cs W W f -> ex_lfp_geq Cs V V f.

Lemma pred_P_downward (Cs : set Clause) :
  forall n m n' m', pred_P Cs n m ->
  n' <= n -> m' <= m -> pred_P Cs n' m'.
Proof.
Admitted.

Definition lem_xx (Cs : set Clause) (V W : set string) (f : Frontier) :
  (* subject to change *)
  incl W V -> ex_lfp_geq Cs W W f -> ex_lfp_geq Cs V W f.
Proof.
Admitted.


Theorem thm_xx (Cs : set Clause) :
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
      inversion H1. apply le_lteq in H3. destruct H3.
      * apply (IHm f V W); try assumption. lia.
      * rewrite (@ex_lfp_geq_nodup_iff string) in H2.
        assert (ex_lfp_geq Cs (nodup string_dec W) (nodup string_dec W) f).
         -- apply (IHn n f (nodup string_dec W) []);
            try assumption; try apply incl_nil_l.
            ++ eapply (set_diff_succ string_dec) in H.
               ** apply succ_le_mono. eapply le_trans.
                  apply H. assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
                  --- eapply NoDup_incl_length. apply NoDup_nodup.
                      rewrite <- nodup_incl2. apply incl_refl.
                  --- eapply le_trans in H0. apply H0. assumption.
               ** apply H3.
            ++ rewrite set_diff_nil. eapply (set_diff_succ string_dec) in H.
               ** split; try lia. apply succ_le_mono. eapply le_trans.
                  apply H. assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
                  --- eapply NoDup_incl_length. apply NoDup_nodup.
                      rewrite <- nodup_incl2. apply incl_refl.
                  --- eapply le_trans in H0. apply H0. assumption.
               ** apply H3.
           ++ unfold ex_lfp_geq. exists f. split.
              apply geq_refl. apply sub_model_W_empty.
         -- assert (H': incl W V) by assumption.
            apply (nodup_incl2 string_dec) in H.
            apply (lem_xx Cs V (nodup string_dec W) f) in H;
            try assumption. elim H. intros h [H8 H9].
            destruct (sub_forward Cs V V h) as [U h'] eqn:Hforward.
            assert (sub_forward Cs V V h = (U, h')) by assumption.
            assert (sub_forward Cs V V h = (U, h')) by assumption.
            inversion Hforward. apply sub_forward_incl in Hforward.
            destruct U as [|u U'] eqn:Hu.
            ++ subst. apply sub_forward_empty in H6.
               destruct H6. unfold ex_lfp_geq. exists h. split;
               try assumption.
            ++ destruct (list_eq_dec string_dec V (set_union string_dec W U)).
               ** rewrite e. unfold ex_lfp_geq. exists frontier_infty. split.
                  --- apply geq_infty.
                  --- apply sub_model_infty.
               ** assert (Datatypes.length (set_union string_dec W U) < Datatypes.length (nodup string_dec V)).
                   admit.
                   assert (Datatypes.length (set_diff string_dec V (set_union string_dec W U)) < Datatypes.length (set_diff string_dec V W) <= S m).
                   admit.
                   apply (ex_lfp_geq_monotone Cs V h' f).
                   eapply (IHm h' V (set_union string_dec W U)).
                   --- (* H11 *) admit.
                   --- assumption.
                   --- lia.
                   --- apply (IHn n h' (set_union string_dec W U) []).
                       +++ apply incl_nil_l.
                       +++ (* use H0 and H11 + lemma about nodup & length *) admit.
                       +++ (* same as above *)  admit.
                       +++ unfold ex_lfp_geq. exists h'.
                           split. apply geq_refl.
                           apply sub_model_W_empty.
                   --- eapply geq_trans with h; try assumption.
                       (* apply sub_forward_geq in H10. *)
Admitted.

Theorem pre_thm32 (Cs : set Clause) (n : nat) (m : nat) (V : set string) :
  Datatypes.length V <= n ->
  (forall f : Frontier,
    (forall W : set string, strict_subset W V ->
      Datatypes.length (set_diff string_dec V W) <= m ->
      forall g : Frontier, geq W g f = true ->
      (sub_model Cs W W g = true) -> exists h, geq W h g = true /\ sub_model Cs V W h = true)
(* main implication *) ->
    exists h : Frontier, geq V h f = true /\ sub_model Cs (vars Cs) V h = true).
Proof.
  intros. induction n.
  - exists f. apply le_0_r in H.
    apply length_zero_iff_nil in H. rewrite H.
    split; try reflexivity. apply sub_model_W_empty.
  - destruct (sub_forward Cs V V f) as [W g] eqn:Hforward.
    apply (sub_forward_incl Cs f) in Hforward.
Admitted.

Theorem thm32 (Cs : set Clause) (f : Frontier) :
  exists h : Frontier,
    geq (vars Cs) h f = true /\ model Cs h = true.
Proof.
  intros. setoid_rewrite <- sub_model_eq_model;
  try apply incl_refl.
  apply (pre_thm32 Cs (List.length (vars Cs)) 0 (vars Cs)).
  intros; try reflexivity; try apply incl_refl.
  intros. exists g. split. apply geq_refl.
  apply le_0_r in H0. apply length_zero_iff_nil in H0.
  unfold strict_subset in H. destruct H as [H H'].
  apply set_diff_nil_incl in H0. contradiction.
Qed.

Lemma lem33 (Cs : set Clause) (W : set string) :
  let V := vars Cs in
  let V_m_W := set_diff string_dec V W in
  strict_subset W V ->
  forall f : Frontier, exists g : Frontier, (geq W g f) && sub_model Cs W W g = true ->
  forall f : Frontier, (forall v : string, (v € V_m_W) = true -> is_infty (f v) = true) ->
  exists h : Frontier, (forall v : string, (v € V_m_W) = true -> (h v) = (f v)) /\
  geq V h f = true /\ sub_model Cs (vars Cs) W h = true.
Proof.
Admitted.
