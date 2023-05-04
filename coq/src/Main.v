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
From Coq Require Import FunctionalExtensionality.
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

Definition pre_thm (n m : nat) (Cs : set Clause) (V W : set string) (f : Frontier) :=
  incl W V ->
  Datatypes.length (nodup string_dec V) <= n ->
  Datatypes.length
    (set_diff string_dec
      (nodup string_dec V)
      (nodup string_dec W)
    ) <= m <= n ->
  ex_lfp_geq Cs (nodup string_dec W) (nodup string_dec W) f ->
  ex_lfp_geq Cs (nodup string_dec V) (nodup string_dec V) f.

(* informal proof sketch, cf. TCS note.
Given Cs, V, W, and f, distinguish the following cases:

1. Some v in V has f(v)=Infty. Then we can simplify Cs
by eliminating all clauses with v in the conclusion, and
simplifying clauses by eliminating atoms with v in the premiss.
It may be that the premiss of a clause becomes empty, in which
case we know that also the variable in the conclusion is Infty.
We continue this process until the clause set cannot be simplified
any more. Call the remaining clause set Cs', with variables in V',
which is a strict subset of V. Now apply the first condition of
lem33 to Cs', V'and W' empty to get a model of Cs' restricted to V'.
Then we can extend this with value Infty for variables in V\V'
to a model of Cs restricted to V.

2. Not 1, so f: V->N. Now we can apply the method from the TCS note
and termination is guaranteed since variables in V-W have values in N
which do not change, and "bound" clauses having such a variable in
the premiss.

Matthieu Sozeau has a formal proof of termination in this case. *)

Definition exists_pred_stuff (V : set string) (f : Frontier) :
  {exists v : string, (In v V) /\ (f v = infty)} +
  {forall v : string, In v V -> f v <> infty}.
Proof.
  induction V as [|v V' IHV'].
  - right. intros. inversion H.
  - destruct IHV' as [IH|IH].
    + left. elim IH.
      intros. exists x. destruct H.
      split. right. assumption. assumption.
    + destruct (f v) eqn:Hf.
      * left. exists v.
        split. left. reflexivity. assumption.
      * right. intros. destruct H as [H|H].
        -- rewrite H in Hf. rewrite Hf. discriminate.
        -- apply IH. assumption.
Qed.

Lemma fold_right_andb_true_map_incl_vars_set_atom_false (V W : set string) (l : set Atom) :
  incl W V ->
  fold_right andb true
    (map
      (fun x : string => x € nodup string_dec W)
      (vars_set_atom l)) = false ->
  fold_right andb true
    (map
      (fun x : string => x € nodup string_dec V)
      (vars_set_atom l)) = false.
Proof.
  intros.
  induction V as [|v V].
  - destruct W.
    + simpl in *. assumption.
    + apply incl_l_nil_false in H.
      contradiction. discriminate.
  - simpl. destruct (in_dec string_dec v V).
    + apply IHV. induction W as [|w W].
      * apply incl_nil_l.
      * apply incl_cons_inv in H.
        destruct H. apply incl_cons.
        -- simpl in H, H1. destruct H;
           subst; assumption.
        -- apply IHW; try assumption.
           ++ simpl in H0.
              rewrite <- H0.
              f_equal. f_equal.
              apply functional_extensionality.
              intros. destruct (in_dec string_dec w W);
              try reflexivity.
              simpl. destruct (string_dec x w);
              try reflexivity. subst.
              apply set_mem_correct2. unfold set_In.
              apply nodup_In.  simpl in H.
              destruct H.
              ** subst.
Admitted.

Lemma all_shifts_true_geq (c : Clause) (V : set string) (f g : Frontier) :
  all_shifts_true c f = true ->
  geq V f g = true ->
  all_shifts_true c g = true.
Proof.
  intros. destruct c as [l [x k]].
  induction k as [|k].
  - simpl. destruct (g x) eqn:Hgx; try reflexivity.
    destruct (f x) eqn:Hfx; try reflexivity.
    simpl in H. rewrite Hfx in H.
    + destruct (fold_right andb true (map (fun a : Atom => atom_true a g) (map (shift_atom (n + 1 - 0)) l)));
      try reflexivity.
Admitted.


Lemma lem_33 :
  forall Cs : set Clause,
  forall V W : set string,
  forall f : Frontier,
    (forall Cs' : set Clause,
     forall V' W' : set string,
     forall f' : Frontier,
     forall m : nat,
      pre_thm (Datatypes.length (nodup string_dec V) - 1) m Cs' V' W' f'
    ) ->
    incl W V ->
    ex_lfp_geq Cs (nodup string_dec W) (nodup string_dec W) f ->
    ex_lfp_geq Cs (nodup string_dec V) (nodup string_dec W) f.
Proof.
  intros.
  destruct (exists_pred_stuff V f).
  - induction Cs as [|c Cs].
    + unfold ex_lfp_geq.
      unfold ex_lfp_geq_S. exists f.
      split; try apply geq_refl; try reflexivity.
    + unfold ex_lfp_geq.
      unfold ex_lfp_geq_S. exists f.
      split; try apply geq_refl.
      unfold sub_model. fold sub_model.
      destruct c as [l [x k]].
      apply andb_true_iff. split.
      * unfold ex_lfp_geq in H0. unfold ex_lfp_geq_S in H0.
        elim H0. intros. destruct p.
        unfold sub_model in e1. fold sub_model in e1.
        apply andb_true_iff in e1. destruct e1.
        repeat rewrite orb_true_iff in H1.
        destruct H1. destruct H1.
        -- rewrite H1. apply orb_true_l.
        -- repeat rewrite orb_true_iff.
           left. right. apply negb_true_iff.
           apply negb_true_iff in H1.
           apply (fold_right_andb_true_map_incl_vars_set_atom_false V W);
           try assumption.
        -- repeat rewrite orb_true_iff.
           right.



Admitted.

Theorem thm_32 :
  forall n m : nat,
  forall Cs : set Clause,
  forall V W : set string,
  forall f : Frontier,
    pre_thm n m Cs V W f.
Proof.
  unfold pre_thm. induction n as [|n IHn].
  - intros. apply le_0_r in H0.
    apply length_zero_iff_nil in H0.
    rewrite H0. apply ex_lfp_geq_empty.
  - induction m as [|m IHm]; intros.
    + apply (ex_lfp_geq_incl Cs (nodup string_dec V) (nodup string_dec W));
      try assumption. destruct H1. apply le_0_r in H1.
      apply length_zero_iff_nil in H1.
      apply set_diff_nil_incl in H1. assumption.
    + inversion H1.
      apply le_lt_eq_dec in H3. destruct H3.
      * apply (IHm Cs V W f); try assumption. lia.
      * apply (ex_lfp_geq_nodup_iff) in H2.
        assert (Datatypes.length (nodup string_dec W) <= n).
        {
           eapply (set_diff_succ string_dec) in H; try apply H3.
           apply succ_le_mono. eapply le_trans.
           apply H.
           - eapply le_trans in H0. apply H0. apply le_refl.
           - apply e.
         }
         assert (ex_lfp_geq Cs (nodup string_dec W) (nodup string_dec W) f).
         {
            apply (IHn n Cs W [] f);
            try assumption; try apply incl_nil_l.
            - eapply (set_diff_succ string_dec) in H; try apply H3.
              simpl. rewrite set_diff_nil. apply conj; lia. apply e.
            - unfold ex_lfp_geq. exists f. split.
              apply geq_refl. apply sub_model_W_empty.
          }
          assert (H': incl W V) by assumption.
          apply (nodup_incl2 string_dec) in H.
          apply (lem_33 Cs V (nodup string_dec W) f) in H;
          try assumption. elim H. intros h [H8 H9].
          destruct (sub_forward Cs (nodup string_dec V) (nodup string_dec V) h) as [U h'] eqn:Hforward.
          assert (sub_forward Cs (nodup string_dec V) (nodup string_dec V) h = (U, h')) by assumption.
          assert (sub_forward Cs (nodup string_dec V) (nodup string_dec V) h = (U, h')) by assumption.
          rewrite nodup_rm in H9.
          apply (sub_forward_incl_set_diff Cs h h' (nodup string_dec V) (nodup string_dec W) U) in H9; try apply Hforward.
          inversion Hforward. apply sub_forward_incl in Hforward.
          destruct U as [|u U'] eqn:Hu.
          -- apply sub_forward_empty in H7.
             destruct H7. unfold ex_lfp_geq. exists h. split; assumption.
          -- destruct (incl_dec string_dec V (nodup string_dec (set_union string_dec (nodup string_dec W) U))).
             ++ unfold ex_lfp_geq. exists (update_infty_V V f). split.
                ** apply geq_nodup_true. apply geq_update_infty_V.
                ** rewrite <- sub_model_nodup. apply sub_model_update_infty_V.
             ++ assert (incl (nodup string_dec (set_union string_dec W U)) V).
                {
                  apply nodup_incl2. eapply incl_set_union_trans.
                  assumption. apply nodup_incl in Hforward.
                  rewrite Hu. assumption.
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
                      apply nodup_incl2 in H13.
                      assert (incl (nodup string_dec (set_union string_dec W U)) (nodup string_dec V)).
                      {
                        apply nodup_incl. assumption.
                      }
                      rewrite (incl_set_union_nodup_l string_dec). assumption.
                  }
                  apply (strict_subset_lt_length string_dec).
                  unfold strict_subset in H13.
                  destruct H13. unfold strict_subset. split.
                  - apply nodup_incl in H13.
                    apply nodup_incl2 in H13. assumption.
                  - unfold not. intros. apply n0.
                    rewrite (incl_set_union_nodup_l string_dec).
                    apply nodup_incl. assumption.
                }
                (*
                   fails here (?)
                   when W goes from empty to non-empty
                   and then does not increase further in next step.
                *)
                assert (Datatypes.length (set_diff string_dec V (set_union string_dec (nodup string_dec W) U)) < Datatypes.length (set_diff string_dec V (nodup string_dec W)) <= S m).
                {
                  apply conj.
                  - rewrite Hu. apply set_diff_incl_lt_length;
                    try assumption. apply nodup_incl2. assumption.
                    rewrite <- set_diff_nodup_l in H9. assumption.
                  - rewrite <- set_diff_nodup_r.
                    rewrite <- set_diff_nodup_eq. rewrite e. lia.
                }
                apply (ex_lfp_geq_monotone Cs (nodup string_dec V) h' f).
                eapply (IHm Cs V (nodup string_dec (set_union string_dec W U)) h');
                try assumption.
                ** apply conj; try lia. inversion H14.
                   apply le_lt_eq_dec in H16. destruct H16;
                   rewrite nodup_rm; rewrite set_diff_nodup_eq in *;
                   rewrite <- length_set_diff_set_union_nodup_l;
                   lia.
                ** apply (IHn n Cs (nodup string_dec (set_union string_dec W U)) [] h');
                   try apply incl_nil_l.
                   --- assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
                       {
                         apply NoDup_incl_length. apply NoDup_nodup.
                         apply nodup_incl2. apply incl_refl.
                       }
                       rewrite nodup_rm. rewrite set_diff_nodup_eq in *;
                       try rewrite set_union_nodup_l in *; lia.
                   --- apply conj; try lia.
                       assert (Datatypes.length (set_diff string_dec (nodup string_dec (set_union string_dec W U)) []) <= Datatypes.length (nodup string_dec (set_union string_dec W U))).
                       apply (set_diff_nil_length string_dec).
                       eapply le_trans.
                       rewrite set_diff_nodup_eq. apply H15. apply lt_le_pred in H13.
                       eapply le_trans. apply H13.
                       assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
                       {
                          apply NoDup_incl_length. apply NoDup_nodup.
                          apply nodup_incl2. apply incl_refl.
                       }
                       assert (pred (Datatypes.length (nodup string_dec V)) <= pred (Datatypes.length V)).
                       {
                         apply Nat.pred_le_mono. assumption.
                       }
                       apply le_n_Sm_pred_n_m in H0. assumption.
                   --- unfold ex_lfp_geq. exists h'.
                       split. apply geq_refl.
                       apply sub_model_W_empty.
                ** eapply geq_trans with h; try assumption.
                   rewrite <- H12.
                   apply geq_Sinfty_f2.
          -- unfold pre_thm. intros. apply (IHn m0 Cs' V' W' f');
             try assumption; try lia.
          -- rewrite nodup_rm. assumption.
Qed.
