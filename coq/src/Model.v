From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Sets. Import Sets.
Require Import Clause. Import Clause.
Require Import Atom. Import Atom.
Require Import Frontier. Import Frontier.
Require Import Vars. Import Vars.
Require Import Misc. Import Misc.
Require Import Ninfty. Import Ninfty.

Module Model.

  Fixpoint model (Cs : set Clause) (f : Frontier) : bool :=
    match Cs with
    | []      => true
    | h :: t  => all_shifts_true h f && model t f
    end.

  Fixpoint sub_model (Cs : set Clause) (V W : set string) (f : Frontier) : bool :=
    match Cs with
    | []      => true
    | (l ~> (x & k)) :: t  =>
        (negb (set_mem string_dec x W) ||
         negb (fold_right andb true (map (fun x => set_mem string_dec x V) (vars_set_atom l))) ||
         all_shifts_true (l ~> (x & k)) f
        ) && sub_model t V W f
    end.

  Lemma fold_right_andb_true_map_incl_iff (V W : set string) :
    incl W V <->
    fold_right andb true (map (fun x => set_mem string_dec x V) W) = true.
  Proof.
    split; intros; induction W as [|h t];
    try reflexivity; try apply incl_nil_l.
    - apply incl_cons_inv in H. destruct H as [H1 H2].
      simpl. apply andb_true_iff. split.
      + apply set_mem_correct2. unfold set_In. apply H1.
      + apply IHt. apply H2.
    - simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply set_mem_correct1 in H1. unfold set_In in H1.
      apply incl_cons; try assumption.
      apply IHt. assumption.
  Qed.

  Lemma fold_right_andb_false_map_not_incl_iff (V W : set string) :
    ~ incl W V <->
    fold_right andb true (map (fun x => set_mem string_dec x V) W) = false.
  Proof.
    rewrite fold_right_andb_true_map_incl_iff.
    split; intros.
    - apply not_true_is_false in H. assumption.
    - unfold not. intros. rewrite H in H0. discriminate.
  Qed.

  Lemma sub_model_W_empty (Cs : set Clause) (V : set string) (f : Frontier) :
    sub_model Cs V [] f = true.
  Proof.
    induction Cs; try reflexivity.
    simpl. try repeat destruct a. assumption.
  Qed.

  Lemma sub_model_eq_model (Cs : set Clause) (f : Frontier) :
    forall W, incl (vars Cs) W -> sub_model Cs W W f = model Cs f.
  Proof.
    intros W Incl. induction Cs; try reflexivity.
    destruct (all_shifts_true a f) eqn:Aaf;
    destruct a as [l [x k]];
    unfold model; unfold sub_model; rewrite Aaf;
    fold sub_model; fold model; erewrite IHCs.
    - simpl. rewrite orb_true_r. simpl. reflexivity.
    - simpl in Incl. apply incl_app_inv in Incl. apply Incl.
    - rewrite vars_cons in Incl. apply incl_app_inv in Incl.
      destruct Incl as [Incl Incl']. assert (incl (vars_clause (l ~> (x & k))) W) by assumption.
      rewrite vars_set_atom_incl_fold.
      + simpl. destruct (set_mem string_dec x W) eqn:Hxw; try reflexivity.
        * apply set_mem_complete1 in Hxw.
          apply vars_clause_incl_In in H. contradiction.
      + apply vars_clause_incl_vars_set_atom in H. assumption.
    - simpl in Incl. apply incl_app_inv in Incl. apply Incl.
  Qed.

  Lemma sub_model_monotone_false (Cs : set Clause) (f : Frontier) :
    forall X X' Y Y', incl X X' -> incl Y Y' ->
    sub_model Cs X Y f = false -> sub_model Cs X' Y' f = false.
  Proof.
    intros. induction Cs; try discriminate.
    simpl. destruct a as [l [x k]]. destruct (f x) eqn:Hfx.
    simpl in H1. rewrite Hfx in H1. rewrite orb_true_r in H1.
    rewrite andb_true_l in H1.
    - apply IHCs in H1. rewrite H1. rewrite orb_true_r. reflexivity.
    - apply andb_false_iff.
      unfold sub_model in H1. fold sub_model in H1.
      apply andb_false_iff in H1. destruct H1.
      + apply orb_false_iff in H1. destruct H1.
        apply orb_false_iff in H1. destruct H1.
        apply negb_false_iff in H1. apply set_mem_correct1 in H1.
        assert ((set_mem string_dec x Y') = true).
        * apply set_mem_correct2. apply H0. assumption.
        * left. rewrite H4. simpl. simpl in H2.
           rewrite Hfx in H2. rewrite H2. rewrite orb_false_r.
           rewrite negb_false_iff.
           eapply incl_fold_right_andb_true; try apply H.
           rewrite negb_false_iff in H3. assumption.
      + right. apply IHCs. assumption.
  Qed.

  Lemma sub_model_monotone (Cs : set Clause) (f : Frontier) :
    forall X X' Y Y', incl X X' -> incl Y Y' ->
    sub_model Cs X' Y' f = true -> sub_model Cs X Y f = true.
  Proof.
    induction Cs; try reflexivity.
    intros. destruct a as [l [x k]]. destruct (f x) eqn:Hfx.
    - simpl in *. try rewrite Hfx in *.
      try rewrite orb_true_r in *. simpl in *. eapply IHCs.
      apply H. apply H0. apply H1.
    - simpl in H1. rewrite Hfx in H1.
      apply andb_true_iff in H1. destruct H1.
      simpl. rewrite Hfx. apply andb_true_iff. split.
      + destruct (set_mem string_dec x Y) eqn:HxY; destruct (set_mem string_dec x Y') eqn:HxY'; try reflexivity.
        * simpl in *. apply orb_true_iff. apply orb_true_iff in H1.
          destruct H1.
          -- left. apply negb_true_iff. apply negb_true_iff in H1.
             eapply incl_fold_right_andb_false in H1.
             ++ apply H1.
             ++ assumption.
          -- right. assumption.
        * apply set_mem_correct1 in HxY.
          apply set_mem_complete1 in HxY'.
          apply H0 in HxY. contradiction.
      + eapply IHCs. apply H. apply H0. apply H2.
  Qed.

  Lemma sub_model_infty (Cs : set Clause) (V W : set string) :
    sub_model Cs V W frontier_infty = true.
  Proof.
    induction Cs as [|h t]; try reflexivity.
    unfold sub_model. fold sub_model. destruct h as [l [x k]].
    apply andb_true_iff. split; try assumption.
    destruct V as [|v V]; destruct W as [|w W];
    try reflexivity; simpl in *; rewrite orb_true_r; reflexivity.
  Qed.

  Lemma sub_model_nodup (Cs : set Clause) (V : set string) (f : Frontier) :
    sub_model Cs V V f = sub_model Cs (nodup string_dec V) (nodup string_dec V) f.
  Proof.
    induction Cs as [|h t]; try reflexivity.
    unfold sub_model. fold sub_model. destruct h as [l [x k]].
    rewrite IHt. assert ((negb (set_mem string_dec x V)) = (negb (set_mem string_dec x (nodup string_dec V)))).
    - destruct V; try reflexivity.
      simpl. destruct (string_dec x s); destruct (in_dec string_dec s V).
      + simpl. symmetry. apply negb_false_iff. apply (set_mem_correct2 string_dec).
        rewrite <- (nodup_In string_dec) in i. subst. assumption.
      + simpl. subst. destruct (string_dec s s); try reflexivity.
        contradiction.
      + f_equal. destruct (set_mem string_dec x V) eqn:HxV; symmetry.
        * apply set_mem_correct2. unfold set_In. apply set_mem_correct1 in HxV.
          unfold set_In in HxV. rewrite nodup_In. assumption.
        * apply set_mem_complete2. unfold set_In. apply set_mem_complete1 in HxV.
          unfold set_In in HxV. rewrite nodup_In. assumption.
      + simpl. destruct (string_dec x s); subst; try contradiction.
        f_equal. destruct (set_mem string_dec x V) eqn:HxV; symmetry.
        * apply set_mem_correct2. unfold set_In. apply set_mem_correct1 in HxV.
          unfold set_In in HxV. rewrite nodup_In. assumption.
        * apply set_mem_complete2. unfold set_In. apply set_mem_complete1 in HxV.
          unfold set_In in HxV. rewrite nodup_In. assumption.
    - rewrite H. assert (incl V (nodup string_dec V)).
      apply nodup_incl. apply incl_refl.
      assert (negb (fold_right andb true (map (fun x0 : string => set_mem string_dec x0 (nodup string_dec V)) (vars_set_atom l))) = (negb (fold_right andb true (map (fun x : string => set_mem string_dec x V) (vars_set_atom l))))).
      + destruct (negb (fold_right andb true (map (fun x0 : string => set_mem string_dec x0 (nodup string_dec V)) (vars_set_atom l)))) eqn:HndV.
        * symmetry. apply negb_true_iff. apply negb_true_iff in HndV.
          eapply incl_fold_right_andb_false. apply H0. assumption.
        * symmetry. rewrite negb_false_iff in *.
          eapply incl_fold_right_andb_true. assert (incl (nodup string_dec V) V).
          rewrite <- (nodup_incl string_dec). apply incl_refl. apply H1.
          assumption.
      + rewrite H1. reflexivity.
  Qed.

  (* NEEDED *)
  Lemma sub_model_update_infty_V (Cs : set Clause) (V : set string) (f : Frontier) :
    sub_model Cs V V (update_infty_V V f) = true.
  Proof.
    generalize dependent f.
    induction Cs as [|c Cs]; intros; try reflexivity.
    destruct c as [l [x k]]. unfold sub_model. fold sub_model.
    apply andb_true_iff. split; try apply IHCs.
    repeat rewrite orb_true_iff. destruct (negb (set_mem string_dec x V)) eqn:HxV;
    destruct (negb (fold_right andb true (map (fun x0 : string => set_mem string_dec x0 V) (vars_set_atom l)))) eqn:Hfold;
    destruct (all_shifts_true (l ~> x & k) (update_infty_V V f)) eqn:Hast;
    try auto.
  Admitted.
  (*
    - destruct l. simpl in Hast. destruct (update_infty_V V f x) eqn:Hfx.
      -- discriminate.
      -- simpl in Hfold. induction n.

      left. apply negb_false_iff in HxV, Hfold.
      assert (Hfold' := Hfold).
      apply fold_right_andb_true_map_incl_iff in Hfold.
      eapply (incl_fold_right_andb_true) in Hfold.
      + apply HxV.
      + apply incl_refl.


    induction V as [|h t]; intros.
    - unfold update_infty_V. simpl.
      assert ((fun x : string => f x) = f).
      + apply functional_extensionality. intros. reflexivity.
      + rewrite H. induction Cs as [|c Cs]; try reflexivity.
        destruct c as [l [x k]]. simpl. assumption.
    - unfold update_infty_V. fold update_infty_V.
      + induction Cs as [|c Cs]; try reflexivity.
        destruct c as [l [x k]]. unfold sub_model. fold sub_model.
        apply andb_true_iff. split.
        * repeat rewrite orb_true_iff.
          destruct (negb (set_mem string_dec x (h :: t))) eqn:Hxht; try reflexivity.
          -- left. left. reflexivity.
          -- assert (Hxht' := Hxht).
             apply negb_false_iff in Hxht'.
             apply set_mem_correct1 in Hxht'.
             unfold set_In in *.
             right. apply In_incl_singleton in Hxht'.
             assert (sub_model ([l ~> x & k]) [x] [x] (fun x0: string => if set_mem string_dec x0 (h :: t) then infty else f x0) = true).
             ++ eapply sub_model_monotone.
                ** apply Hxht'.
                ** apply Hxht'.
                ** admit.
             ++ unfold sub_model in H. fold sub_model in H.
                apply andb_true_iff in H. destruct H as [H _].
                repeat rewrite orb_true_iff in H. destruct H;
                destruct H.
                ** simpl in H. destruct (string_dec x x).
                   --- discriminate.
                   --- contradiction.
                ** simpl in H.

             eapply sub_model_monotone in Hxht.
          unfold sub_model in IHt. fold sub_model in IHt.
          admit.
        * apply IHCs. unfold sub_model in IHt. fold sub_model in IHt.
          setoid_rewrite andb_true_iff in IHt. intros.
          destruct (IHt f0) as [IHt1 IHt2]. apply IHt2.
  Admitted.
   *)

  Example sub_model_test1 :
    sub_model
      [clause_x0y1_x2]
      [x_str; y_str]
      [x_str]
      frontier_infty
    = true.
  Proof. reflexivity. Qed.

  Example sub_model_test2 :
    sub_model
      [clause_x0y1_x2]
      [x_str]
      [x_str]
      frontier_infty
    = true.
  Proof. reflexivity. Qed.

  Example sub_model_test3 :
    sub_model
      [clause_x0y1_x2]
      [x_str; y_str]
      [x_str]
      frontier_fin_1
    = false.
  Proof. reflexivity. Qed.

  Example sub_model_test4 :
    sub_model
      [clause_x0y1_x2]
      [x_str]
      [x_str]
      frontier_fin_1
    = true.
  Proof. reflexivity. Qed.

End Model.
