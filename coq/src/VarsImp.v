From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List. Import ListNotations. From Coq Require Import Lists.ListSet. From Coq Require Import Strings.String.
Require Import Clause. Import Clause.
Require Import Atom. Import Atom.
Require Import Frontier. Import Frontier.
Require Import Sets. Import Sets. Import StringSetsNotation.
Require Import Vars. Import Vars.
Require Import Model. Import Model.

Module VarsImp.

  Fixpoint vars_improvable (Cs : set Clause) (f : Frontier) : set string :=
    match Cs with
    | []      => []
    | (l ~> (x & k)) :: t  =>
        if all_shifts_true (l ~> (x & k)) f
        then vars_improvable t f
        else set_add string_dec x (vars_improvable t f)
    end.

  Fixpoint sub_vars_improvable (Cs : set Clause) (V W : set string) (f : Frontier) : set string :=
    match Cs with
    | []      => []
    | (l ~> (x & k)) :: t  =>
        if negb (x € W) ||
           negb (fold_right andb true (map (fun x => x € V) (vars_set_atom l))) ||
           all_shifts_true (l ~> (x & k)) f
        then sub_vars_improvable t V W f
        else set_add string_dec x (sub_vars_improvable t V W f)
    end.

  Lemma sub_vars_improvable_NoDup_Cs (Cs : set Clause) (f : Frontier) :
    forall V W,
      NoDup Cs ->
      NoDup (sub_vars_improvable Cs V W f).
  Proof.
    induction Cs as [|h t]; intros.
    - simpl. apply NoDup_nil.
    - unfold sub_vars_improvable. destruct h as [l [x k]].
      fold sub_vars_improvable.
      destruct (negb (x € W)
                || negb (fold_right andb true (map (fun x0 : string => x0 € V) (vars_set_atom l))) 
                || all_shifts_true (l ~> x & k) f).
    + apply IHt. apply NoDup_cons_iff in H. destruct H. assumption.
    + apply set_add_nodup. apply IHt. apply NoDup_cons_iff in H.
      destruct H. assumption.
  Qed.

  Lemma sub_vars_improvable_incl_W (Cs : set Clause) (V W : set string) (f : Frontier) :
    incl (sub_vars_improvable Cs V W f) W.
  Proof.
    induction Cs as [|h t]; try apply incl_nil_l.
    destruct h as [l [x k]]. (* key *)
    destruct (all_shifts_true (l ~> (x & k)) f) eqn:Hhtf.
    - unfold sub_vars_improvable. rewrite Hhtf.
      fold sub_vars_improvable. (* candidate for tactic *)
      unfold incl; intros. rewrite orb_true_r in H. eapply incl_tran.
      apply IHt. apply incl_refl. assumption.
    - unfold sub_vars_improvable. rewrite Hhtf.
      fold sub_vars_improvable. (* candidate for tactic *)
      unfold incl; intros. rewrite orb_false_r in H.
      (* key *) destruct (string_dec a x).
      + subst. destruct (negb (x € W)) eqn:HxW.
        * simpl in H. eapply incl_tran. apply IHt.
          apply incl_refl. assumption.
        * simpl in H. destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l)))).
          -- eapply incl_tran. apply IHt. apply incl_refl. assumption.
          -- apply negb_false_iff in HxW. apply set_mem_correct1 in HxW.
             assumption.
      + destruct (negb (x € W)) eqn:HxW.
        * simpl in H. eapply incl_tran. apply IHt. apply incl_refl.
          assumption.
        * destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l)))).
          -- simpl in H. eapply incl_tran. apply IHt. apply incl_refl.
             assumption.
          -- simpl in H. apply negb_false_iff in HxW.
             apply set_add_mem_true in HxW.
             apply set_add_elim in H. destruct H.
             ++ contradiction.
             ++ eapply incl_tran. apply IHt. apply incl_refl. assumption.
  Qed.

  Lemma sub_vars_improvable_cons_empty (h : Clause) (t : set Clause) (V W : set string) (f : Frontier) :
    sub_vars_improvable (h :: t) V W f = [] ->
    sub_vars_improvable t V W f = [].
  Proof.
    intros. induction t as [|h' t]; try reflexivity.
    unfold sub_vars_improvable in H. destruct h as [l [x k]].
    destruct h' as [l' [x' k']]. fold sub_vars_improvable in H.
    destruct (all_shifts_true (l ~> x & k) f) eqn:Hhtf;
    destruct (all_shifts_true (l' ~> x' & k') f) eqn:Hhtf'.
    - unfold sub_vars_improvable. fold sub_vars_improvable.
      rewrite Hhtf'. rewrite orb_true_r in *.
      rewrite orb_true_r in H. assumption.
    - unfold sub_vars_improvable. fold sub_vars_improvable.
      rewrite Hhtf'. rewrite orb_true_r in *.
      rewrite orb_false_r in *. assumption.
    - rewrite orb_true_r in *. rewrite orb_false_r in H.
      destruct (negb (x € W)) eqn:HxW.
      + simpl in H. rewrite <- H.
        unfold sub_vars_improvable. fold sub_vars_improvable.
        destruct (negb (x' € W)); try reflexivity.
        rewrite orb_false_l.
        destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l'))));
        try reflexivity. rewrite orb_false_l. rewrite Hhtf'.
        reflexivity.
      + rewrite orb_false_l in H.
        destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l)))).
        * unfold sub_vars_improvable. fold sub_vars_improvable.
          rewrite Hhtf'. rewrite orb_true_r. assumption.
        * apply set_add_not_empty in H. contradiction.
    - unfold sub_vars_improvable. fold sub_vars_improvable.
      rewrite Hhtf'. rewrite orb_false_r in *.
      destruct (negb (x' € W));
      simpl; simpl in H; try rewrite orb_false_r in H;
      destruct (negb (x € W)); simpl in H; try assumption;
      destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l))));
      try assumption; apply set_add_not_empty in H; contradiction.
  Qed.

  Lemma sub_vars_improvable_incl_set_diff (Cs : set Clause) (V W : set string) (f : Frontier) :
    incl (sub_vars_improvable Cs V W f) (set_diff string_dec W V).
  Proof.
    induction Cs as [|h t]; try reflexivity.
    unfold incl; intros. unfold sub_vars_improvable in H.
    - contradiction.
    - destruct h as [l [x k]].
      destruct (all_shifts_true (l ~> x & k) f) eqn:Hhtf.
      + unfold incl; intros. eapply incl_tran. apply IHt. apply incl_refl.
        unfold sub_vars_improvable in H. fold sub_vars_improvable in H.
        rewrite Hhtf in H. rewrite orb_true_r in H. assumption.
      + unfold incl; intros. eapply incl_tran. apply IHt. apply incl_refl.
        unfold sub_vars_improvable in H. fold sub_vars_improvable in H.
        rewrite Hhtf in H. rewrite orb_false_r in H.
        destruct (negb (x € W)) eqn:HxW;
        destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l))));
        simpl in H; try assumption. apply negb_false_iff in HxW.
        destruct (in_dec string_dec x (sub_vars_improvable t V W f)).
        * apply (set_add_In string_dec) in i. rewrite i in H.
          assumption.
        * exfalso. apply n. apply (set_add_not_In string_dec) in n.
          rewrite n in H. apply in_app_or in H. destruct H.
          --
  Admitted.

  Lemma sub_vars_improvable_refl_nil (Cs : set Clause) (V : set string) (f : Frontier) :
    sub_vars_improvable Cs V V f = [].
  Proof.
    assert (incl (sub_vars_improvable Cs V V f) (set_diff string_dec V V)).
    apply sub_vars_improvable_incl_set_diff.
    destruct (sub_vars_improvable Cs V V f) eqn:Hsvi; try reflexivity.
    rewrite set_diff_refl_nil in H. apply incl_l_nil_false in H.
    contradiction. discriminate.
  Qed.

  Lemma sub_vars_improvable_nodup (Cs : set Clause) (f : Frontier) :
    forall V,
      sub_vars_improvable Cs V V f =
      sub_vars_improvable Cs (nodup string_dec V) (nodup string_dec V) f.
  Proof.
    intros. rewrite sub_vars_improvable_refl_nil.
    rewrite sub_vars_improvable_refl_nil. reflexivity.
  Qed.

  (*
    induction Cs as [|h t]; intros; try reflexivity.
    destruct h as [l [x k]]. (* key *)
    destruct (all_shifts_true (l ~> (x & k)) f) eqn:Hhtf.
    - unfold sub_vars_improvable. rewrite Hhtf.
      fold sub_vars_improvable. (* candidate for tactic *)
      unfold incl; intros. rewrite orb_true_r. rewrite orb_true_r.
      apply IHt. 
    - unfold sub_vars_improvable. rewrite Hhtf.
      fold sub_vars_improvable. (* candidate for tactic *)
      rewrite orb_false_r. rewrite orb_false_r.
      destruct (negb (x € V)) eqn:HxW.
      + rewrite orb_true_l.
        apply negb_true_iff in HxW. apply set_mem_complete1 in HxW.
        rewrite <- (nodup_In string_dec) in HxW.
        apply (set_mem_complete2 string_dec) in HxW.
        rewrite HxW. simpl. apply IHt.
      + rewrite orb_false_l.
        apply negb_false_iff in HxW. apply set_mem_correct1 in HxW.
        rewrite <- (nodup_In string_dec) in HxW.
        apply (set_mem_correct2 string_dec) in HxW.
        rewrite HxW. simpl.
        destruct (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l)));
        destruct (fold_right andb true (map (fun x : string => x € nodup string_dec V) (vars_set_atom l))).
        * simpl. f_equal. apply IHt.
        * simpl. apply set_mem_correct1 in HxW.

  Admitted.

        rewrite HxW. simpl. apply IHt.
        * simpl in H. eapply incl_tran. apply IHt.
          apply incl_refl. assumption.
        * simpl in H. destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l)))).
          -- eapply incl_tran. apply IHt. apply incl_refl. assumption.
          -- apply negb_false_iff in HxW. apply set_mem_correct1 in HxW.
             assumption.
      + destruct (negb (x € W)) eqn:HxW.
        * simpl in H. eapply incl_tran. apply IHt. apply incl_refl.
          assumption.
        * destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l)))).
          -- simpl in H. eapply incl_tran. apply IHt. apply incl_refl.
             assumption.
          -- simpl in H. apply negb_false_iff in HxW.
             apply set_add_mem_true in HxW.
             apply set_add_elim in H. destruct H.
             ++ contradiction.
             ++ eapply incl_tran. apply IHt. apply incl_refl. assumption.

    induction Cs as [|h t]; intros; try reflexivity.
    unfold sub_vars_improvable. destruct h as [l [x k]].
    fold sub_vars_improvable.
    destruct (negb (fold_right andb true (map (fun x0 : string => x0 € V) (vars_set_atom l))) 
              || all_shifts_true (l ~> x & k) f) eqn:Hor;
    destruct (negb (fold_right andb true (map (fun x0 : string => x0 € nodup string_dec V) (vars_set_atom l)))
              || all_shifts_true (l ~> x & k) f) eqn:Hor';
    destruct (negb (x € V)) eqn:HxV;
    destruct (negb (x € nodup string_dec V)) eqn:HxV'.
    - simpl. apply IHt.
    - rewrite orb_false_l. rewrite orb_true_l. rewrite Hor'.
      apply IHt.
    - rewrite orb_false_l. rewrite orb_true_l. rewrite Hor.
      apply IHt.
    - rewrite orb_false_l. rewrite orb_false_l. rewrite Hor.
      rewrite Hor'. apply IHt.
    - rewrite orb_true_l. rewrite orb_true_l. apply IHt.
    - rewrite orb_false_l. rewrite orb_true_l. rewrite Hor'.
      apply negb_true_iff in HxV. apply negb_false_iff in HxV'.
      apply set_mem_complete1 in HxV. apply set_mem_correct1 in HxV'.
      apply nodup_In in HxV'. contradiction.
    - rewrite orb_true_l. rewrite orb_false_l.
      rewrite Hor. apply IHt.
    - rewrite orb_false_l. rewrite orb_false_l.
      rewrite Hor. rewrite Hor'.
      apply negb_false_iff in HxV. apply set_mem_correct1 in HxV.
      assert (In x (sub_vars_improvable t (nodup string_dec V) (nodup string_dec V) f)).
      { admit. }
      apply (set_add_In string_dec) in H. rewrite H.
      apply IHt.
    - rewrite orb_true_l. rewrite orb_true_l. apply IHt.
    - rewrite orb_true_l. rewrite orb_false_l. rewrite Hor'.
      apply IHt.
    - rewrite orb_true_l. rewrite orb_false_l. rewrite Hor.
      apply negb_true_iff in HxV'. apply negb_false_iff in HxV.
      apply set_mem_complete1 in HxV'. apply set_mem_correct1 in HxV.
      rewrite nodup_In in HxV'. contradiction.
    - rewrite orb_false_l. rewrite orb_false_l.
      rewrite Hor. rewrite Hor'.
      apply negb_false_iff in HxV. apply set_mem_correct1 in HxV.
      assert (In x (sub_vars_improvable t V V f)).
      { admit. }
      apply (set_add_In string_dec) in H. rewrite H.
      apply IHt.
    - rewrite orb_true_l. rewrite orb_true_l. apply IHt.
    - rewrite orb_true_l. rewrite orb_false_l. rewrite Hor'.
      apply negb_true_iff in HxV. apply negb_false_iff in HxV'.
      apply set_mem_complete1 in HxV. apply set_mem_correct1 in HxV'.
      rewrite nodup_In in HxV'. contradiction.
    - rewrite orb_true_l. rewrite orb_false_l. rewrite Hor.
      apply negb_true_iff in HxV'. apply negb_false_iff in HxV.
      apply set_mem_complete1 in HxV'. apply set_mem_correct1 in HxV.
      rewrite nodup_In in HxV'. contradiction.
    - rewrite orb_false_l. rewrite orb_false_l. rewrite Hor.
      rewrite Hor'.
      apply negb_false_iff in HxV. apply set_mem_correct1 in HxV.
      assert (In x (sub_vars_improvable t V V f)).
      { admit. }
      apply (set_add_In string_dec) in H. rewrite H.
      assert (In x (sub_vars_improvable t (nodup string_dec V) (nodup string_dec V) f)).
      { admit. }
      apply (set_add_In string_dec) in H0. rewrite H0.
      apply IHt.
  Admitted.
        
      + assert ((negb (x € V)) = (negb (x € nodup dec V))).
        { f_equal. assert (((x € V) = true) <-> In x V).
          + destruct V; split; intros.
            * simpl in H. discriminate.
            * contradiction.
            * simpl in H. destruct (string_dec x s).
              -- subst. simpl. left. reflexivity.
              -- simpl. apply set_mem_correct1 in H.
                 right. assumption.
            * simpl in *. destruct (string_dec x s); try reflexivity.
              destruct H.
              -- subst. contradiction.
              -- apply set_mem_correct2. assumption.
          + destruct (x € V) eqn:HxV.
            * symmetry. apply set_mem_correct2. apply nodup_In.
              apply set_mem_correct1 in HxV. assumption.
            * symmetry. apply set_mem_complete2. rewrite nodup_In.
              apply set_mem_complete1 in HxV. assumption.
        }
        rewrite <- H. rewrite <- fold_right_andb_true_map_incl_iff.

        }
      + simpl. rewrite set_add_nodup. rewrite IHt. reflexivity.
   *)

  Example vars_improvable_test1 :
    vars_improvable [clause_x0y1_x2] frontier_infty = [].
  Proof. reflexivity. Qed.

  Example vars_improvable_test2 :
    vars_improvable [clause_x0y1_x2] frontier_fin_1 = [x_str].
  Proof. reflexivity. Qed.

  Example vars_improvable_test3 :
    vars_improvable [clause_x0y1_x2] frontier_fin_0 = [].
  Proof. reflexivity. Qed.

  Example vars_improvable_test4 :
    vars_improvable [clause_x0y1_x2] frontier_fin_2 = [x_str].
  Proof. reflexivity. Qed.

  Example vars_improvable_test5 :
    vars_improvable [clause_y1_y2] frontier_fin_0 = [].
  Proof. reflexivity. Qed.

End VarsImp.
