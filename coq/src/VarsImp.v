From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
Require Import Clause. Import Clause.
Require Import Atom. Import Atom.
Require Import Frontier. Import Frontier.
Require Import Sets. Import Sets. Import StringSetsNotation.
Require Import Vars. Import Vars.

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
