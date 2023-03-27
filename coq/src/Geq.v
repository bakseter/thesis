From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Minus.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Frontier. Import Frontier.
Require Import Clause. Import Clause.
Require Import Ninfty. Import Ninfty.
Require Import Sets. Import StringSetsNotation.
Require Import Atom. Import Atom.
Require Import Vars. Import Vars.
Require Import Model. Import Model.
Require Import VarsImp. Import VarsImp.

Module Geq.

  Fixpoint geq (V : set string) (g f : Frontier) : bool :=
    match V with
    | []      => true
    | h :: t  =>
      match g h with
      | infty => geq t g f
      | fin n =>
          match f h with
          | infty => false
          | fin k => (k <=? n) && geq t g f
          end
      end
    end.

  Lemma geq_infty (V : set string) (f : Frontier) :
    geq V frontier_infty f = true.
  Proof.
    induction V as [|h t]; try reflexivity.
    simpl. assumption.
  Qed.

  Lemma geq_refl (V : set string) (f : Frontier) :
    geq V f f = true.
  Proof.
    induction V as [|h t]; try reflexivity.
    simpl. destruct (f h); try assumption.
    assert (n <=? n = true). { apply leb_le. lia. }
    rewrite H. simpl. assumption.
  Qed.

  Lemma f_is_f (h : string) (t : set string) (f : Frontier) :
    f h = infty ->
    (fun v : string =>
      if
        if string_dec v h
        then true
        else v € t
      then Sinfty (f v)
      else f v) =
    (fun v : string =>
      if v € t
      then Sinfty (f v)
      else f v).
  Proof.
    intros. apply functional_extensionality. intros.
    destruct (string_dec x h) eqn:Hxh; try reflexivity.
    destruct (x € t) eqn:Hxt; try reflexivity.
    assert (f x = infty). { rewrite e. assumption. }
    rewrite e. rewrite H. reflexivity.
  Qed.

  Lemma geq_bool (h : string) (t : set string) (f g : Frontier) :
    (forall v, (v € (h :: t)) = true -> ninfty_geq (f v) (g v) = true)
      <-> geq (h :: t) f g = true.
  Proof.
    split; induction (h :: t); try auto; try discriminate.
    - intros. simpl. destruct (f a) eqn:Hfa; destruct (g a) eqn:Hga;
      try apply IHl; try intros; try apply H; try simpl;
      try destruct (string_dec v a); try reflexivity;
      try assumption.
      + destruct (H a). simpl. destruct (string_dec a a).
        reflexivity. contradiction. rewrite Hfa. rewrite Hga.
        simpl. reflexivity.
      + apply andb_true_iff. split.
        * destruct (H a). simpl. destruct (string_dec a a).
          reflexivity. contradiction. rewrite Hfa. rewrite Hga.
          reflexivity.
        * apply IHl. intros. apply H. simpl.
          destruct (string_dec v a); try reflexivity.
          assumption.
    - intros. destruct (f v) eqn:Hfv; destruct (g v) eqn:Hgv;
      try reflexivity.
      + rewrite <- Hfv. rewrite <- Hgv.  apply IHl.
        * simpl in H. destruct (f a); destruct (g a);
          try assumption; try discriminate.
          apply andb_true_iff in H. apply H.
        * apply set_mem_correct1 in H0. simpl in H0.
          destruct H0.
          -- simpl in H. rewrite <- H0 in Hfv, Hgv.
             rewrite Hfv in H. rewrite Hgv in H. discriminate.
          -- apply set_mem_correct2. assumption.
      + simpl in H. apply set_mem_correct1 in H0. simpl in H0.
        destruct H0.
        * rewrite <- H0 in Hfv, Hgv.
          rewrite Hfv in H. rewrite Hgv in H.
          simpl. apply andb_true_iff in H. apply H.
        * rewrite <- Hfv. rewrite <- Hgv. apply IHl.
          destruct (f a); destruct (g a); try assumption.
          -- discriminate.
          -- apply andb_true_iff in H. apply H.
          -- apply set_mem_correct2. assumption.
  Qed.

  Lemma incl_frontier_nodup (V : set string) (f : Frontier) :
    incl (map f (nodup string_dec V)) (map f V).
  Proof.
    induction V as [|h t].
    - simpl. apply incl_refl.
    - simpl. destruct (in_dec string_dec).
      + apply incl_tl. assumption.
      + simpl. apply incl_cons.
        * simpl. left. reflexivity.
        * apply incl_tl. assumption.
  Qed.

  Lemma geq_nodup_true (V : set string) (f g : Frontier) :
    geq V g f = true -> geq (nodup string_dec V) g f = true.
  Proof.
    induction V as [|h t]; try reflexivity.
    intros. simpl. destruct (in_dec string_dec h t).
    - apply IHt. simpl in H. destruct (g h) eqn:Hgh.
      + assumption.
      + destruct (f h) eqn:Hfh.
        * discriminate.
        * apply andb_true_iff in H. apply H.
    - unfold geq. fold geq. destruct (g h) eqn:Hgh.
      + apply IHt. simpl in H. rewrite Hgh in H.
        assumption.
      + destruct (f h) eqn:Hfh.
        * simpl in H. rewrite Hgh in H. rewrite Hfh in H.
          discriminate.
        * simpl in H. rewrite Hgh in H. rewrite Hfh in H.
          apply andb_true_iff in H. apply andb_true_iff. split.
          -- apply H.
          -- apply IHt. apply H.
  Qed.

  Lemma geq_In (x : string) (t : set string) (f g : Frontier) :
    In x t -> geq t g f = true -> ninfty_geq (g x) (f x) = true.
  Proof.
    intros. induction t as [|h t].
    - contradiction.
    - destruct H.
      + subst. simpl in H0. destruct (g x) eqn:Hgx.
        -- simpl. reflexivity.
        -- simpl. destruct (f x) eqn:Hfx.
           * discriminate.
           * apply andb_true_iff in H0. apply H0.
      + simpl in H0. destruct (g h) eqn:Hgh.
        -- apply IHt in H; assumption.
        -- destruct (f h) eqn:Hfh.
           * discriminate.
           * apply andb_true_iff in H0. apply IHt in H.
             assumption. apply H0.
  Qed.

  Lemma geq_nodup_true_iff (V : set string) (f g : Frontier) :
    geq V g f = true <-> geq (nodup string_dec V) g f = true.
  Proof.
    split; try apply geq_nodup_true.
    generalize dependent f. generalize dependent g.
    induction V as [|h t]; try reflexivity. intros.
    simpl in H. destruct (in_dec string_dec h t).
    - unfold geq. fold geq. destruct (g h) eqn:Hgh.
      + apply IHt in H. assumption.
      + destruct (f h) eqn:Hfh.
        * rewrite <- (nodup_In string_dec) in i.
          apply (geq_In h (nodup string_dec t) f g) in i.
          -- rewrite Hgh in i. rewrite Hfh in i. simpl in i.
             discriminate.
          -- assumption.
        * apply IHt in H. apply andb_true_iff. split.
          -- apply (geq_In h t f g) in i.
             ++ rewrite Hgh in i. rewrite Hfh in i. simpl in i.
                assumption.
             ++ assumption.
          -- assumption.
    - unfold geq. fold geq. destruct (g h) eqn:Hgh.
      + apply IHt. simpl in H. rewrite Hgh in H.
        assumption.
      + simpl in H. rewrite Hgh in H. destruct (f h).
        * discriminate.
        * apply andb_true_iff in H. destruct H. apply IHt in H0.
          apply andb_true_iff. split; assumption.
  Qed.

  Lemma geq_incl (V W : set string) (f g : Frontier) :
    incl V W -> geq W g f = true -> geq V g f = true.
  Proof.
    intros. induction V as [|h t]; try reflexivity.
    unfold geq. fold geq. apply incl_cons_inv in H.
    destruct H. destruct (g h) eqn:Hfh.
    - apply IHt in H1. assumption.
    - destruct (f h) eqn:Hgh.
      + apply (geq_In h W f g) in H; try assumption.
        rewrite Hfh in H. rewrite Hgh in H. simpl in H.
        discriminate.
      + apply (geq_In h W f g) in H; try assumption.
        rewrite Hfh in H. rewrite Hgh in H. simpl in H.
        apply andb_true_iff. apply IHt in H1. split; assumption.
  Qed.

  Lemma ninfty_geq_refl (n : Ninfty) :
    ninfty_geq n n = true.
  Proof. destruct n. reflexivity. simpl. apply leb_refl. Qed.

  Lemma ninfty_geq_Sinfty (n : Ninfty) :
    ninfty_geq (Sinfty n) n = true.
  Proof. destruct n. reflexivity. simpl. apply leb_le. lia. Qed.

  Lemma geq_Sinfty_f (h : string) (t : set string) (f : Frontier) :
    geq t
    (fun v : string =>
     if
      if string_dec v h
      then true
      else v € t
     then Sinfty (f v)
     else f v)
    (fun v : string => if v € t then Sinfty (f v) else f v)
    = true.
  Proof.
    destruct t as [| h' t]; try reflexivity.
    apply geq_bool. intros. simpl. destruct (string_dec v h);
    destruct (string_dec v h'); try apply ninfty_geq_refl;
    destruct (v € t); try apply ninfty_geq_refl.
    apply ninfty_geq_Sinfty.
  Qed.

  Lemma geq_Sinfty_f2 (Cs : set Clause) (t : set string) (f: Frontier) :
    geq
      t
      (fun v : string => if v € sub_vars_improvable Cs t t f then Sinfty (f v) else f v)
      f
    = true.
  Proof.
    destruct t as [| h t]; try reflexivity.
    apply geq_bool. intros. simpl. destruct (v € sub_vars_improvable Cs (h :: t) (h :: t) f); try apply ninfty_geq_refl.
    apply ninfty_geq_Sinfty.
  Qed.

  Lemma geq_trans (t : set string) (f g h : Frontier) :
    geq t f g = true -> geq t g h = true -> geq t f h = true.
  Proof.
    intros. induction t as [| h' t]; try reflexivity.
    simpl in *. destruct (f h') eqn:Hfh'; destruct (g h') eqn:Hgh';
    destruct (h h') eqn:Hhh'; try apply IHt; try assumption;
    try discriminate.
    - apply andb_true_iff in H0. destruct H0.
      assumption.
    - apply andb_true_iff. apply andb_true_iff in H, H0.
      destruct H, H0. split.
      + apply leb_le. apply leb_le in H, H0. lia.
      + apply IHt; assumption.
  Qed.

  Lemma geq_conditional_infty_true (V : set string) (f : Frontier) :
    forall b : bool,
      geq V (fun x : string => if b then infty else f x) f = true.
  Proof.
    destruct b.
    - induction V as [|h t]; try reflexivity.
      simpl. assumption.
    - induction V as [|h t]; try reflexivity.
      simpl. destruct (f h) eqn:Hfh; try assumption.
      apply andb_true_iff. split.
      + apply leb_refl.
      + assumption.
  Qed.

  (* NEEDED *)
  Lemma geq_update_infty_V (V : set string) (f : Frontier) :
    geq V (update_infty_V V f) f = true.
  Proof.
    induction V as [| h t]; try reflexivity.
    unfold geq. fold geq.
    destruct (update_infty_V (h :: t) f h) eqn:HuiV.
    - unfold update_infty_V in *. simpl in HuiV.
      erewrite <- (geq_conditional_infty_true t f (_ € h :: t)).
      f_equal. apply functional_extensionality. intros.
      simpl. instantiate (1 := h). destruct (string_dec x h).
      destruct (string_dec h h); try reflexivity; try contradiction.
      destruct (string_dec h h); try reflexivity; try contradiction.
      destruct (x € t) eqn:HxT; try reflexivity.
      erewrite <- (geq_conditional_infty_true t f (x € t)) in IHt.
      simpl. admit.
    - destruct (f h) eqn:Hfh.
      + unfold update_infty_V in HuiV. simpl in HuiV.
        destruct (string_dec h h). discriminate.
        contradiction.
      + apply andb_true_iff. split.
        * unfold update_infty_V in HuiV. simpl in HuiV.
          destruct (string_dec h h). discriminate.
          contradiction.
        * unfold update_infty_V in HuiV. simpl in HuiV.
          destruct (string_dec h h). discriminate.
          contradiction.
  Admitted.

  Example geq_test1 :
    geq [x_str] (frontier_fin_1) (frontier_infty) = false.
  Proof. reflexivity. Qed.

  Example geq_test2 :
    geq [x_str] (frontier_fin_2) (frontier_fin_1) = true.
  Proof. reflexivity. Qed.

  Example geq_test3 :
    geq [x_str] (frontier_infty) (frontier_fin_2) = true.
  Proof. reflexivity. Qed.

  Example geq_test4 :
    geq [x_str] (frontier_fin_1) (frontier_fin_2) = false.
  Proof. reflexivity. Qed.

  Example geq_test5 :
    geq [] (frontier_fin_1) (frontier_fin_2) = true.
  Proof. reflexivity. Qed.

  Example geq_test6 :
    geq [x_str] (frontier_infty) (frontier_infty) = true.
  Proof. reflexivity. Qed.

  Example geq_test7 :
    geq
      (vars [clause_x1_x2])
      frontier_fin_1
      frontier_fin_0
    = true.
  Proof. reflexivity. Qed.

  Example geq_test8 :
    geq
      (vars [clause_x1_x2])
      frontier_fin_2
      frontier_fin_2
    = true.
  Proof. reflexivity. Qed.

  Example geq_test9 :
    geq
      (vars [clause_x1_x2])
      frontier_fin_0
      frontier_fin_1
    = false.
  Proof. reflexivity. Qed.

  Example geq_test10 :
    geq
      (vars [clause_x1_x2])
      frontier_infty
      frontier_fin_1
    = true.
  Proof. reflexivity. Qed.

  Example geq_test11 :
    geq
      (vars [clause_x1_x2])
      frontier_fin_1
      frontier_infty
    = false.
  Proof. reflexivity. Qed.

  Definition ex_lfp_geq_P (Cs : set Clause) (V W : set string) (f : Frontier) : Prop :=
    exists g : Frontier, geq V g f = true /\ sub_model Cs V W g = true.

  Definition ex_lfp_geq_T (Cs : set Clause) (V W : set string) (f : Frontier) : Type :=
    sig (fun g : Frontier => prod (geq V g f = true) (sub_model Cs V W g = true)).

  (* we can also use Set, this def. is equivalent to the def. above *)
  Definition ex_lfp_geq_S (Cs : set Clause) (V W : set string) (f : Frontier) : Set :=
    sig (fun g : Frontier => prod (geq V g f = true) (sub_model Cs V W g = true)).

  Definition ex_lfp_geq := ex_lfp_geq_S.

  Lemma ex_lfp_geq_incl (Cs : set Clause) (V W : set string) :
    incl V W ->
    forall f,
      ex_lfp_geq Cs W W f ->
      ex_lfp_geq Cs V V f.
  Proof.
    intros. unfold ex_lfp_geq in *.
    destruct H0 as [g [Hg1 Hg2]].
    exists g. split.
    - apply geq_incl with W; assumption.
    - apply (sub_model_monotone Cs g V W V W); assumption.
  Qed.

  Lemma ex_lfp_geq_monotone (Cs : set Clause) (V : set string) (f g : Frontier) :
    ex_lfp_geq Cs V V f ->
    geq V f g = true ->
    ex_lfp_geq Cs V V g.
  Proof.
    intros. unfold ex_lfp_geq in H.
    destruct H as [x [H1 H2]].
    unfold ex_lfp_geq. exists x. split;
    try assumption. eapply geq_trans.
    apply H1. assumption.
  Qed.

  Lemma ex_lfp_geq_empty (Cs : set Clause) (f : Frontier) :
    ex_lfp_geq Cs [] [] f.
  Proof.
    unfold ex_lfp_geq. exists f. split; try reflexivity.
    induction Cs; try reflexivity.
    simpl. destruct a. destruct a. assumption.
  Qed.

  Lemma ex_lfp_geq_nodup_iff (Cs : set Clause) (V : set string) (f : Frontier) :
    let A := ex_lfp_geq Cs V V f in
    let B := ex_lfp_geq Cs (nodup string_dec V) (nodup string_dec V) f in
    prod (A -> B) (B -> A).
  Proof.
    split; intros.
    - unfold ex_lfp_geq in *. elim H. intros. destruct p.
      exists x. split.
      + rewrite <- geq_nodup_true_iff. assumption.
      + rewrite <- sub_model_nodup. assumption.
    - unfold ex_lfp_geq in *. elim H. intros. destruct p.
      exists x. split.
      + rewrite geq_nodup_true_iff. assumption.
      + rewrite sub_model_nodup. assumption.
  Qed.

End Geq.
