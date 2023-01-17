From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Minus.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
Require Import Sets. Import Sets. Import StringSetsNotation.
Require Import Clause. Import Clause.
Require Import Atom. Import Atom.
Require Import Frontier. Import Frontier.
Require Import Vars. Import Vars.
Require Import VarsImp. Import VarsImp.
Require Import Misc. Import Misc.
Require Import Ninfty. Import Ninfty.
Require Import Geq. Import Geq.
Require Import Model. Import Model.

Module Forward.

  Definition sub_forward (Cs : set Clause) (V W : set string) (f : Frontier) : set string * Frontier :=
    let X := sub_vars_improvable Cs V W f in
    let f' := fun v => if v € X then Sinfty (f v) else f v
    in (X, f').

  Definition forward (Cs : set Clause) (f : Frontier) : set string * Frontier :=
    sub_forward Cs (vars Cs) (vars Cs) f.

  Lemma sub_forward_geq (Cs : set Clause) (V W : set string) (f : Frontier) :
    let (X, g) := sub_forward Cs V W f in
    geq X g f = true.
  Proof.
    simpl. induction (sub_vars_improvable Cs V W f) as [|h t];
    try reflexivity. destruct (f h) as [| k] eqn:Hfh.
    - simpl. destruct (string_dec h h) eqn:Hdec.
      destruct (Sinfty (f h)) eqn:Hsinfty.
      + simpl. rewrite f_is_f; assumption.
      + rewrite Hfh. rewrite Hfh in Hsinfty.
        unfold Sinfty in Hsinfty. discriminate.
      + contradiction.
    - unfold geq. rewrite Hfh. destruct (h € h :: t); unfold Sinfty; simpl; fold geq;
      apply andb_true_intro; split; try apply leb_le; try lia;
      eapply geq_trans with (fun v : string => if v € t then Sinfty (f v) else f v);
      try apply geq_Sinfty_f; try assumption.
  Qed.

  Lemma sub_forward_cons_empty (a : Clause) (Cs : set Clause) (V W : set string) (f g : Frontier) :
    sub_forward (a :: Cs) V W f = ([], g) ->
    sub_forward Cs V W f = ([], g).
  Proof.
    intros. unfold sub_forward in H.
    assert ((sub_vars_improvable (a :: Cs) V W f,
       fun v : string =>
       if v € sub_vars_improvable (a :: Cs) V W f then Sinfty (f v) else f v) = (
      [], g)) by assumption.
    apply tuple_fst in H.
    unfold sub_forward.
    assert (sub_vars_improvable (a :: Cs) V W f = []) by assumption.
    apply sub_vars_improvable_cons_empty in H. rewrite H. simpl.
    apply tuple_snd in H0. rewrite H1 in H0. simpl in H0.
    rewrite H0. reflexivity.
  Qed.

  Lemma sub_forward_empty (Cs : set Clause) (V W : set string) (f g : Frontier) :
    sub_forward Cs V W f = ([], g) -> f = g /\
    sub_model Cs V W f = true.
  Proof.
    split; inversion H.
    - rewrite H1. simpl. apply frontier_lambda.
    - rewrite H1 in H2. simpl in H2. induction Cs; try reflexivity.
      assert (H3: sub_vars_improvable (a :: Cs) V W f = []) by assumption.
      apply sub_vars_improvable_cons_empty in H3.
      unfold sub_model. fold sub_model. destruct a as [l [x k]].
      apply andb_true_iff. split.
      + unfold sub_vars_improvable in H1. fold sub_vars_improvable in H1.
        destruct (all_shifts_true (l ~> x & k) f).
        * apply orb_true_r.
        * rewrite orb_false_r in H1. destruct (negb (x € W));
          try reflexivity. simpl in *. rewrite orb_false_r.
           destruct (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l))));
           try reflexivity. apply set_add_not_empty in H1. contradiction.
      + eapply IHCs.
        * apply (sub_forward_cons_empty (l ~> x & k)). assumption.
        * apply sub_vars_improvable_cons_empty in H1. assumption.
  Qed.

  Lemma sub_forward_incl (Cs : set Clause) (f g : Frontier) (V W U: set string) :
    sub_forward Cs V W f = (U, g) -> incl U W.
  Proof. intros. inversion H. apply sub_vars_improvable_incl_W. Qed.

  Example forward_test1 :
    forward [clause_x0y1_x2] frontier_infty = ([], frontier_infty).
  Proof. reflexivity. Qed.

  Example forward_test2 :
    forward [clause_x0y1_x2] frontier_fin_1 =
    ([x_str], fun v => if v € [x_str] then fin 2 else fin 1).
  Proof. reflexivity. Qed.

  Example forward_test3 :
    forward [clause_x0y1_x2] frontier_fin_0 = ([], frontier_fin_0).
  Proof. reflexivity. Qed.

  Example forward_test4 :
    forward [clause_x0y1_x2] frontier_fin_2 =
    ([x_str], fun v => if v € [x_str] then fin 3 else fin 2).
  Proof. reflexivity. Qed.

  Example forward_test5 :
    forward [clause_x0y1_x2; clause_y1_y2] frontier_fin_0 =
    ([], frontier_fin_0).
  Proof. reflexivity. Qed.

  Example forward_test6 :
    forward [clause_x0y1_x2; clause_y1_y2] frontier_fin_1 =
    ([y_str; x_str], fun v => if v € [y_str; x_str] then fin 2 else fin 1).
  Proof. reflexivity. Qed.

End Forward.
