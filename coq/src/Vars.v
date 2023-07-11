From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
Require Import Atom. Import Atom.
Require Import Clause. Import Clause.
Require Import Frontier. Import Frontier.
Require Import Ninfty. Import Ninfty.
Require Import Misc. Import Misc.
Require Import Sets. Import Sets.

Module Vars.

  Fixpoint vars_set_atom (s : set Atom) : set string :=
    match s with
    | []       => []
    | ((x & _) :: t) =>
        let cl := vars_set_atom t in
        set_add string_dec x cl
    end.

  Lemma vars_set_atom_cons (x : string) (t : set Atom) (k : nat) (W : set string) :
    incl (vars_set_atom ((x & k) :: t)) W ->
    incl (vars_set_atom t) W.
  Proof.
    intros. induction t as [|h t']; try apply incl_nil_l.
    destruct h as [y k']. simpl in *.
    apply incl_set_add_reduce in H. assumption.
  Qed.

  Lemma incl_vars_set_atom_In (s : set Atom) (W : set string) (x : string) (k : nat) :
    incl (vars_set_atom ((x & k) :: s)) W ->
    In x W.
  Proof.
    intros. induction W as [|h t].
    - eapply incl_l_nil_false in H; try contradiction.
      simpl. apply set_add_not_empty.
    - destruct s as [|h' t']; apply H; simpl; auto.
      destruct h'. apply set_add_intro2. reflexivity.
  Qed.

  Lemma vars_set_atom_incl_fold (s : set Atom) (W : set string) :
    incl (vars_set_atom s) W ->
    (fold_right andb true (map (fun x : string => set_mem string_dec x W) (vars_set_atom s))) = true.
  Proof.
    intros. induction s as [|h t]; try reflexivity.
    simpl. destruct h as [x k] eqn:Hxk.
    - destruct (set_mem string_dec x (vars_set_atom t)) eqn:Ht.
      + apply vars_set_atom_cons in H. apply IHt in H.
        apply (set_add_mem_true string_dec) in Ht.
        rewrite Ht. assumption.
      + apply set_add_mem_false in Ht. rewrite Ht.
        assert (H': incl (vars_set_atom ((x & k) :: t)) W) by assumption.
        apply vars_set_atom_cons in H. apply IHt in H. rewrite map_app.
        assert (map (fun x0: string => set_mem string_dec x0 W) [x] = [set_mem string_dec x W]) by reflexivity.
        rewrite H0. rewrite fold_right_app. simpl. rewrite andb_true_intro.
        * assumption.
        * split; try reflexivity.
          apply set_mem_correct2. apply incl_vars_set_atom_In in H'.
          assumption.
  Qed.

  Example vars_set_atom_test1 :
    vars_set_atom [atom_x0; atom_y1] = [y_str; x_str].
  Proof. reflexivity. Qed.

  Example vars_set_atom_test2 :
    vars_set_atom [atom_x0; atom_y1; atom_x1] = [x_str; y_str].
  Proof. reflexivity. Qed.

  Example vars_set_atom_test3 :
    vars_set_atom [atom_x0; atom_y1; atom_x1] = [x_str; y_str].
  Proof. reflexivity. Qed.

  Definition vars_clause (c : Clause) : set string :=
    match c with
    | conds ~> (x & k) =>
        set_add string_dec x (vars_set_atom conds)
    end.

  Lemma vars_clause_In_conc (s : set Atom) (x : string) (k : nat) :
    In x (vars_clause (s ~> (x & k))).
  Proof.
    unfold vars_clause. destruct s as [| [y k'] s'].
    - left. reflexivity.
    - apply set_add_intro2. reflexivity.
  Qed.

  Lemma vars_clause_incl_In (s : set Atom) (x : string) (k : nat) (W : set string) :
    incl (vars_clause (s ~> (x & k))) W ->
    In x W.
  Proof.
    intros. induction W as [|h t];
    apply H; apply vars_clause_In_conc.
  Qed.

  Lemma vars_clause_incl_vars_set_atom (s : set Atom) (W : set string) (x : string) (k : nat) :
    incl (vars_clause (s ~> (x & k))) W ->
    incl (vars_set_atom s) W.
  Proof.
    intros. destruct s as [|h t]; try apply incl_nil_l.
    simpl in *. destruct h as [y m].
    apply incl_set_add_reduce in H.
    assumption.
  Qed.

  Example vars_clause_test1 :
    vars_clause clause_x1_x2 = vars_clause clause_x0_x1.
  Proof. reflexivity. Qed.

  Example vars_clause_test2 :
    vars_clause clause_x0y1_x2 <> vars_clause clause_x0_x1.
  Proof. discriminate. Qed.

  Definition vars (Cs : set Clause) : set string :=
    flat_map vars_clause Cs.

  Lemma vars_cons (c : Clause) (Cs : set Clause) :
    vars (c :: Cs) = vars_clause c ++ vars Cs.
  Proof. unfold vars. reflexivity. Qed.

  Example vars_test1 :
    vars [clause_x0y1_x2; clause_x0_x1] = [y_str; x_str; x_str].
  Proof. simpl. reflexivity. Qed.

  Example vars_test2 :
    vars [clause_x0y1_x2; clause_x0_x1] <> [x_str; y_str; z_str].
  Proof. discriminate. Qed.

  Example vars_test3 :
    vars [clause_x0y1_x2; clause_x0_x1] = [y_str; x_str; x_str].
  Proof. reflexivity. Qed.

End Vars.
