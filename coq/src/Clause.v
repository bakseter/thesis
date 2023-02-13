From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
Require Import Atom. Import Atom.
Require Import Frontier. Import Frontier.
Require Import Ninfty. Import Ninfty.
Require Import Misc. Import Misc.

Module Clause.

  Inductive Clause : Type :=
    | clause : set Atom -> Atom -> Clause. (* non-empty body! *)

  Notation "ps ~> c" := (clause ps c) (at level 81). (* level ?? *)

  Example clause_x1_x2 : Clause := ([atom_x1] ~> atom_x2).
  Example clause_x0_x1 : Clause := ([atom_x0] ~> atom_x1).
  Example clause_x0y1_x2 : Clause := ([atom_x0; atom_y1] ~> atom_x2).
  Example clause_y0_y1 : Clause := ([atom_y0] ~> atom_y1).
  Example clause_y1_y2 : Clause := ([atom_y1] ~> atom_y2).

  Definition conc (c : Clause) : Atom :=
    match c with
    | ps ~> c => c
    end.

  Definition conds (c : Clause) : set Atom :=
    match c with
    | ps ~> c => ps
    end.

  Definition clause_true (c : Clause) (f : Frontier) : bool :=
    match c with
    | (conds ~> conc) =>
      if fold_right andb true (map (fun a => atom_true a f) conds)
      then (atom_true conc f)
      else true
    end.

  Definition shift_clause (n : nat) (c : Clause) : Clause :=
    match c with
    | conds ~> conc =>
      (map (shift_atom n) conds) ~> (shift_atom n conc)
    end.

  Lemma shift_clause_0 (c : Clause) :
    shift_clause 0 c = c.
  Proof.
    destruct c. destruct s as [| h t]; simpl.
    - rewrite shift_atom_0. reflexivity.
    - repeat rewrite shift_atom_0. rewrite map_shift_atom_0.
      reflexivity.
  Qed.

  Lemma shift_clause_twice (c : Clause) (n m : nat) :
    shift_clause (n + m) c = shift_clause n (shift_clause m c).
  Proof.
    destruct c. simpl.
    rewrite shift_atom_twice.
    rewrite map_shift_atom_twice. reflexivity.
  Qed.

  Definition weaken_clause (c : Clause) (h : Atom) :=
    match c with
    | ps ~> c => h :: ps ~> c
    end.

  Lemma shift_weaken_commute (n : nat) (c : Clause) (h : Atom) :
    shift_clause n (weaken_clause c h) =
    weaken_clause (shift_clause n c) (shift_atom n h).
  Proof. destruct c as [ps a]. reflexivity. Qed.

  Lemma weakening_sound (c : Clause) (h : Atom) (f : Frontier) :
    clause_true c f = true -> clause_true (weaken_clause c h) f = true.
  Proof.
    intros. destruct c. simpl.
    destruct (atom_true h f); try reflexivity.
    simpl. apply H.
  Qed.

  Lemma conc_false_clause_true_shift_true (c : Clause) (f : Frontier) (n: nat) :
    atom_true (conc c) f = false ->
    clause_true c f = true ->
    clause_true (shift_clause n c) f = true.
  Proof with simpl.
    intros H H'. destruct c. simpl in H.
    induction s as [| h conds IHconds].
    - destruct a as [x k]... simpl in H, H'.
      destruct (f x) as [|n']; try reflexivity...
      rewrite H in H'. discriminate.
    - destruct a as [x k]... simpl in H, H', IHconds.
      destruct (f x) as [|n']; try apply if_true_then_true_true.
      destruct (atom_true h f) eqn:athf.
      + simpl in H', IHconds. apply IHconds in H'.
        destruct (atom_true (shift_atom n h) f)...
        * assumption.
        * reflexivity.
      + assert (atom_true (shift_atom n h) f = false).
        { apply atom_false_shift_atom_false. assumption. }
        rewrite H0... reflexivity.
  Qed.

  Lemma conc_false_clause_true_shift_true' (c : Clause) (f : Frontier) (n: nat) :
    atom_true (conc c) f = false ->
    clause_true c f = true ->
    clause_true (shift_clause n c) f = true.
  Proof.
    destruct c as [ps a]. intros na nps. simpl in na.
    destruct (clause_true (ps ~> a) f) eqn:cf; try discriminate.
    induction ps as [ | h hs].
    - simpl in cf. rewrite na in cf. discriminate.
    - destruct (atom_true h f) eqn:htf.
      + assert (W: (h :: hs ~> a) = weaken_clause (hs ~> a) h ). { reflexivity. }
      rewrite W. rewrite (shift_weaken_commute n (hs ~> a) h).
      apply weakening_sound. apply IHhs. rewrite <- cf.
      unfold clause_true. simpl. rewrite htf. reflexivity.
      + assert (hnf : atom_true (shift_atom n h) f = false).
        * apply atom_false_shift_atom_false. assumption.
        * simpl. rewrite hnf. simpl. reflexivity.
  Qed.

  Definition all_shifts_true (c : Clause) (f : Frontier) : bool :=
    match c with
    | (conds ~> conc) =>
        match conc with
        | (x & k) =>
            match f x with
            | infty => true
            | fin n => clause_true (shift_clause (n + 1 - k) c) f
            end
        end
    end.

  Example all_shifts_true_test1 :
    all_shifts_true clause_x1_x2 frontier_fin_1 = false.
  Proof. reflexivity. Qed.

  Lemma all_shifts_true_sound (c : Clause) (f : Frontier) (n : nat) :
     all_shifts_true c f = true ->
     clause_true (shift_clause n c) f = true.
  Proof with simpl.
    destruct c as [conds conc].
    destruct conc as [x k].
    unfold all_shifts_true.
    destruct (f x) as [| n'] eqn:infty_fin_n.
    - destruct n.
      + intro. clear H.
        rewrite shift_clause_0...
        rewrite infty_fin_n. apply if_true_then_true_true.
      + intro... rewrite infty_fin_n. apply if_true_then_true_true.
    - destruct (n' + 1 - k) as [| m] eqn:n'1k; intros.
      + apply conc_false_clause_true_shift_true.
        * assert (L1 : ~ k <= n'). { lia. } simpl.
          rewrite infty_fin_n. apply leb_nle. assumption.
        * rewrite shift_clause_0 in H. assumption.
      + assert (L2: n <= m \/ ~n <= m). { lia. }
        destruct L2.
        * simpl. rewrite infty_fin_n. apply if_b_then_a_or_true.
          apply leb_le. { lia. }
        * assert (L3: n = (n - S m) + S m). { lia. }
          rewrite L3. rewrite shift_clause_twice.
          apply conc_false_clause_true_shift_true.
          2: apply H. simpl. rewrite infty_fin_n. destruct n'.
          reflexivity. apply leb_nle. lia.
  Qed.

  Lemma all_shifts_true_complete (c : Clause) (f : Frontier) :
     all_shifts_true c f = false ->
     exists n, clause_true (shift_clause n c) f = false.
  Proof.
    intros. unfold clause_true. destruct c as [conds conc].
    destruct conc as [x k]. simpl in *. destruct (f x) as [|n'].
    - exists 0. rewrite if_b_then_a_or_true.
      + assumption.
      + reflexivity.
    - exists (n' + 1 - k). assumption.
  Qed.

  Definition all_shifts_dec (c : Clause) (f : Frontier):
    (forall n, clause_true (shift_clause n c) f = true) +
    sig (fun n => clause_true (shift_clause n c) f = false).
  Proof.
    destruct (all_shifts_true c f) eqn:H.
    - left. intro n. apply all_shifts_true_sound. assumption.
    - right. intros. unfold clause_true.
      destruct c as [conds conc]. destruct conc as [x k].
      simpl in *. destruct (f x) as [|n'].
      * exists 0. rewrite if_b_then_a_or_true.
        + assumption.
        + discriminate.
      * exists (n' + 1 - k). assumption.
  Defined. (* this allows one to compute, Qed does not *)

  (* the next definition is probably more useful *)

  Definition all_shifts_func (c : Clause) (f : Frontier) : unit + nat :=
    match c with conds ~> x & k =>
      match f x with
      | infty => inl tt
      | fin n => if clause_true (shift_clause (n + 1 - k) c) f
                 then inl tt else inr (n + 1 - k)
      end
    end.

  Lemma all_shifts_func_tt_sound (c : Clause) (f : Frontier) :
    all_shifts_func c f = inl tt ->
    forall n, clause_true (shift_clause n c) f = true.
  Proof.
    intros H n. destruct c as [cond [x k]].
    destruct (all_shifts_func (cond ~> x & k) f) eqn:Cases.
    - apply all_shifts_true_sound. unfold all_shifts_true.
      destruct (f x) eqn: Hfx. reflexivity.
      destruct (clause_true (shift_clause (n0 + 1 - k) (cond ~> x & k)) f)
      eqn:C.
      reflexivity. unfold all_shifts_func in Cases.
      rewrite Hfx,C in Cases. discriminate Cases.
    - discriminate H.
  Qed.

  Lemma all_shifts_func_n_sound (c : Clause) (f : Frontier) :
    forall n, all_shifts_func c f = inr n ->
    clause_true (shift_clause n c) f = false.
  Proof.
    intros n H. destruct c as [conds [x k]].
    unfold all_shifts_func in H.
    destruct (f x) as [|n'] eqn:Hfx in H; try discriminate.
    destruct (clause_true (shift_clause (n' + 1 - k) (conds ~> x & k)) f) eqn:CT.
    - discriminate H.
    - inversion H. assumption.
  Qed.

End Clause.
