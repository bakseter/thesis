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

Definition pre_thm (n m : nat) (Cs : set Clause) (V W : set string) (f : Frontier) : Set :=
  incl W V ->
  Datatypes.length (nodup string_dec V) <= n ->
  Datatypes.length
    (set_diff string_dec
      (nodup string_dec V)
      (nodup string_dec W)) <= m <= n ->
  ex_lfp_geq Cs (nodup string_dec W) (nodup string_dec W) f ->
  ex_lfp_geq Cs (nodup string_dec V) (nodup string_dec V) f.

Definition ex_v_V_infty (V : set string) (f : Frontier) : Set :=
  sig (fun v : string => In v V /\ f v = infty).

Lemma ex_v_V_infty_dec (V : set string) (f : Frontier) :
  (ex_v_V_infty V f) + (ex_v_V_infty V f -> False).
Proof.
  unfold ex_v_V_infty. induction V as [|h t].
  - right. unfold not. intros.
    destruct H. destruct a. inversion H.
  - destruct IHt.
    + left. destruct s. exists x. destruct a. split.
      * right. assumption.
      * assumption.
    + destruct (f h) eqn:Hh.
      * left. exists h. split;
        try assumption.
        left. reflexivity.
      * right. unfold not. intros. destruct H. destruct a.
         inversion H.
         -- subst. rewrite Hh in H0. discriminate.
         -- apply f0. exists x. destruct H. split;
            assumption. split; assumption.
Qed.

Fixpoint elim_atoms (l : set Atom) (v : string) :=
  match l with
  | [] => []
  | h :: t =>
      match h with
      | x & k =>
          if string_dec x v
          then elim_atoms t v
          else h :: elim_atoms t v
      end
  end.

Lemma elim_atoms_incl_vars_set_atom (l : set Atom) (v : string) :
  incl (vars_set_atom (elim_atoms l v)) (vars_set_atom l).
Proof.
  induction l as [|h t]; simpl; try apply incl_refl.
  destruct h. destruct (string_dec s v).
  - apply incl_set_add_reduce2. assumption.
  - simpl. apply incl_set_add_reduce3.
    apply incl_set_add_reduce2. assumption.
Qed.

Lemma elim_atoms_incl_V (l : set Atom) (v : string) :
  In v (vars_set_atom l) ->
  Datatypes.length (vars_set_atom (elim_atoms l v)) (vars_set_atom l).
Proof.
  induction l as [|h t]; intros; simpl in *; try contradiction.
  destruct h. destruct (string_dec s v).
  - subst. unfold strict_subset. split.
    + apply incl_set_add_reduce2.
      apply elim_atoms_incl_vars_set_atom.
    + unfold not. intros.
  - simpl. apply incl_set_add_reduce3.
      apply incl_set_add_reduce2. assumption.


Fixpoint elim_clauses (Cs : set Clause) (v : string) :=
  match Cs with
  | [] => []
  | (conds ~> conc) :: t =>
      match conc with
      | x & k =>
          if string_dec x v
          then elim_clauses t v
          else (elim_atoms conds v ~> conc) :: elim_clauses t v
      end
  end.

Open Scope string_scope.

Example V := ["d"; "e"; "f"].
Example l := ["a" & 0; "b" & 1; "c" & 0].
Compute elim_atoms l "a".

Example Cs := [["a" & 0] ~> "b" & 1; ["b" & 0] ~> "c" & 0; ["c" & 1] ~> "a" & 1].
Compute elim_clauses Cs "d".
Compute elim_clauses Cs "e".
Compute vars (elim_clauses Cs "d").
Compute vars (elim_clauses Cs "e").

Lemma elim_clauses_incl_vars (Cs : set Clause) (v : string) :
  incl (vars (elim_clauses Cs v)) (vars Cs).
Proof.
  induction Cs as [|c Cs]; simpl; try apply incl_refl.
  destruct c as [conds conc]. destruct conc as [x k].
  destruct (string_dec x v).
  - subst. unfold vars in *. rewrite nodup_incl.
    rewrite <- nodup_incl2. rewrite nodup_incl in IHCs.
    rewrite <- nodup_incl2 in IHCs. simpl.
    apply incl_appr. assumption.
  - unfold vars in *. rewrite nodup_incl.
    rewrite <- nodup_incl2. rewrite nodup_incl in IHCs.
    rewrite <- nodup_incl2 in IHCs. simpl.
    apply incl_app_app; try assumption.
    apply incl_set_add_reduce3. apply incl_set_add_reduce2.
    apply elim_atoms_incl_vars_set_atom.
Qed.


Definition elim_clauses_V (Cs : set Clause) (v : string) :
  (set Clause) * (set string) :=
    let Cs' := elim_clauses Cs v in
    let V' := vars Cs' in
    (Cs', V').

Lemma exists_In_cons {A : Type} (V : set A) :
  (exists v, In v V) <-> V <> [].
Proof.
  split.
  - intros. elim H. intros. unfold not.
    intros. subst. inversion H0.
  - intros. destruct V.
    + contradiction.
    + exists a. left. reflexivity.
Qed.

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
  intros. destruct (ex_v_V_infty_dec V f);
  unfold ex_v_V_infty in *; unfold pre_thm in X.
  - elim e. intros.
    destruct (elim_clauses_V Cs x) as [Cs' V'] eqn:Helim.
    assert (ex_lfp_geq Cs' (nodup string_dec V') (nodup string_dec V') f).
    {
      apply (X Cs' V' [] f 0).
      + apply incl_nil_l.
      + simpl. rewrite sub_1_r.
        apply lt_le_pred. apply strict_subset_lt_length.
        unfold strict_subset. inversion Helim. split.
        * apply elim_clauses_incl_V. admit.
        * apply V_not_incl_elim_clauses.
          admit.
      + simpl. apply conj; try lia. rewrite set_diff_nil.
        apply le_0_r. apply length_zero_iff_nil.
        induction V' as [|h' t']; try reflexivity.
        simpl. destruct (in_dec string_dec h' t').
        * apply IHt'. inversion Helim. apply tuple_destruct.
          -- reflexivity.
          -- admit.
        * admit.
      + simpl. apply ex_lfp_geq_empty.
    }
Admitted.

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
          destruct
            (sub_forward
              Cs
              (nodup string_dec V)
              (nodup string_dec V)
              h) as [U h'] eqn:Hforward.
          assert (H6 := Hforward).
          assert (H7 := Hforward).
          rewrite nodup_rm in H9.
          apply
            (sub_forward_incl_set_diff
              Cs
              h
              h'
              (nodup string_dec V)
              (nodup string_dec W)
              U) in H9;
          try apply Hforward.
          inversion Hforward. apply sub_forward_incl in Hforward.
          destruct U as [|u U'] eqn:Hu.
          -- apply sub_forward_empty in H7.
             destruct H7. unfold ex_lfp_geq. exists h.
             split; assumption.
          -- destruct
              (incl_dec
                string_dec
                V
                (nodup
                  string_dec
                  (set_union string_dec (nodup string_dec W) U))).
             ++ unfold ex_lfp_geq. exists (update_infty_V V f). split.
                ** apply geq_nodup_true. apply geq_update_infty_V.
                ** rewrite <- sub_model_nodup. apply sub_model_update_infty_V.
             ++ assert (incl (nodup string_dec (set_union string_dec W U)) V).
                {
                  apply nodup_incl2. eapply incl_set_union_trans.
                  assumption. apply nodup_incl in Hforward.
                  rewrite Hu. assumption.
                }
                assert
                  (Datatypes.length
                    (nodup string_dec (set_union string_dec W U)) <
                  Datatypes.length
                    (nodup string_dec V)).
                {
                  assert (Datatypes.length
                    (nodup string_dec (set_union string_dec W U)) <=
                      Datatypes.length
                        (nodup string_dec V)).
                  {
                    eapply NoDup_incl_length. apply NoDup_nodup.
                    apply nodup_incl. assumption.
                  }
                  apply le_lt_eq_dec in H13. destruct H13; try assumption.
                  assert
                    (strict_subset
                      (nodup string_dec (set_union string_dec W U))
                      (nodup string_dec V)).
                  {
                    unfold strict_subset. split.
                    - apply nodup_incl. assumption.
                    - unfold not. intros. apply n0.
                      apply nodup_incl2 in H13.
                      assert
                        (incl
                          (nodup string_dec (set_union string_dec W U))
                          (nodup string_dec V)).
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
                assert
                  (Datatypes.length
                    (set_diff string_dec V (set_union string_dec (nodup string_dec W) U)) <
                  Datatypes.length
                    (set_diff string_dec V (nodup string_dec W)) <= S m).
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
                       assert
                         (Datatypes.length
                           (set_diff
                              string_dec
                              (nodup string_dec (set_union string_dec W U))
                              []) <=
                         Datatypes.length
                           (nodup string_dec (set_union string_dec W U))).
                       apply (set_diff_nil_length string_dec).
                       eapply le_trans.
                       rewrite set_diff_nodup_eq. apply H15.
                       apply lt_le_pred in H13.
                       eapply le_trans. apply H13.
                       assert
                        (Datatypes.length (nodup string_dec V) <=
                         Datatypes.length V).
                       {
                          apply NoDup_incl_length. apply NoDup_nodup.
                          apply nodup_incl2. apply incl_refl.
                       }
                       assert
                        (pred (Datatypes.length (nodup string_dec V)) <=
                         pred (Datatypes.length V)).
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
