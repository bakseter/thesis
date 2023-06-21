From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
Require Import Misc. Import Misc.

(* Set-related lemmas and definitions *)

Module StringSetsNotation.

  Notation "s € S" := (set_mem string_dec s S) (at level 80).

End StringSetsNotation.

Module Sets.

  Lemma nodup_rm (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (l : set A) :
    nodup dec (nodup dec l) = nodup dec l.
  Proof.
    assert (NoDup (nodup dec l)) by apply NoDup_nodup.
    apply (nodup_fixed_point dec). assumption.
  Qed.

  Lemma set_diff_NoDup {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W U : set A) :
    NoDup (set_diff dec V W).
  Proof.
    induction V as [|h t]; try apply NoDup_nil.
    simpl. destruct (set_mem dec h W) eqn:Hmem; try assumption.
    apply set_add_nodup. assumption.
  Qed.

  Lemma set_add_mem_true {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (t : set A) (h : A) :
    set_mem dec h t = true -> set_add dec h t = t.
  Proof.
    intros. induction t; simpl in H; try discriminate.
    destruct (dec h a) eqn:Hdec; simpl.
    - rewrite e. rewrite e in Hdec. rewrite Hdec.
      reflexivity.
    - rewrite Hdec. apply IHt in H. rewrite H.
      reflexivity.
  Qed.

  Lemma set_add_mem_false {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (t : set A) (h : A) :
    set_mem dec h t = false -> set_add dec h t = t ++ [h].
  Proof.
    intros.
    induction t as [|h' t']; try reflexivity.
    simpl in H. destruct (dec h h') eqn:Hdec; try discriminate.
    simpl. rewrite Hdec. apply IHt' in H. rewrite H. reflexivity.
  Qed.

  Lemma incl_l_nil_false {A : Type} (l : set A) :
    l <> [] <-> ~(incl l []).
  Proof.
    split; intros; intro H1; apply H.
    - apply incl_l_nil in H1. assumption.
    - unfold incl. intros. rewrite H1 in H0.
      assumption.
  Qed.

  Lemma In_incl_singleton {A : Type} (a : A) (V : set A) :
    In a V <-> incl [a] V.
  Proof.
    split; induction V.
    - intros. contradiction.
    - simpl in *. intros. destruct H.
      + rewrite H. apply incl_cons.
        * simpl. auto.
        * apply incl_nil_l.
      + apply incl_cons.
        * simpl. right. assumption.
        * apply incl_nil_l.
    - intros. apply incl_l_nil_false in H. contradiction.
      discriminate.
    - intros. simpl in *. destruct (H a).
      + simpl. left. reflexivity.
      + left. assumption.
      + right. assumption.
  Qed.

  Lemma incl_set_add_reduce {A : Type} (dec : forall x y, {x = y} + {x <> y}) (x : A) (s1 s2 : set A) :
    incl (set_add dec x s1) s2 ->
    incl s1 s2.
  Proof.
    intros. induction s1 as [|h t]; try apply incl_nil_l.
    simpl. apply incl_cons.
    + apply H. simpl. destruct (dec x h);
      left; reflexivity.
    + simpl in *. destruct (dec x h); apply incl_cons_inv in H.
      * apply H.
      * apply IHt. apply H.
  Qed.

  Lemma incl_set_add_reduce2 {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (w : A) (V W : set A) :
    incl V W ->
    incl V (set_add dec w W).
  Proof.
    intros. induction V as [|v V]; try apply incl_nil_l.
    apply incl_cons_inv in H. destruct H.
    apply incl_cons.
    - apply set_add_intro1. assumption.
    - apply IHV. assumption.
  Qed.

  Lemma incl_set_add_reduce3 {A : Type} (dec : forall x y, {x = y} + {x <> y}) (s1 s2 : set A) (a : A) :
    incl s1 (set_add dec a s2) ->
    incl (set_add dec a s1) (set_add dec a s2).
  Proof.
    generalize dependent s2. induction s1 as [|h t]; intros.
    - simpl. destruct s2 as [|h' t'].
      + simpl. apply incl_refl.
      + simpl. destruct (dec a h').
        * subst. apply In_incl_singleton.
          left. reflexivity.
        * apply In_incl_singleton.
          right. apply set_add_intro.
          left. reflexivity.
    - simpl. destruct (dec a h); try assumption.
      apply incl_cons_inv in H. destruct H.
      apply incl_cons; try assumption.
      apply IHt. assumption.
  Qed.

  Lemma length_set_add_reduce {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (t V : set A) :
    Datatypes.length (set_add dec h t) <= Datatypes.length V ->
    Datatypes.length t <= Datatypes.length V.
  Proof.
    induction t; intros.
    - simpl. lia.
    - simpl in H. destruct (dec h a).
      + simpl in *. assumption.
      + simpl in *.
  Admitted.

  Lemma incl_set_add_cons_reduce {A : Type} (dec : forall x y, {x = y} + {x <> y}) (x : A) (s1 s2 : set A) :
    incl s1 s2 -> incl (set_add dec x s1) (x :: s2).
  Proof.
    intros. induction s1 as [|h t].
    - simpl. apply incl_cons. left. reflexivity.
      apply incl_nil_l.
    - simpl. destruct (dec x h).
      + subst. apply incl_tl. assumption.
      + apply incl_cons.
        * simpl. right. apply incl_cons_inv in H.
          destruct H. apply H.
        * simpl. apply IHt. apply incl_cons_inv in H.
          destruct H. apply H0.
  Qed.

  Lemma incl_cons_set_add_reduce {A : Type} (dec : forall x y, {x = y} + {x <> y}) (x h : A) (t s2 : set A) :
    x <> h /\ incl (set_add dec x (h :: t)) s2 ->
    incl (set_add dec x t) s2.
  Proof.
    intros. destruct H. induction t as [|h' t'].
    - simpl in *. destruct (dec x h); try contradiction.
      assert ([h; x] = [h] ++ [x]) by reflexivity.
      rewrite H1 in H0. apply incl_app_inv in H0. apply H0.
    - simpl in *. destruct (dec x h); try contradiction.
      destruct (dec x h'); apply incl_cons_inv in H0;
      apply H0.
  Qed.

  Lemma incl_fold_right_andb_true {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    incl V W ->
    forall l : set A,
      fold_right andb true (map (fun x => set_mem dec x V) l) = true ->
      fold_right andb true (map (fun x => set_mem dec x W) l) = true.
  Proof.
    intros. induction l as [|h t]; try reflexivity.
    simpl in *. apply andb_true_iff in H0. destruct H0.
    apply andb_true_iff. split.
    - apply (set_mem_correct2 dec). apply H.
      apply (set_mem_correct1 dec) in H0.
      assumption.
    - apply IHt. assumption.
  Qed.

  Lemma incl_fold_right_andb_false {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    incl V W ->
    forall l : set A,
      fold_right andb true (map (fun x => set_mem dec x W) l) = false ->
      fold_right andb true (map (fun x => set_mem dec x V) l) = false.
  Proof.
    intros. induction l as [|h t]; try discriminate.
    simpl in *. apply andb_false_iff in H0.
    apply andb_false_iff. destruct H0.
    - left. apply (set_mem_complete2 dec).
      apply (set_mem_complete1 dec) in H0.
      intros Hneg. apply H in Hneg. contradiction.
    - right. apply IHt. assumption.
  Qed.

  Lemma set_diff_nil_incl {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    set_diff dec V W = [] <-> incl V W.
  Proof.
    split.
    - intros. induction V as [|h t]; induction W as [|h' t'];
      try apply incl_nil_l; simpl in H.
      + apply set_add_not_empty in H. contradiction.
      + destruct (dec h h') eqn:Hdec.
        * apply IHt in H. rewrite e. apply incl_cons.
          -- simpl. left. reflexivity.
          -- assumption.
        * destruct (set_mem dec h t') eqn:Hht.
          -- simpl. apply (set_mem_correct1 dec) in Hht.
             apply IHt in H. apply incl_cons.
             ++ right. assumption.
             ++ assumption.
          -- apply set_add_not_empty in H. contradiction.
    - intros. induction V as [|h t]; try reflexivity.
      + simpl. destruct (set_mem dec h W) eqn:Hhw.
        * apply (set_mem_correct1 dec) in Hhw. apply IHt.
          apply incl_cons_inv in H. apply H.
        * apply (set_mem_complete1 dec) in Hhw.
          apply incl_cons_inv in H. destruct H.
          contradiction.
  Qed.

  Lemma set_diff_nil_false (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (l : set A) :
    l <> [] -> ~(set_diff dec l [] = []).
  Proof.
    intros. unfold not. intros. apply H.
    induction l as [|h t]; try reflexivity.
    destruct t as [|h' t]; try contradiction.
    simpl in *. apply set_add_not_empty in H0. contradiction.
  Qed.

  Lemma incl_V_singleton {A : Type} (dec : forall x y: A, {x = y} + {x <> y}) :
    forall (V : set A) (a : A),
    incl V [a] ->
    (nodup dec V) = [a] \/ V = [].
  Proof.
    induction V as [|h t]; intros.
    - right. reflexivity.
    - apply incl_cons_inv in H.
      destruct H. assert (H1 := H0).
      apply IHt in H0. destruct H0.
      + simpl. destruct (in_dec dec h t).
        * left. assumption.
        * simpl in H. destruct H; try contradiction.
          subst. rewrite <- (nodup_In dec) in n.
          rewrite H0 in n. exfalso. apply n.
          left. reflexivity.
      + subst. simpl in *. destruct H; try contradiction.
        subst. left. reflexivity.
  Qed.

  Lemma set_add_cons {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (t : set A) :
    forall h x,
      set_mem dec x (h :: t) = false ->
      (h :: set_add dec x t) = (h :: t) ++ [x].
  Proof.
    induction t as [|h' t]; intros; try reflexivity.
    simpl in *. destruct (dec x h'); subst.
    - destruct (dec h' h); discriminate.
    - destruct (dec x h); try discriminate.
      f_equal. apply IHt. destruct (dec x h'); try assumption.
      subst. contradiction.
  Qed.

  Lemma incl_set_add_reduce_set_mem {A : Type} (dec : forall x y, {x = y} + {x <> y}) (x y z : A) (s1 s2 : set A) :
    set_mem dec x s1 = false ->
    incl s1 s2 ->
    incl (set_add dec x s1) (x :: s2).
  Proof.
    intros. induction s1 as [|h t].
    - simpl. apply incl_cons.
      + left. reflexivity.
      + apply incl_nil_l.
    - simpl. destruct (dec x h) eqn:Hxh; subst.
      + apply incl_tl. assumption.
      + erewrite set_add_cons; simpl; try assumption.
        apply incl_cons.
        * right. apply incl_cons_inv in H0. destruct H0.
          assumption.
        * assert (set_mem dec x t = false). destruct H.
          simpl. rewrite Hxh. reflexivity.
          assert (set_mem dec x t = false) by assumption.
          apply set_add_mem_false in H1. rewrite <- H1.
          apply IHt. assumption. apply incl_cons_inv in H0.
          apply H0.
  Qed.

  Lemma incl_eq {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    nodup dec V = nodup dec W -> incl V W /\ incl W V.
  Proof.
    split.
    - destruct V as [|h t].
      + apply incl_nil_l.
      + simpl in H. destruct (in_dec dec h t).
      * rewrite <- nodup_In in i. rewrite H in i.
        rewrite nodup_In in i. apply incl_cons.
        assumption. rewrite <- nodup_incl.
        rewrite <- H. rewrite nodup_incl. apply incl_refl.
      * rewrite <- nodup_incl. rewrite <- H.
        apply incl_cons.
        -- left. reflexivity.
        -- right. apply nodup_In. assumption.
    - destruct V as [|h t].
      + rewrite <- nodup_incl. rewrite H. rewrite nodup_incl.
        apply incl_refl.
      + rewrite <- nodup_incl. rewrite H. rewrite nodup_incl.
        apply incl_refl.
  Qed.

  Lemma nodup_incl2 {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V W : set A) :
    incl V W <-> incl (nodup dec V) W.
  Proof.
    split; intros.
    - induction V as [|h t]; try apply incl_nil_l.
      simpl in *. destruct (in_dec dec h t).
      + apply IHt. apply incl_cons_inv in H. apply H.
      + apply incl_cons.
        * apply incl_cons_inv in H. destruct H. assumption.
        * apply IHt. apply incl_cons_inv in H. apply H.
    - induction V as [|h t]; try apply incl_nil_l.
      simpl in *. destruct (in_dec dec h t).
      + apply incl_cons.
        * apply IHt in H. eapply incl_tran.
          -- apply H.
          -- apply incl_refl.
          -- assumption.
        * apply IHt in H. assumption.
      + apply incl_cons_inv in H. destruct H. apply incl_cons.
        * assumption.
        * apply IHt in H0. assumption.
  Qed.

  Lemma nodup_incl_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V W : set A) :
    incl V W ->
    Datatypes.length (nodup dec V) <= Datatypes.length (nodup dec W).
  Proof.
    intros. assert (NoDup (nodup dec V)).
    apply NoDup_nodup. apply NoDup_incl_length.
    assumption. apply nodup_incl. apply nodup_incl2.
    assumption.
  Qed.

  Definition strict_subset {A : Type} (s1 s2 : set A) :=
    incl s1 s2 /\ ~(incl s2 s1).

  Lemma set_add_In {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x : A) (V : set A) :
    In x V -> set_add dec x V = V.
  Proof.
    intros. induction V; try contradiction.
    simpl. destruct (dec x a).
    - subst. reflexivity.
    - simpl in *. destruct H.
      + subst. contradiction.
      + apply IHV in H. rewrite H. reflexivity.
  Qed.

  Lemma set_add_not_In {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x : A) (V : set A) :
    ~ In x V -> set_add dec x V = V ++ [x].
  Proof.
    intros. induction V; try reflexivity.
    simpl. destruct (dec x a).
    - subst. exfalso. apply H. left. reflexivity.
    - f_equal. apply IHV. unfold not. intros.
      apply H. right. assumption.
  Qed.

  Lemma set_diff_In_emptyR {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x : A) (V : set A) :
    In x V <->
    In x (set_diff dec V []).
  Proof.
    generalize dependent x.
    induction V; split; intros;
    try contradiction; simpl in *.
    - destruct H; subst.
      + apply set_add_intro. left.
        reflexivity.
      + apply set_add_intro. right.
        apply IHV. assumption.
    - apply set_add_elim in H.
      destruct H; try auto.
      right. apply IHV. assumption.
  Qed.

  Lemma set_diff_nodup_eq {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    set_diff dec (nodup dec V) (nodup dec W) = set_diff dec V W.
  Proof.
    induction V as [|h t]; try reflexivity.
    simpl. destruct (in_dec dec h t).
    + simpl. destruct (set_mem dec h W) eqn:HhW; try assumption.
      apply set_mem_complete1 in HhW. unfold set_In in HhW.
      rewrite IHt. eapply (set_diff_intro dec) in HhW.
      apply (set_add_In dec) in HhW. rewrite HhW. reflexivity.
      assumption.
    + simpl. destruct (set_mem dec h W) eqn:HhW; destruct (set_mem dec h (nodup dec W)) eqn:HhWn.
      * rewrite IHt. reflexivity.
      * apply set_mem_complete1 in HhWn. apply set_mem_correct1 in HhW.
        unfold set_In in *. rewrite nodup_In in HhWn. contradiction.
      * apply set_mem_correct1 in HhWn. apply set_mem_complete1 in HhW.
        unfold set_In in *. rewrite nodup_In in HhWn. contradiction.
      * rewrite IHt. reflexivity.
  Qed.

  Lemma set_union_nil_incl_l {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V : set A) :
    incl (set_union dec [] V) V.
  Proof.
    induction V; try apply incl_nil_l.
    simpl in *. destruct (in_dec dec a (set_union dec [] V));
    apply incl_set_add_cons_reduce; assumption.
  Qed.

  Lemma set_union_nil_incl_r {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V : set A) :
    incl (set_union dec V []) V.
  Proof.
    induction V; try apply incl_nil_l.
    simpl in *. apply incl_refl.
  Qed.

  Lemma set_union_l_nil {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V W : set A) :
    set_union dec V [] = V.
  Proof. destruct V; try reflexivity. Qed.

  Lemma set_union_incl_nil {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V W : set A) :
    V = [] ->
    W = [] ->
    incl (set_union dec V W) [].
  Proof.
    intros. subst. simpl. apply incl_refl.
  Qed.

  Definition incl_dec {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    {incl V W} + {~ incl V W}.
  Proof.
    induction V as [|h t].
    - left. apply incl_nil_l.
    - destruct (in_dec dec h W).
      + destruct IHt.
        * left. apply incl_cons; assumption.
        * right. unfold not. intros. apply n.
          apply incl_cons_inv in H. apply H.
      + right. unfold not. intros. apply n.
        apply incl_cons_inv in H. destruct H.
        apply H.
  Qed.

  Lemma incl_set_add_iff {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V W : set A) (a : A) :
    incl (set_add dec a V) W <-> incl (a :: V) W.
  Proof.
    split; intros.
    - apply incl_cons.
      + destruct (in_dec dec a V).
        * assert (In a V) by assumption.
          apply (set_add_In dec) in i. rewrite i in H.
          apply In_incl_singleton in H0. eapply incl_tran.
          apply H0. apply H. left. reflexivity.
        * assert (~ In a V) by assumption.
          apply (set_add_not_In dec) in n. rewrite n in H.
          eapply incl_app_inv in H. destruct H. apply H1.
          left. reflexivity.
      + destruct (in_dec dec a V).
        * assert (In a V) by assumption.
          apply (set_add_In dec) in i. rewrite i in H. assumption.
        * assert (~ In a V) by assumption.
          apply (set_add_not_In dec) in n. rewrite n in H.
          eapply incl_app_inv in H. destruct H. apply H.
    - apply incl_cons_inv in H. destruct H as [H H'].
      destruct (in_dec dec a V).
      + apply (set_add_In dec) in i. rewrite i. assumption.
      + apply (set_add_not_In dec) in n. rewrite n.
        apply incl_app; try assumption. apply In_incl_singleton.
        assumption.
  Qed.

  Lemma set_union_nil_incl_iff_lr {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    incl V W <-> incl (set_union dec [] V) W.
  Proof.
    split; intros; induction V;
    try apply incl_nil_l; try assumption; simpl.
    - destruct (in_dec dec a (set_union dec [] V)).
      + apply (set_add_In dec) in i. rewrite i.
        apply IHV. apply incl_cons_inv in H. apply H.
      + assert (~ In a (set_union dec [] V)) by assumption.
        apply (set_add_not_In dec) in n. rewrite n.
        apply incl_cons_inv in H. destruct H.
        apply IHV in H1. apply incl_app; try assumption.
        apply In_incl_singleton. assumption.
    - apply incl_cons; simpl in H.
      + destruct (in_dec dec a (set_union dec [] V)).
        * assert (In a (set_union dec [] V)) by assumption.
          apply (set_add_In dec) in i. rewrite i in H.
          apply In_incl_singleton in H0.
          eapply incl_tran. apply H0. apply H.
          simpl. left. reflexivity.
        * apply (set_union_emptyR dec). simpl. unfold set_In.
          rewrite incl_set_add_iff in H. apply incl_cons_inv in H.
          destruct H. apply H.
      + destruct (in_dec dec a (set_union dec [] V)).
        * apply (set_add_In dec) in i. rewrite i in H.
          apply IHV in H. assumption.
        * apply (set_add_not_In dec) in n. rewrite n in H.
          apply incl_app_inv in H. destruct H. apply IHV in H.
          assumption.
  Qed.

  Lemma incl_set_union_intro1 {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V : set A) :
    forall W U,
      incl V W ->
      incl V (set_union dec W U).
  Proof.
    induction V as [|h t]; intros; try apply incl_nil_l.
    apply incl_cons_inv in H. destruct H. apply incl_cons.
    - apply set_union_intro1. assumption.
    - apply IHt. assumption.
  Qed.

  Lemma incl_set_union_intro2 {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W U : set A) :
    incl V W ->
    incl V (set_union dec U W).
  Proof.
    induction V as [|h t]; intros; try apply incl_nil_l.
    apply incl_cons_inv in H. destruct H. apply incl_cons.
    - apply set_union_intro2. assumption.
    - apply IHt. assumption.
  Qed.

  Lemma incl_set_union_elim1 {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W U : set A) :
    incl (set_union dec V W) U ->
    incl V U.
  Proof.
    induction W as [|h t]; intros.
    - simpl in *. assumption.
    - simpl in *. apply incl_set_add_reduce in H.
      apply IHt in H. assumption.
  Qed.

  Lemma set_diff_not_In_emptyR {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x : A) (V : set A) :
    ~ In x V -> ~ In x (set_diff dec V []).
  Proof.
    intros. induction V.
    - simpl. unfold not. intros. contradiction.
    - simpl. rewrite set_add_iff. unfold not. intros.
      destruct H0.
      + subst. apply H. left. reflexivity.
      + apply IHV. unfold not. intros. apply H.
        right. assumption. assumption.
  Qed.

  Lemma set_add_not_In_length_S_n {A : Type} (dec : forall x y, {x = y} + {x <> y}) (x : A) (V : set A) :
    ~ In x V <->
    Datatypes.length (set_add dec x V) = S (Datatypes.length V).
  Proof.
    split; induction V as [|h t];
    try reflexivity; intros; simpl in *.
    - destruct (dec x h).
      + subst. destruct H. left. reflexivity.
      + simpl. destruct (dec x h); try contradiction.
        rewrite IHt. reflexivity. unfold not.
        intros. apply H. right. assumption.
    - unfold not. intros. contradiction.
    - unfold not. intros. destruct IHt; rewrite eq_sym_iff in H0;
      rewrite <- (set_add_iff dec) in H0; destruct (dec x h);
      try simpl in *; try lia. destruct t; simpl in *.
      + destruct H0; subst; contradiction.
      + destruct (dec x a).
        * subst. left. reflexivity.
        * simpl in *. destruct (dec h a).
          -- subst. destruct H0; auto.
          -- simpl in *. destruct H0; try auto.
             right. apply set_add_iff in H0. destruct H0;
             subst; try contradiction; try assumption.
  Qed.

  Lemma set_add_In_length_n {A : Type} (dec : forall x y, {x = y} + {x <> y}) (x : A) (V : set A) :
    In x V <->
    Datatypes.length (set_add dec x V) = Datatypes.length V.
  Proof.
    split; induction V as [|h t];
    intros; simpl in *; try contradiction; try discriminate.
    - destruct (dec x h); try reflexivity.
      simpl. destruct H; subst; try contradiction.
      apply IHt in H. rewrite H. reflexivity.
    - destruct (dec x h).
      + subst. left. reflexivity.
      + simpl in *. apply eq_add_S in H. apply IHt in H.
        right. assumption.
  Qed.

  Lemma set_add_le_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V : set A) (x : A) :
    forall n,
      Datatypes.length (set_add dec x V) = n ->
      Datatypes.length V <= n.
  Proof.
    induction V as [|h t]; intros; simpl in *; try lia.
    destruct (dec x h); simpl in *.
    - rewrite H. apply Nat.le_refl.
    - rewrite <- H. apply le_n_S. apply IHt. reflexivity.
  Qed.

  Lemma set_diff_nil {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V : set A) :
    Datatypes.length (set_diff dec (nodup dec V) []) =
    Datatypes.length (nodup dec V).
  Proof.
    induction V as [|h t IHV]; try reflexivity.
    simpl. destruct (in_dec dec h t); try assumption.
    rewrite <- (nodup_In dec) in n. simpl. rewrite <- IHV.
    simpl. apply (set_add_not_In_length_S_n dec).
    unfold not. intros. apply n. apply (nodup_In dec).
    apply set_diff_elim1 in H. contradiction.
  Qed.

  Lemma set_union_incl (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    incl V (set_union dec V W) /\ incl W (set_union dec V W).
  Proof.
    split.
    - induction V; try apply incl_nil_l; apply incl_cons.
      + apply set_union_intro1. left. reflexivity.
      + unfold incl. intros. apply set_union_intro1. right. apply H.
    - induction W; try apply incl_nil_l; apply incl_cons.
      + apply set_union_intro2. left. reflexivity.
      + unfold incl. intros. apply set_union_intro2. right. apply H.
  Qed.

  Lemma set_diff_nil_length_nodup {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V : set A) :
    Datatypes.length (set_diff dec V []) = Datatypes.length (nodup dec V).
  Proof.
    induction V; try reflexivity.
    simpl. destruct (in_dec dec a V).
    - rewrite <- IHV. apply (set_diff_In_emptyR dec) in i.
      apply (set_add_In dec) in i. rewrite i. reflexivity.
    - simpl. rewrite <- IHV. apply (set_diff_not_In_emptyR dec) in n.
      apply (set_add_not_In dec) in n.
      rewrite n. rewrite app_length. simpl. lia.
  Qed.

  Lemma set_add_In_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (l : set A) (a : A) :
    (In a l -> Datatypes.length (set_add dec a l) = Datatypes.length l) /\
    (~ In a l -> Datatypes.length (set_add dec a l) = S (Datatypes.length l)).
  Proof.
    split; intros; induction l as [|h t]; try reflexivity.
    - contradiction.
    - simpl. destruct (dec a h); subst; try reflexivity.
      simpl. f_equal. apply IHt. simpl in H. destruct H.
      + subst. contradiction.
      + assumption.
    - simpl. destruct (dec a h); subst.
      + destruct H. left. reflexivity.
      + simpl. f_equal. apply IHt. unfold not. intros.
        apply H. right. assumption.
  Qed.

  Lemma set_diff_In_consR {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (t V : set A) :
    In h t ->
    set_diff dec (h :: t) V = set_diff dec t V.
  Proof.
    intros. simpl. destruct (set_mem dec h V) eqn:Hmem;
    try reflexivity. apply set_mem_complete1 in Hmem.
    unfold set_In in Hmem. assert (In h t /\ ~ In h V).
    { split; assumption. } rewrite <- set_diff_iff in H0.
    apply (set_add_In dec) in H0. rewrite H0. reflexivity.
  Qed.

  Lemma set_diff_In_consL {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (t V : set A) :
    In h t ->
    set_diff dec V (h :: t) = set_diff dec V t.
  Proof.
    intros. induction V; try reflexivity.
    - simpl. destruct (dec a h).
      + subst. destruct (set_mem dec h t) eqn:Hmem.
        * assumption.
        * apply set_mem_complete1 in Hmem.
          unfold set_In in Hmem. contradiction.
      + destruct (set_mem dec h t) eqn:Hmem1;
        destruct (set_mem dec a t) eqn:Hmem2; try assumption.
        * f_equal. assumption.
        * f_equal. assumption.
  Qed.

  (* NEEDED *)
  Lemma set_diff_succ {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V : set A) (n : nat) :
    forall W,
      incl W V ->
      Datatypes.length (set_diff dec (nodup dec V) (nodup dec W)) = S n ->
      S (Datatypes.length (nodup dec W)) <= Datatypes.length (nodup dec V).
  Proof.
  Admitted.

  Lemma set_add_add {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (V W : set A) :
    (~ In h V /\ ~ In h W) \/
    (In h V /\ In h W) ->
    set_add dec h V = set_add dec h W ->
    V = W.
  Proof.
    intros. destruct H as [[H1 H2] | [H1 H2]].
  - apply (set_add_not_In dec) in H1, H2.
    rewrite H1, H2 in H0. apply app_inv_tail in H0.
    assumption.
  - apply (set_add_In dec) in H1, H2.
    rewrite H1, H2 in H0. assumption.
  Qed.

  Lemma set_union_nodup_r {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V W : set A) :
    set_union dec V (nodup dec W) = set_union dec V W.
  Proof.
    intros. induction W as [|h t]; try reflexivity.
    simpl. destruct (in_dec dec h t).
    - apply (set_union_intro2 dec h V t) in i.
      apply (set_add_In dec) in i. rewrite i. assumption.
    - simpl in *. rewrite IHt. reflexivity.
  Qed.

  Lemma nodup_nil_iff {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V : set A):
    nodup dec V = [] <-> V = [].
  Proof.
    split; intros.
    - induction V; try reflexivity.
      simpl in H. destruct (in_dec dec a V).
      + apply IHV in H. subst. contradiction.
      + discriminate.
    - subst. reflexivity.
  Qed.

  Lemma set_union_cons_rm_r {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) :
    forall V U W,
      set_union dec V W = set_union dec U W ->
      set_union dec V (h :: W) = set_union dec U (h :: W).
  Proof.
    intros. simpl. f_equal. apply H.
  Qed.

  Lemma set_diff_nil_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V : set A) :
    Datatypes.length (set_diff dec V []) <= Datatypes.length V.
  Proof.
    intros. induction V as [|h t]; try reflexivity.
    simpl in *. destruct (in_dec dec h t).
    - apply (set_diff_intro dec h t []) in i.
      + apply (set_add_In dec) in i. rewrite i.
        apply le_S. assumption.
      + unfold not. intros. apply H.
    - assert (~ In h (set_diff dec t [])).
      + unfold not. intros. apply n.
        apply (set_diff_elim1 dec h t []). assumption.
      + apply (set_add_not_In dec) in H. rewrite H.
        rewrite app_length. simpl. lia.
  Qed.

  Lemma set_diff_nodup_l {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    set_diff dec V W = set_diff dec (nodup dec V) W.
  Proof.
    induction V as [|h t]; try reflexivity.
    simpl. destruct (set_mem dec h W) eqn:Hmem.
    - destruct (in_dec dec h t); simpl; try rewrite Hmem; assumption.
    - apply set_mem_complete1 in Hmem. unfold set_In in *. destruct (in_dec dec h t).
      + apply (set_diff_intro dec h t W) in Hmem; try assumption.
        apply (set_add_In dec) in Hmem. rewrite Hmem. assumption.
      + simpl. apply (set_mem_complete2 dec) in Hmem. rewrite Hmem.
        f_equal. assumption.
  Qed.

  Lemma set_diff_nodup_r {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    set_diff dec V W = set_diff dec V (nodup dec W).
  Proof.
    induction V as [|h t]; try reflexivity.
    simpl. destruct (set_mem dec h W) eqn:Hmem.
    - apply set_mem_correct1 in Hmem. rewrite <- (nodup_In dec) in Hmem.
      apply (set_mem_correct2 dec) in Hmem. rewrite Hmem.
      assumption.
    - apply set_mem_complete1 in Hmem. rewrite <- (nodup_In dec) in Hmem.
      apply (set_mem_complete2 dec) in Hmem. rewrite Hmem.
      f_equal. assumption.
  Qed.

  Lemma set_add_length_not_nil {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (V : set A) :
    Datatypes.length (set_add dec h V) <> 0.
  Proof.
    intros. destruct V as [|h' V]; try discriminate.
    simpl. destruct (dec h h'); try discriminate.
  Qed.

  Lemma set_diff_length_cons_nil {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (V t : set A) :
    Datatypes.length (set_diff dec V (h :: t)) = 0 ->
    V = [] \/ In h V.
  Admitted.

  Lemma set_diff_length_zero {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    Datatypes.length (set_diff dec V W) = 0 ->
    nodup dec V = nodup dec W.
  Proof.
    generalize dependent V.
    induction W as [|w W]; intros.
    - destruct V as [|v V]; try reflexivity.
      simpl in *. destruct (in_dec dec v V);
      apply set_add_length_not_nil in H; contradiction.
    - simpl in *. destruct (in_dec dec w W).
      + apply IHW. apply (set_diff_In_consL dec w W V) in i.
        rewrite i in H. assumption.
      + simpl in *. apply set_diff_length_cons_nil in H.
        destruct H.
        * subst. simpl.
  Admitted.

  Lemma set_add_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (V : set A) :
    Datatypes.length (set_add dec h V) <= S (Datatypes.length V).
  Proof.
    induction V as [|h' V]; try reflexivity; simpl.
    destruct (dec h h'); simpl; lia.
  Qed.

  Lemma set_add_set_diff_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (V W : set A) :
    Datatypes.length (set_add dec h (set_diff dec V W)) <=
    S (Datatypes.length V).
  Proof.
    induction V as [|h' V]; try reflexivity; simpl.
    destruct (dec h h'); simpl; try lia; intros.
    - subst. destruct (set_mem dec h' W) eqn:Hmem.
      + simpl. apply le_S. apply IHV.
      + simpl. apply le_S.
        destruct (set_mem dec h' (set_diff dec V W)) eqn:Hmem2.
        * apply set_mem_correct1 in Hmem2.
          apply (set_add_In dec) in Hmem2.
          rewrite Hmem2. apply IHV.
        * apply set_mem_complete1 in Hmem2.
          apply (set_add_not_In dec) in Hmem2.
          rewrite Hmem2.
          assert (set_add dec h' (set_diff dec V W ++ [h']) = set_diff dec V W ++ [h']).
          { destruct (set_diff dec V W).
            - simpl. destruct (dec h' h');
              try reflexivity. contradiction.
            - simpl in *. destruct (dec h' a);
              try reflexivity. simpl.
              assert (In h' (s ++ [h'])).
              { apply in_or_app. right. left. reflexivity. }
              apply (set_add_In dec) in H. rewrite H.
              reflexivity. }
          rewrite H. rewrite app_length. simpl.
          rewrite Nat.add_1_r. rewrite Hmem2 in IHV.
          rewrite app_length in IHV. simpl in IHV.
          rewrite Nat.add_1_r in IHV. apply IHV.
    - destruct (set_mem dec h' W) eqn:Hmem.
      + simpl. apply le_S. apply IHV.
      + simpl. apply le_S.
        destruct (set_mem dec h' (set_diff dec V W)) eqn:Hmem2.
        * apply set_mem_correct1 in Hmem2.
          apply (set_add_In dec) in Hmem2.
          rewrite Hmem2. apply IHV.
        * apply set_mem_complete1 in Hmem2.
          apply (set_add_not_In dec) in Hmem2.
          rewrite Hmem2.
          destruct (set_mem dec h (set_diff dec V W ++ [h'])) eqn:Hmem3.
          -- apply set_mem_correct1 in Hmem3.
             apply (set_add_In dec) in Hmem3.
             rewrite Hmem3. rewrite app_length. simpl.
             rewrite Nat.add_1_r. eapply Nat.le_trans in IHV.
             apply IHV.
  Admitted.

  Lemma nodup_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V : set A) :
    Datatypes.length (nodup dec V) <= Datatypes.length V.
  Proof.
    induction V as [|h t]; try reflexivity.
    simpl. destruct (in_dec dec h t); simpl; lia.
  Qed.

  Lemma set_diff_length_le {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    Datatypes.length (set_diff dec V W) <= Datatypes.length V.
  Proof.
    generalize dependent V.
    induction W as [|w W]; intros.
    - rewrite set_diff_nodup_l.
      rewrite set_diff_nil. apply nodup_length.
    - induction V as [|v V].
      + simpl. lia.
      + simpl. destruct (dec v w) eqn:Hdec.
        * lia.
        * destruct (set_mem dec v W) eqn:Hmem.
          -- lia.
          -- apply set_mem_complete1 in Hmem.
             apply (set_add_not_In dec) in Hmem.
  Admitted.

  (* NEEDED *)
  Lemma set_diff_incl_lt_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (u : A) (V W U : set A) :
    incl W V ->
    incl (u :: U) (set_diff dec V W) ->
    Datatypes.length (set_diff dec V (set_union dec W (u :: U))) <
      Datatypes.length (set_diff dec V W).
  Proof.
    intros. apply incl_cons_inv in H0. destruct H0.
    induction W as [|w W].
    - simpl.
      assert (Datatypes.length (set_diff dec V []) = Datatypes.length (set_diff dec (nodup dec V) [])).
      { rewrite set_diff_nodup_l. reflexivity. }
      rewrite set_diff_nil_length_nodup.
      apply (set_diff_In_emptyR dec) in H0.
  Admitted.

  Lemma set_diff_refl_nil {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (l : set A) :
    set_diff dec l l = [].
  Proof.
    induction l; try reflexivity.
    simpl. destruct (dec a a); try contradiction.
    rewrite set_diff_nil_incl. apply incl_tl.
    apply incl_refl.
  Qed.

  Lemma incl_set_union_l_nil {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    incl V W ->
    incl V (set_union dec W []).
  Proof.
    intros. induction W as [|h t]; simpl; try assumption.
  Qed.

  Lemma incl_set_union_nil_l {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    incl V W ->
    incl (set_union dec [] V) W.
  Proof.
    intros. induction V as [|h t]; try apply incl_nil_l.
    simpl. apply incl_cons_inv in H. destruct H.
    apply incl_set_add_iff. apply incl_cons.
    assumption. apply IHt. assumption.
  Qed.

  (* CAN BE USED AS EXAMPLE FOR SET_UNION HARD PROOF *)
  Lemma incl_set_add_set_union_nil {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (h : A) (V t : set A) :
    incl (set_add dec h t) V ->
    incl (set_add dec h (set_union dec [] t)) V.
  Proof.
    intros. apply incl_set_add_iff. apply incl_set_add_iff in H.
    induction V as [|h' t'].
    - apply incl_l_nil_false in H. contradiction.
      discriminate.
    - apply incl_cons_inv in H. destruct H.
      apply incl_cons; try assumption.
      apply (incl_set_union_nil_l dec). assumption.
  Qed.

  Lemma incl_set_union_trans {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W U : set A) :
    incl W V ->
    incl U V ->
    incl (set_union dec W U) V.
  Proof.
    intros. destruct V as [|v V].
    - simpl. apply set_union_incl_nil.
      + destruct W; try reflexivity.
        apply incl_l_nil_false in H. contradiction.
        discriminate.
      + destruct U; try reflexivity.
        apply incl_l_nil_false in H0. contradiction.
        discriminate.
    - unfold incl in *. intros.
      apply (set_union_elim dec) in H1. destruct H1.
      + apply H in H1. assumption.
      + apply H0 in H1. assumption.
  Qed.

  Lemma set_union_nil_iff {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) :
    set_union dec V W = [] <->
    V = [] /\ W = [].
  Proof.
    split; intros.
    - split.
      + induction W as [|w W]; try assumption.
        simpl in H. apply set_add_not_empty in H.
        contradiction.
      + induction W as [|w W]; try reflexivity.
        simpl in H. apply set_add_not_empty in H.
        contradiction.
    - destruct H. rewrite H. rewrite H0. reflexivity.
  Qed.

  Lemma incl_set_union_nodup_l {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W U : set A) :
    incl V (nodup dec (set_union dec (nodup dec W) U)) <->
    incl V (nodup dec (set_union dec W U)).
  Proof.
    generalize dependent W. generalize dependent U.
    induction V as [|v V]; intros; split; intros;
    try assumption; simpl in *; try apply incl_nil_l.
    - apply incl_cons_inv in H. destruct H.
      apply incl_cons.
      + apply nodup_In in H. apply nodup_In.
        destruct U as [|u U].
        * simpl in *. apply nodup_In in H. assumption.
        * simpl in *. apply set_add_elim in H. destruct H.
          -- apply set_add_intro. left. assumption.
          -- apply set_add_intro. right. unfold set_In in *.
             apply set_union_elim in H.
             apply set_union_intro. destruct H.
             ++ left. apply (nodup_In dec). assumption.
             ++ right. assumption.
      + apply IHV. assumption.
    - apply incl_cons_inv in H. destruct H.
      apply incl_cons.
      + apply nodup_In in H. apply nodup_In.
        destruct U as [|u U].
        * simpl in *. apply nodup_In. assumption.
        * simpl in *. apply set_add_elim in H. destruct H.
          -- apply set_add_intro. left. assumption.
          -- apply set_add_intro. right. unfold set_In in *.
             apply set_union_elim in H.
             apply set_union_intro. destruct H.
             ++ left. apply (nodup_In dec). assumption.
             ++ right. assumption.
      + apply IHV. assumption.
  Qed.

  (* NEEDED *)
  Lemma length_set_diff_set_union_nodup_l {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W U : set A) :
    Datatypes.length (set_diff dec V (set_union dec (nodup dec W) U)) =
    Datatypes.length (set_diff dec V (set_union dec W U)).
  Proof.
    generalize dependent W. generalize dependent U.
    induction V as [|v V]; intros; simpl; try lia.
    - destruct (set_mem dec v (set_union dec (nodup dec W) U)) eqn:Hdec.
      assert (Hdec2 := Hdec). apply set_mem_correct1 in Hdec.
      apply set_union_elim in Hdec. destruct Hdec.
      + apply nodup_In in H. apply (set_union_intro1 dec v W U) in H.
        apply (set_mem_correct2 dec) in H. rewrite H.
        apply IHV.
      + apply (set_union_intro2 dec v W U) in H.
        apply (set_mem_correct2 dec) in H. rewrite H.
        apply IHV.
  Admitted.

  Lemma strict_subset_lt_length {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V W : set A) :
     strict_subset V W ->
     Datatypes.length (nodup dec V) < Datatypes.length (nodup dec W).
  Proof.
    intros. unfold strict_subset in H. destruct H.
    assert (H1 := H). apply (nodup_incl_length dec) in H1.
    apply le_lt_eq_dec in H1. destruct H1; try assumption.
    exfalso. apply H0. apply (nodup_incl dec).
    apply (nodup_incl2 dec). eapply NoDup_length_incl.
    - apply NoDup_nodup.
    - rewrite e. apply Nat.le_refl.
    - apply nodup_incl. apply nodup_incl2.
      assumption.
  Qed.

  Lemma nodup_nil {A : Type} (dec : forall x y, {x = y} + {x <> y}) (l : list A) :
    nodup dec l = [] -> l = [].
  Proof.
    induction l; intros; try reflexivity.
    simpl in H. destruct (in_dec dec a l).
    - apply IHl in H. subst. contradiction.
    - discriminate.
  Qed.

  Lemma app_empty {A : Type} (l1 l2 : list A) :
    l1 ++ l2 = [] -> l1 = [].
  Proof.
    intros. apply app_eq_nil in H.
    apply H.
  Qed.

End Sets.
