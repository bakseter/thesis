Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.Minus.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.ListSet.
From Coq Require Import MSets.MSetWeakList.
From Coq Require Import Structures.Equalities.
From Coq Require Import Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Setoids.Setoid.

(* Misc. lemmas and definitions *)

Definition total_map (A : Type) := string -> A.

Lemma sym : forall (A : Type) (x y : A),
  x = y <-> y = x.
Proof. split; intros; symmetry; assumption. Qed.

Lemma if_true_then_true_true (b : bool) :
  (if b then true else true) = true.
Proof. destruct b; reflexivity. Qed.

Lemma if_b_then_a_or_true (b1 b2 : bool) :
  b1 = true -> (if b2 then b1 else true) = true.
Proof. destruct b2; trivial. Qed.

Lemma bool_exfalso (b : bool) :
  b = false <-> b <> true.
Proof.
  split; unfold not in *; intros; subst; try discriminate.
  destruct b; try reflexivity. exfalso. apply H. reflexivity.
Qed.

Lemma tuple_fst {A B : Type} (a a' : A) (b b' : B) :
  (a, b) = (a', b') -> a = a'.
Proof. intros. inversion H. reflexivity. Qed.

Lemma tuple_snd {A B : Type} (a a' : A) (b b' : B) :
  (a, b) = (a', b') -> b = b'.
Proof. intros. inversion H. reflexivity. Qed.

Lemma negb_iff (b1 b2 : bool) :
  negb b1 = negb b2 <-> b1 = b2.
Proof.
  split; intros; destruct b1 eqn:Hb1; destruct b2 eqn:Hb2;
  try reflexivity; simpl in *; try discriminate.
Qed.


(* Set-related lemmas and definitions *)

Notation "s € S" := (set_mem string_dec s S) (at level 80).

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

Lemma incl_set_add_reduce {A : Type} (dec : forall x y, {x = y} + {x <> y}) (x : A) (s1 s2 : set A) :
  incl (set_add dec x s1) s2 -> incl s1 s2.
Proof.
  intros. induction s1 as [|h t]; try apply incl_nil_l.
  simpl. apply incl_cons.
  + apply H. simpl. destruct (dec x h);
    left; reflexivity.
  + simpl in *. destruct (dec x h); apply incl_cons_inv in H.
    * apply H.
    * apply IHt. apply H.
Qed.

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

Lemma incl_cons_In {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V t : set A) (h : A) :
  In h t /\ incl V (h :: t) -> incl V t.
Proof.
  intros. destruct H. induction V as [|h' t'];
  try apply incl_nil_l. apply incl_cons; simpl in *.
  - destruct (dec h' h); subst; try assumption.
    apply incl_cons_inv in H0. destruct H0.
    simpl in H0. destruct H0; subst; assumption.
  - apply IHt'. apply incl_cons_inv in H0. destruct H0.
    apply H1.
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

Lemma set_diff_In {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x : A) (V : set A) :
  In x V -> In x (set_diff dec V []).
Proof.
  intros. induction V; try contradiction.
  destruct H.
  - subst. simpl. apply set_add_intro. left. reflexivity.
  - apply IHV in H. simpl. apply set_add_intro. right.
    assumption.
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

Lemma set_union_nil_l {A : Type} (dec : forall x y, {x = y} + {x <> y}) (V W : set A) :
  set_union dec V [] = V.
Proof. destruct V; try reflexivity. Qed.

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


Lemma set_union_nil_app_incl_iff_lr {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W U : set A) :
  incl (V ++ U) W <-> incl (set_union dec [] V ++ U) W.
Proof.
  split; intros; induction V;
  try apply incl_nil_l;
  simpl in *. 
Admitted.

Lemma incl_set_union {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V : set A) :
  forall W U, incl W V -> incl U V -> incl (set_union dec W U) V.
Proof.
  induction V as [|h t]; intros.
  - destruct W; destruct U.
    + simpl. apply incl_refl.
    + apply incl_l_nil_false in H0.
      contradiction. discriminate.
    + apply incl_l_nil_false in H.
      contradiction. discriminate.
    + apply incl_l_nil_false in H.
      contradiction. discriminate.
  - induction W as [|a W]; induction U as [|b U].
    + simpl. apply incl_nil_l.
    + simpl. destruct (in_dec dec b (set_union dec [] U)).
      * apply (set_add_In dec) in i. rewrite i.
        rewrite <- (set_union_nil_incl_iff_lr dec).
        apply incl_cons_inv in H0. apply H0.
      * apply (set_add_not_In dec) in n. rewrite n.
        apply incl_cons_inv in H0. destruct H0. apply incl_app.
        -- rewrite <- (set_union_nil_incl_iff_lr dec). assumption.
        -- apply In_incl_singleton. assumption.
    + simpl. assumption.
    + 
Admitted.

Lemma set_diff_not_In {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (x : A) (V : set A) :
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
  ~ In x V <-> Datatypes.length (set_add dec x V) = S (Datatypes.length V).
Proof.
  split; induction V as [|h t];
  try reflexivity; intros; simpl in *.
  - destruct (dec x h).
    + subst. destruct H. left. reflexivity.
    + simpl. destruct (dec x h); try contradiction.
      rewrite IHt. reflexivity. unfold not.
      intros. apply H. right. assumption.
  - unfold not. intros. contradiction.
  - unfold not. intros. destruct IHt; rewrite sym in H0;
    rewrite <- (set_add_iff dec) in H0; destruct (dec x h);
    try simpl in *; try lia. destruct t; simpl in *.
    + destruct H0; subst; contradiction.
    + destruct (dec x a).
      * subst. left. reflexivity.
      * simpl in *. destruct (dec h a).
        -- subst. destruct H0; auto.
        -- simpl in *. destruct H0; try auto.
           right. apply set_add_iff in H0. destruct H0.
           ++ subst. contradiction.
           ++ assumption.
Qed.

Lemma set_add_In_length_n {A : Type} (dec : forall x y, {x = y} + {x <> y}) (x : A) (V : set A) :
  In x V <-> Datatypes.length (set_add dec x V) = Datatypes.length V.
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
  forall n, Datatypes.length (set_add dec x V) = n ->
  Datatypes.length V <= n.
Proof.
  induction V as [|h t]; intros; simpl in *; try lia.
  destruct (dec x h); simpl in *.
  - rewrite H. apply le_refl.
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

Lemma set_diff_length_nodup {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V : set A) :
  Datatypes.length (set_diff dec V []) = Datatypes.length (nodup dec V).
Proof.
  induction V; try reflexivity.
  simpl. destruct (in_dec dec a V).
  - rewrite <- IHV. apply (set_diff_In dec) in i.
    apply (set_add_In dec) in i. rewrite i. reflexivity.
  - simpl. rewrite <- IHV. apply (set_diff_not_In dec) in n.
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


(* Main definitions *)

(* ---------- NINFTY ---------- *)

Inductive Ninfty : Type :=
  | infty : Ninfty
  | fin   : nat -> Ninfty.

Definition ninfty_geq (x y : Ninfty) : bool :=
  match x with
  | infty => true
  | fin n =>
      match y with
      | infty => false
      | fin n' => n' <=? n
      end
  end.

Example ninfty_geq_test1 :
  forall n, ninfty_geq infty (fin n) = true.
Proof. reflexivity. Qed.

Example ninfty_geq_test2 :
  forall n, ninfty_geq (fin n) infty = false.
Proof. reflexivity. Qed.

Example ninfty_geq_test3 :
  forall n, ninfty_geq (fin n) (fin n) = true.
Proof. simpl. intros. apply leb_refl. Qed.

Example ninfty_geq_test4 :
  forall n n', ninfty_geq (fin n) (fin n') = (n' <=? n).
Proof. simpl. intros. reflexivity. Qed.

Example ninfty_geq_test5 :
  ninfty_geq infty infty = true.
Proof. reflexivity. Qed.

Definition Sinfty (x : Ninfty) : Ninfty :=
  match x with
  | infty => infty
  | fin n => fin (S n)
  end.

Definition is_infty (ninf : Ninfty) : bool :=
  match ninf with
  | infty => true
  | _     => false
  end.

(* ---------- FRONTIER ---------- *)

Definition Frontier := total_map Ninfty.

Example frontier_fin_0 : Frontier := fun _ => fin 0.
Example frontier_fin_1 : Frontier := fun _ => fin 1.
Example frontier_fin_2 : Frontier := fun _ => fin 2.
Example frontier_infty : Frontier := fun _ => infty.

Lemma frontier_lambda (f : Frontier) :
  (fun v : string => f v) = f.
Proof. apply functional_extensionality. intros. reflexivity. Qed.


(* ---------- ATOM ---------- *)

Inductive Atom : Type :=
  | atom : string -> nat -> Atom.

Notation "x & k" := (atom x k) (at level 80). (* level ?? *)

Definition x_str := "x"%string.
Definition y_str := "y"%string.
Definition z_str := "z"%string.

Example atom_x0 : Atom := "x" & 0.
Example atom_x1 : Atom := "x" & 1.
Example atom_x2 : Atom := "x" & 2.
Example atom_y0 : Atom := "y" & 0.
Example atom_y1 : Atom := "y" & 1.
Example atom_y2 : Atom := "y" & 2.

Definition atom_true (a : Atom) (f : Frontier) : bool :=
  match a with
  | (x & k) =>
    match f x with
    | infty => true
    | fin n => k <=? n
    end
  end.

Definition shift_atom (n : nat) (a : Atom)  : Atom :=
  match a with
  | (x & k) => (x & (n+k))
  end.

Lemma shift_atom_0 (a : Atom) :
  shift_atom 0 a = a.
Proof. induction a. reflexivity. Qed.

Lemma shift_atom_twice (a : Atom) (n m : nat) :
  shift_atom (n + m) a = shift_atom n (shift_atom m a).
Proof.
  destruct a as [x k]. simpl.
  rewrite add_assoc. reflexivity.
Qed.

Lemma map_shift_atom_0 (s : set Atom) :
  map (shift_atom 0) s = s.
Proof.
  induction s as [| h t IHl]; try reflexivity.
  simpl. rewrite IHl. rewrite shift_atom_0. reflexivity.
Qed.

Lemma map_shift_atom_twice (s : set Atom) (n m : nat) :
  map (shift_atom (n + m)) s =
  map (shift_atom n) (map (shift_atom m) s).
Proof.
  induction s; try reflexivity.
  simpl. rewrite shift_atom_twice, IHs. reflexivity.
Qed.

Lemma atom_false_shift_atom_false (a : Atom) (f : Frontier) (n : nat) :
  atom_true a f = false -> atom_true (shift_atom n a) f = false.
Proof.
  intros. induction n.
  - rewrite shift_atom_0. assumption.
  - destruct a as [x k].
    induction k; simpl; simpl in H, IHn;
    destruct (f x); try assumption;
    destruct n0; try reflexivity;
    apply leb_nle; apply leb_nle in IHn; lia.
Qed.

(* ---------- CLAUSE ---------- *)

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
   all_shifts_true (c : Clause) (f : Frontier) = false ->
   exists (n: nat), clause_true (shift_clause n c) f = false.
Proof with simpl.
  intros. unfold clause_true.
  destruct c as [conds conc]...
  destruct conc as [x k]...
  simpl in H. destruct (f x) as [|n'].
  - exists 0. rewrite if_b_then_a_or_true.
    + assumption.
    + reflexivity.
  - exists (n' + 1 - k). assumption.
Qed.

Definition all_shifts_dec (c : Clause) (f : Frontier):
  (forall n : nat, clause_true (shift_clause n c) f = true) +
  sig (fun n : nat => clause_true (shift_clause n c) f = false).
Proof with simpl.
  destruct (all_shifts_true c f) eqn:H.
  - left. intro n. apply all_shifts_true_sound. assumption.
  - right. intros. unfold clause_true.
    destruct c as [conds conc]... destruct conc as [x k]...
    simpl in H. destruct (f x) as [|n'].
    * exists 0. rewrite if_b_then_a_or_true...
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
  forall (n : nat), clause_true (shift_clause n c) f = true.
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
  forall (n : nat), all_shifts_func c f = inr n ->
  clause_true (shift_clause n c) f = false.
Proof.
  intros n H. destruct c as [conds [x k]].
  unfold all_shifts_func in H.
  destruct (f x) as [|n'] eqn:Hfx in H; try discriminate.
  destruct (clause_true (shift_clause (n' + 1 - k) (conds ~> x & k)) f) eqn:CT.
  - discriminate H.
  - inversion H. assumption.
Qed.

(* ---------- VARS ---------- *)

Fixpoint vars_set_atom (s : set Atom) : set string :=
  match s with
  | []       => []
  | ((x & _) :: t) =>
      let cl := vars_set_atom t in
      set_add string_dec x cl
  end.

Lemma vars_set_atom_cons (x : string) (t : set Atom) (k : nat) (W : set string) :
  incl (vars_set_atom ((x & k) :: t)) W -> incl (vars_set_atom t) W.
Proof.
  intros. induction t as [|h t']; try apply incl_nil_l.
  destruct h as [y k']. simpl in *.
  apply incl_set_add_reduce in H. assumption.
Qed.

Lemma incl_vars_set_atom_In (s : set Atom) (W : set string) (x : string) (k : nat) :
  incl (vars_set_atom ((x & k) :: s)) W -> In x W.
Proof.
  intros. induction W as [|h t].
  - eapply incl_l_nil_false in H; try contradiction.
    simpl. apply set_add_not_empty.
  - destruct s as [|h' t']; apply H; simpl; auto.
    destruct h'. apply set_add_intro2. reflexivity.
Qed.

Lemma vars_set_atom_incl_fold (s : set Atom) (W : set string) :
  incl (vars_set_atom s) W -> (fold_right andb true (map (fun x : string => x € W) (vars_set_atom s))) = true.
Proof.
  intros. induction s as [|h t]; try reflexivity.
  simpl. destruct h as [x k] eqn:Hxk.
  - destruct (x € vars_set_atom t) eqn:Ht.
    + apply vars_set_atom_cons in H. apply IHt in H.
      apply (set_add_mem_true string_dec) in Ht.
      rewrite Ht. assumption.
    + apply set_add_mem_false in Ht. rewrite Ht.
      assert (H': incl (vars_set_atom ((x & k) :: t)) W) by assumption.
      apply vars_set_atom_cons in H. apply IHt in H. rewrite map_app.
      assert (map (fun x0: string => x0 € W) [x] = [x € W]) by reflexivity.
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
  incl (vars_clause (s ~> (x & k))) W -> In x W.
Proof.
  intros. induction W as [|h t];
  apply H; apply vars_clause_In_conc.
Qed.

Lemma vars_clause_incl_vars_set_atom (s : set Atom) (W : set string) (x : string) (k : nat) :
  incl (vars_clause (s ~> (x & k))) W -> incl (vars_set_atom s) W.
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

(* ---------- GEQ ---------- *)

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

(* ---------- MODEL & SUB_MODEL ---------- *)

Fixpoint model (Cs : set Clause) (f : Frontier) : bool :=
  match Cs with
  | []      => true
  | h :: t  => all_shifts_true h f && model t f
  end.

Fixpoint sub_model (Cs : set Clause) (V W : set string) (f : Frontier) : bool :=
  match Cs with
  | []      => true
  | (l ~> (x & k)) :: t  =>
      (negb (x € W) ||
       negb (fold_right andb true (map (fun x => x € V) (vars_set_atom l))) ||
       all_shifts_true (l ~> (x & k)) f
      ) && sub_model t V W f
  end.

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
    + simpl. destruct (x € W) eqn:Hxw; try reflexivity.
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
      assert ((x € Y') = true).
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
    + destruct (x € Y) eqn:HxY; destruct (x € Y') eqn:HxY'; try reflexivity.
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
  rewrite IHt. assert ((negb (x € V)) = (negb (x € nodup string_dec V))).
  - destruct V; try reflexivity.
    simpl. destruct (string_dec x s); destruct (in_dec string_dec s V).
    + simpl. symmetry. apply negb_false_iff. apply (set_mem_correct2 string_dec).
      rewrite <- (nodup_In string_dec) in i. subst. assumption.
    + simpl. subst. destruct (string_dec s s); try reflexivity.
      contradiction.
    + apply negb_iff. destruct (x € V) eqn:HxV; symmetry.
      * apply set_mem_correct2. unfold set_In. apply set_mem_correct1 in HxV.
        unfold set_In in HxV. rewrite nodup_In. assumption.
      * apply set_mem_complete2. unfold set_In. apply set_mem_complete1 in HxV.
        unfold set_In in HxV. rewrite nodup_In. assumption.
    + simpl. destruct (string_dec x s); subst; try contradiction.
      apply negb_iff. destruct (x € V) eqn:HxV; symmetry.
      * apply set_mem_correct2. unfold set_In. apply set_mem_correct1 in HxV.
        unfold set_In in HxV. rewrite nodup_In. assumption.
      * apply set_mem_complete2. unfold set_In. apply set_mem_complete1 in HxV.
        unfold set_In in HxV. rewrite nodup_In. assumption.
  - rewrite H. assert (incl V (nodup string_dec V)).
    apply nodup_incl. apply incl_refl.
    assert (negb (fold_right andb true (map (fun x0 : string => x0 € nodup string_dec V) (vars_set_atom l))) = (negb (fold_right andb true (map (fun x : string => x € V) (vars_set_atom l))))).
    + destruct (negb (fold_right andb true (map (fun x0 : string => x0 € nodup string_dec V) (vars_set_atom l)))) eqn:HndV.
      * symmetry. apply negb_true_iff. apply negb_true_iff in HndV.
        eapply incl_fold_right_andb_false. apply H0. assumption.
      * symmetry. rewrite negb_false_iff in *.
        eapply incl_fold_right_andb_true. assert (incl (nodup string_dec V) V).
        rewrite <- (nodup_incl string_dec). apply incl_refl. apply H1.
        assumption.
    + rewrite H1. reflexivity.
Qed.

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

(* ---------- VARS_IMPROVABLE ---------- *)

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

(* ---------- FORWARD ---------- *)

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


(* ---------- EX_LFP_GEQ ---------- *)

Definition ex_lfp_geq (Cs : set Clause) (V W : set string) (f : Frontier) : Prop :=
  exists g, geq V g f = true /\ sub_model Cs V W g = true.

Lemma ex_lfp_geq_incl (Cs : set Clause) (V W : set string) :
  incl V W ->
  forall f, ex_lfp_geq Cs W W f -> ex_lfp_geq Cs V V f.
Proof.
  intros. unfold ex_lfp_geq in *.
  destruct H0 as [g [Hg1 Hg2]].
  exists g. split.
  - apply geq_incl with W; assumption.
  - apply (sub_model_monotone Cs g V W V W); assumption.
Qed.

Lemma ex_lfp_geq_monotone (Cs : set Clause) (V : set string) (f g : Frontier) :
  ex_lfp_geq Cs V V f -> geq V f g = true -> ex_lfp_geq Cs V V g.
Proof.
  intros. elim H. intros. destruct H1.
  unfold ex_lfp_geq. exists x. split;
  try assumption. eapply geq_trans.
  apply H1. apply H0.
Qed.

Lemma ex_lfp_geq_nodup_iff
  {A : Type}
  (Cs : set Clause)
  (V : set string)
  (f : Frontier) :
    ex_lfp_geq Cs V V f <->
    ex_lfp_geq Cs (nodup string_dec V) (nodup string_dec V) f.
Proof.
  split; intros.
  - unfold ex_lfp_geq in *. setoid_rewrite sub_model_nodup in H.
    setoid_rewrite geq_nodup_true_iff in H. assumption.
  - unfold ex_lfp_geq in *. setoid_rewrite sub_model_nodup.
    setoid_rewrite geq_nodup_true_iff. assumption.
Qed.

(* ---------- PRED_P ---------- *)

Definition pred_P (Cs : set Clause) (n m : nat) : Prop :=
  forall f, forall V W, incl W V ->
  Datatypes.length V <= n ->
  Datatypes.length (set_diff string_dec V W) <= m <= n ->
  ex_lfp_geq Cs W W f -> ex_lfp_geq Cs V V f.

Lemma pred_P_downward (Cs : set Clause) :
  forall n m n' m', pred_P Cs n m ->
  n' <= n -> m' <= m -> pred_P Cs n' m'.
Proof.
Admitted.

(* --------- MAIN THEOREMS ---------- *)

Definition lem_xx (Cs : set Clause) (V W : set string) (f : Frontier) :
  (* subject to change *)
  incl W V -> ex_lfp_geq Cs W W f -> ex_lfp_geq Cs V W f.
Proof.
Admitted.

(* should this work??? *)

Theorem thm_xx' (Cs : set Clause) :
  forall n m, pred_P Cs n m.
Proof.
  unfold pred_P. unfold ex_lfp_geq. intros.
  exists frontier_infty. split.
  - apply geq_infty.
  - apply sub_model_infty.
Qed.

Lemma set_diff_In_cons {A : Type} (dec : forall x y, {x = y} + {x <> y}) (h : A) (t V : set A) :
  In h t -> set_diff dec (h :: t) V = set_diff dec t V.
Proof.
  intros. simpl. destruct (set_mem dec h V) eqn:Hmem;
  try reflexivity. apply set_mem_complete1 in Hmem.
  unfold set_In in Hmem. assert (In h t /\ ~ In h V). 
  { split; assumption. } rewrite <- set_diff_iff in H0.
  apply (set_add_In dec) in H0. rewrite H0. reflexivity.
Qed.

Lemma set_diff_succ {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (V W : set A) (n : nat) :
  incl W V ->
  Datatypes.length (set_diff dec V W) = S n ->
  S (Datatypes.length (nodup dec W)) <= Datatypes.length (nodup dec V).
Proof.
  intros. induction W as [|h t].
  - simpl in *.
Admitted.

Theorem thm_xx (Cs : set Clause) :
  forall n m, pred_P Cs n m.
Proof.
  induction n as [|n IHn].
  - intros. unfold pred_P. intros. unfold ex_lfp_geq in *.
    exists f. split. apply geq_refl. apply le_0_r in H0.
    apply length_zero_iff_nil in H0. rewrite H0.
    apply sub_model_W_empty.
  - induction m as [|m IHm].
    + unfold pred_P in *. intros. apply (ex_lfp_geq_incl Cs V W);
      try assumption. destruct H1. apply le_0_r in H1.
      apply length_zero_iff_nil in H1.
      apply set_diff_nil_incl in H1. assumption.
    + unfold pred_P in *. intros.
      inversion H1. apply le_lteq in H3. destruct H3.
      * apply (IHm f V W); try assumption. lia.
      * rewrite (@ex_lfp_geq_nodup_iff string) in H2.
        assert (ex_lfp_geq Cs (nodup string_dec W) (nodup string_dec W) f).
         -- apply (IHn n f (nodup string_dec W) []);
            try assumption; try apply incl_nil_l.
            ++ eapply (set_diff_succ string_dec) in H.
               ** apply succ_le_mono. eapply le_trans.
                  apply H. assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
                  --- eapply NoDup_incl_length. apply NoDup_nodup.
                      rewrite <- nodup_incl2. apply incl_refl.
                  --- eapply le_trans in H0. apply H0. assumption.
               ** apply H3.
            ++ rewrite set_diff_nil. eapply (set_diff_succ string_dec) in H.
               ** split; try lia. apply succ_le_mono. eapply le_trans.
                  apply H. assert (Datatypes.length (nodup string_dec V) <= Datatypes.length V).
                  --- eapply NoDup_incl_length. apply NoDup_nodup.
                      rewrite <- nodup_incl2. apply incl_refl.
                  --- eapply le_trans in H0. apply H0. assumption.
               ** apply H3.
           ++ unfold ex_lfp_geq. exists f. split.
              apply geq_refl. apply sub_model_W_empty.
         -- assert (H': incl W V) by assumption.
            apply (nodup_incl2 string_dec) in H.
            apply (lem_xx Cs V (nodup string_dec W) f) in H;
            try assumption. elim H. intros h [H8 H9].
            destruct (sub_forward Cs V V h) as [U h'] eqn:Hforward.
            assert (sub_forward Cs V V h = (U, h')) by assumption.
            assert (sub_forward Cs V V h = (U, h')) by assumption.
            inversion Hforward. apply sub_forward_incl in Hforward.
            destruct U as [|u U'] eqn:Hu.
            ++ subst. apply sub_forward_empty in H6.
               destruct H6. unfold ex_lfp_geq. exists h. split;
               try assumption.
            ++ destruct (list_eq_dec string_dec V (set_union string_dec W U)).
               ** rewrite e. unfold ex_lfp_geq. exists frontier_infty. split.
                  --- apply geq_infty.
                  --- apply sub_model_infty.
                 --- assert (Datatypes.length (set_union string_dec W U) < Datatypes.length (nodup string_dec V)).
                     admit.
                     assert (Datatypes.length (set_diff string_dec V (set_union string_dec W U)) < Datatypes.length (set_diff string_dec V W) <= S m).
                     admit.
                     apply (ex_lfp_geq_monotone Cs V h' f).
                     eapply (IHm h' V (set_union string_dec W U)).
                     ++++ (* H11 *) admit.
                     ++++ assumption.
                     ++++ lia.
                     ++++ apply (IHn n h' (set_union string_dec W U) []).
                          **** apply incl_nil_l.
                          **** apply Arith_prebase.lt_le_S_stt in H11.
                               symmetry in Hu. subst.
                               subst.
                               
                               
                               (* use H0 and H11 + lemma about nodup & length *) admit.
                          **** (* same as above *)  admit.
                          **** unfold ex_lfp_geq. exists h'.
                               split. apply geq_refl.
                               apply sub_model_W_empty.
                     ++++ eapply geq_trans with h; try assumption.
                          apply sub_forward_geq in H10.
Admitted.

Theorem pre_thm32 (Cs : set Clause) (n : nat) (m : nat) (V : set string) :
  Datatypes.length V <= n ->
  (forall f : Frontier,
    (forall W : set string, strict_subset W V ->
      Datatypes.length (set_diff string_dec V W) <= m ->
      forall g : Frontier, geq W g f = true ->
      (sub_model Cs W W g = true) -> exists h, geq W h g = true /\ sub_model Cs V W h = true)
(* main implication *) ->
    exists h : Frontier, geq V h f = true /\ sub_model Cs (vars Cs) V h = true).
Proof.
  intros. induction n.
  - exists f. apply le_0_r in H.
    apply length_zero_iff_nil in H. rewrite H.
    split; try reflexivity. apply sub_model_W_empty.
  - destruct (sub_forward Cs V V f) as [W g] eqn:Hforward.
    apply (sub_forward_incl Cs f) in Hforward.
Admitted.

Theorem thm32 (Cs : set Clause) (f : Frontier) :
  exists h : Frontier,
    geq (vars Cs) h f = true /\ model Cs h = true.
Proof.
  intros. setoid_rewrite <- sub_model_eq_model;
  try apply incl_refl.
  apply (pre_thm32 Cs (List.length (vars Cs)) 0 (vars Cs)).
  intros; try reflexivity; try apply incl_refl.
  intros. exists g. split. apply geq_refl.
  apply le_0_r in H0. apply length_zero_iff_nil in H0.
  unfold strict_subset in H. destruct H as [H H'].
  apply set_diff_nil_incl in H0. contradiction.
Qed.

Lemma lem33 (Cs : set Clause) (W : set string) :
  let V := vars Cs in
  let V_m_W := set_diff string_dec V W in
  strict_subset W V ->
  forall f : Frontier, exists g : Frontier, (geq W g f) && sub_model Cs W W g = true ->
  forall f : Frontier, (forall v : string, (v € V_m_W) = true -> is_infty (f v) = true) ->
  exists h : Frontier, (forall v : string, (v € V_m_W) = true -> (h v) = (f v)) /\
  geq V h f = true /\ sub_model Cs (vars Cs) W h = true.
Proof.
Admitted.
