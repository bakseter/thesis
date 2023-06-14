From Coq Require Import Strings.String.
From Coq Require Import Lia.

(* Misc. lemmas and definitions *)

Module Misc.

  Lemma eq_sym_iff : forall (A : Type) (x y : A),
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

  Lemma le_n_Sm_pred_n_m (n m : nat) :
    n <= S m -> pred n <= m.
  Proof. induction n; lia. Qed.

  Lemma tuple_destruct {A B : Type} (a a' : A) (b b' : B) :
    a = a' ->
    b = b' ->
    (a, b) = (a', b').
  Proof. intros. subst. reflexivity. Qed.

End Misc.
