From Coq Require Import Strings.String.

(* Misc. lemmas and definitions *)

Module Misc.

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

End Misc.
