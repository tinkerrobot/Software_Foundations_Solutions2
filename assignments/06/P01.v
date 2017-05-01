Require Export D.

Lemma evenb_S : forall n,
    evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - rewrite IHn'. simpl. destruct (evenb n') eqn:Heq.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma evenb_double_true : forall n,
    evenb (double n) = true.
Proof.
  intros n. induction n.
  - reflexivity.
  - assumption.
Qed.
    
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros. induction n.
  - simpl. exists 0. reflexivity.
  - destruct evenb.
    + destruct IHn. subst. exists x. rewrite evenb_S. rewrite evenb_double_true. reflexivity.
    + destruct IHn. subst. exists (S x). simpl. rewrite evenb_double_true. reflexivity.
Qed.
