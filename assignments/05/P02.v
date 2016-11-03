Require Export P01.

Lemma mult_0_l :
  forall n, 0 * n = 0.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Lemma mult_0_r :
  forall n, n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n].
  - intros m H. rewrite mult_0_l in H. left. apply H.
  - intros [|m].
    + intros H. rewrite mult_0_r in H. right. apply H.
    + intros H. inversion H.
Qed.
