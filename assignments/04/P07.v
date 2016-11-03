Require Export P02.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m H. simpl in H. destruct m.
    + reflexivity.
    + inversion H.
  - intros m H. simpl in H. destruct m.
    + inversion H.
    + symmetry in H. rewrite <- plus_n_Sm in H. apply S_injective in H.
      rewrite <- plus_n_Sm in H. rewrite -> plus_comm in H. rewrite <- plus_n_Sm in H.
      apply S_injective in H. symmetry in H. apply IHn' in H. rewrite H. reflexivity.
Qed.
