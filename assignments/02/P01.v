Require Export D.

Theorem  plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  intros n m. induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof. 
  intros n m. induction n.
  - rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.