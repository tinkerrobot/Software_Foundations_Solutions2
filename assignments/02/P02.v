Require Export P01.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. 
  intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

