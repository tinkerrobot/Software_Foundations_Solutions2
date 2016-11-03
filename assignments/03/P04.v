Require Export P03.



Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v. induction l1.
  - reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

