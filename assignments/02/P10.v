Require Export P09.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2. induction l1.
  - simpl. rewrite -> app_nil_end. reflexivity.
  - simpl. rewrite -> snoc_append. rewrite -> snoc_append. rewrite -> IHl1. rewrite <- app_assoc. reflexivity.
Qed.

