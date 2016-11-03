Require Export P03.



Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros n X l. generalize dependent l. generalize dependent n.
  induction n.
  - destruct l.
    + reflexivity.
    + simpl. intros H. inversion H.
  - destruct l.
    + reflexivity.
    + simpl. intros H. apply IHn. inversion H. reflexivity.
Qed.
