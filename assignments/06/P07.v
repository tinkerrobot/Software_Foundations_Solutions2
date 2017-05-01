Require Export P06.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt. intros n1 n2 m H. induction H.
  - split.
    + apply le_n_S. induction n1.
      * simpl. apply le_0_n.
      * simpl. apply le_n_S. assumption.
    + apply le_n_S. induction n1.
      * simpl. apply le_n.
      * simpl. apply le_S. assumption.
  - destruct IHle. split.
    + apply le_S. assumption.
    + apply le_S. assumption.
Qed.      