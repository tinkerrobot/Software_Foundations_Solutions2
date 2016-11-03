Require Export P03.

Theorem proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q H. inversion H. apply H0.
Qed.

Theorem proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q H. inversion H. apply H1.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - (* -> *) intros H. inversion H.
    + split.
      { left. apply H0. }
      { left. apply H0. }
    + split.
      { apply proj1 in H0. right. apply H0. }
      { apply proj2 in H0. right. apply H0. }
  - (* <- *) intros H. inversion H.
    + destruct H1.
      { left. apply H1. }
      { destruct H0.
        { left. apply H0. }
        { right. split.
          { apply H0. }
          { apply H1. } } }
Qed.
