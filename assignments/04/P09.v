Require Export P04.



Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
    intros X test x l lf H0.
    induction l.
    - inversion H0.
    - inversion H0. destruct (test x0) eqn:t0.
      + inversion H1. rewrite <- H2. apply t0.
      + rewrite H1 in IHl. apply IHl. reflexivity.
Qed.