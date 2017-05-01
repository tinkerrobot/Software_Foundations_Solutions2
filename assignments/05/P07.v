Require Export P06.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - (* -> *) intros H. induction l as [| x' l' IHl'].
    + (* l = [] *)
      simpl in H. contradiction.
    + (* l = x' :: l' *)
      simpl in H. destruct H as [H1 | H2].
      { exists x'. split.
        - assumption.
        - simpl. left. reflexivity. }
      { apply IHl' in H2. destruct H2 as [x2 H2]. exists x2. destruct H2. split.
        - assumption.
        - simpl. right. assumption. }
  - (* <- *) intros H. induction l as [| x' l' IHl'].
    + (* l = [] *)
      simpl in H. destruct H. destruct H. contradiction.
    + (* l = x' :: l' *)
      simpl. simpl in H. destruct H as [x'' H]. destruct H. destruct H0.
      { left. rewrite H0. assumption. }
      { right. apply IHl'. exists x''. split.
        - assumption.
        - assumption. }
Qed.
