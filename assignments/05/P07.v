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
        - apply H1.
        - simpl. left. reflexivity. }
      { apply IHl' in H2. destruct H2 as [x2 H2]. exists x2. split.
        - apply proj1 in H2. apply H2.
        - simpl. right. apply proj2 in H2. apply H2. }
  - (* <- *) intros H. induction l as [| x' l' IHl'].
    + (* l = [] *)
      simpl in H. destruct H as [x' H]. apply proj2 in H. contradiction.
    + (* l = x' :: l' *)
      simpl. simpl in H. destruct H as [x'' H]. inversion H. destruct H1 as [H2 | H3].
      { left. rewrite H2. apply H0. }
      { right. apply IHl'. exists x''. split.
        - apply H0.
        - apply H3. }
Qed.
