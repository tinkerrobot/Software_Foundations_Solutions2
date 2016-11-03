Require Export D.



(** **** Problem #13 : 3 stars (apply_exercise1)  *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l. induction l.
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.
  
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1.
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.

