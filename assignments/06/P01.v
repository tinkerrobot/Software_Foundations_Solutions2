Require Export D.

Lemma evenb_S : forall n,
    evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - rewrite IHn'. simpl. destruct (evenb n') eqn:Heq.
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma plus_n_Sm : forall n m,
        S (n + m) = n + S m.
Proof.
  intros n m. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma double_plus : forall n,
    double n = n + n.
Proof.
  intros n. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma plus_1_l : forall n,
    1 + n = S n.
Proof.
  intros n. reflexivity.
Qed.

Lemma plus_0_r : forall n,  
    n = n + 0.
Proof.
  intros n. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Lemma plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  - simpl. rewrite <- plus_0_r. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma plus_assoc : forall n m p : nat,
    n + (m + p) = n + m + p.
Proof.
  intros n m p. induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
    
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros n. induction n as [| n'].
  - simpl. exists 0. reflexivity.
  - destruct (evenb n') eqn: Heq.
    + rewrite evenb_S. rewrite Heq. simpl. destruct IHn' as [n'' IHn'].
      exists n''. rewrite IHn'. reflexivity.
    + rewrite evenb_S. rewrite Heq. simpl. destruct IHn' as [n'' IHn'].
      exists (n''+1). rewrite IHn'. rewrite double_plus. rewrite double_plus.
      rewrite plus_n_Sm. rewrite <- plus_1_l. rewrite <- plus_n_Sm. rewrite <- (plus_1_l (n'' + n'')).
      rewrite plus_comm. rewrite plus_assoc. rewrite (plus_comm 1).
      rewrite plus_assoc. reflexivity.
Qed.
