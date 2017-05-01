Require Export P01.



(** **** Exercise: 3 stars, recommended (t_update_permute)  *)
(** Use [beq_idP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n. induction n.
  - intros m. simpl. destruct m.
    + reflexivity.
    + intros H. inversion H.
  - intros m. simpl. induction m.
    + intros H. inversion H.
    + intros H. apply IHn in H. rewrite H. reflexivity.
Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  intros x y. unfold not. split.
  - (* -> *) intros H0 H1. apply beq_nat_true_iff in H1. rewrite H1 in H0. inversion H0.
  - (* <- *) intros H. induction x as [| x'].
    + induction y as [| y'].
      { exfalso. apply H. reflexivity. }
      { generalize dependent y'. auto. }
    + induction y as [| y'].
      { generalize dependent x'. auto. }
      { simpl. destruct (beq_nat x' y') eqn:Heq.
        - exfalso. apply H. apply f_equal. apply beq_nat_true_iff. apply Heq.
        - reflexivity. }
Qed.

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
   intros [n1] [n2].
   unfold beq_id.
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.  Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *) intros H. rewrite H. intros H'. inversion H'.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros. unfold t_update. apply functional_extensionality.
  intros x. destruct (beq_id x1 x) eqn: H1.
  - apply beq_id_true_iff in H1. rewrite <- H1. rewrite <- beq_id_false_iff in H.
    rewrite H. reflexivity.
  - reflexivity.
Qed.