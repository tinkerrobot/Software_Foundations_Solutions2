Require Export D.



(** **** Exercise: 2 stars, optional (t_update_shadow)  *)
(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity. Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros A m x v. unfold t_update.
  rewrite <- beq_id_refl. reflexivity. Qed.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros A m v1 v2 x. apply functional_extensionality_dep.
  induction x. induction n.
  - intros x'. destruct x' as [n']. induction n'.
    + apply t_update_eq.
    + unfold t_update. simpl. reflexivity.
  - intros x'. destruct x' as [n']. induction n'.
    + unfold t_update. simpl. reflexivity.
    + unfold t_update. simpl. destruct (beq_nat n n') eqn: H.
      * reflexivity.
      * reflexivity.
Qed.

