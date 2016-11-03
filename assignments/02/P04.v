Require Export P03.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.



(** **** Problem : 3 stars (mult_comm) *)

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_assoc. reflexivity.
Qed.

