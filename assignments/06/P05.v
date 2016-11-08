Require Export P04.



(** **** Exercise: 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn. assumption.
  simpl. constructor. apply IHHn.
Qed.


