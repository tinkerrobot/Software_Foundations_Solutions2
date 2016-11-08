Require Export P03.



(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.

    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)

Theorem excluded_middle_to_double_negation_elimination:
  excluded_middle -> double_negation_elimination.
Proof.
  unfold excluded_middle. unfold double_negation_elimination.
  intros ex P neg. unfold not in neg. destruct (ex P).
  - apply H.
  - unfold not in H. apply neg in H. contradiction.
Qed.

Theorem double_negation_elimination_to_excluded_middle:
  double_negation_elimination -> excluded_middle.
Proof.
  unfold excluded_middle. unfold double_negation_elimination.
  intros double_neg P'. unfold not. unfold not in double_neg.
  apply double_neg. intros H. apply H.  right. intros H'. apply H. left. apply H'.
Qed.