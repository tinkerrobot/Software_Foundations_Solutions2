Require Export P07.

Theorem snoc_rev_relation : forall n : nat, forall l : natlist,
      rev (snoc l n) = n :: rev l.
Proof.
  intros n l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

(** Hint: You may need to first state and prove some lemma about snoc and rev. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l.
  - reflexivity.
  - simpl. rewrite -> snoc_rev_relation. rewrite -> IHl. reflexivity.
Qed.

