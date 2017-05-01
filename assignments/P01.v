Require Export D.



(** **** Exercise: 4 stars (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

Lemma beq_id_refl : forall x,
    beq_id x x = true.
Proof.
  intros. unfold beq_id. simpl. induction x. induction n.
  - reflexivity.
  - simpl. assumption.  
Qed.

Theorem hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.
Proof.
  remember (t_update empty_state X 0) as st eqn: Heqst.
  remember (APlus (AId X) (ANum 1)) as X' eqn: HeqX'.
  remember (t_update st X (aeval st X')) as st' eqn: Heqst'.
  exists X'. intros H.
  assert (st' X = aeval st' X' -> False) as Hcontra.
  { subst. simpl. unfold t_update. rewrite beq_id_refl. intros H'. inversion H'. }
  apply Hcontra. eapply H.
  - rewrite Heqst'. apply E_Ass. reflexivity.
  - reflexivity.    
Qed.