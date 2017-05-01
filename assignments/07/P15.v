Require Export P14.



(** **** Exercise: 3 stars, optional (inequiv_exercise)  *)
(** Prove that an infinite loop is not equivalent to [SKIP] *)

Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.
  induction contra; inversion Heqloopdef.
  - (* WhileEnd *) rewrite H1 in H. inversion H.
  - (* WhileLoop *) subst. contradiction.
Qed.

Theorem inequiv_exercise:
  ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
Proof.
  intro H.
  eapply loop_never_stops with empty_state empty_state.
  unfold loop. apply H. constructor.
Qed.