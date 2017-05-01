Require Export P04.



(** **** Exercise: 3 stars, recommended (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.
  induction contra; inversion Heqloopdef.
  - (* WhileEnd *) rewrite H1 in H. inversion H.
  - (* WhileLoop *) subst. apply IHcontra2. assumption.
Qed.

