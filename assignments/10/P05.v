Require Export P04.



(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Hint Constructors aval.
Hint Constructors bstep.

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  intros st b.
  induction b; eauto; try (destruct (aexp_strong_progress st a); destruct (aexp_strong_progress st a0); destruct H; destruct H0; subst; eauto).
  - destruct IHb; destruct H; subst; eauto.
  - destruct IHb1; destruct IHb2; destruct H; destruct H0; subst; eauto. 
Qed.

