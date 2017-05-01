Require Export P05.



(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
 *)

Hint Constructors aval.
Hint Constructors cstep.


Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==> c' / st'.
Proof.
  intros c st. induction c.
  - eauto.
  - right. destruct (aexp_strong_progress st a).
    + destruct H. subst. eauto.
    + destruct H. subst. eauto.
  - right. destruct IHc1; destruct IHc2; subst; eauto; destruct H; destruct H; eauto.
  - destruct (bexp_strong_progress st b); destruct H; subst; eauto.
  - destruct IHc; subst; eauto.
  - destruct IHc1; destruct IHc2; subst; eauto.
    + destruct H0. destruct H. eauto.
    + destruct H. destruct H. eauto.
    + destruct H. destruct H. eauto.
Qed.

