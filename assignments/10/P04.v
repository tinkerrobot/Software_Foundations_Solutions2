Require Export P03.

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
 *)

Hint Constructors aval.
Hint Constructors astep.

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
  intros st a;
  induction a; eauto; destruct IHa1; destruct IHa2; destruct H; destruct H0; subst; eauto.      
Qed.

