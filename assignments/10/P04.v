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
  induction a; try eauto;
  destruct IHa1; try destruct H; destruct IHa2; try destruct H0; try eauto;
  try subst; try eauto.
Qed.

