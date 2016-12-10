Require Export P05.



(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)
Hint Constructors cstep.
Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==> c' / st'.
Proof.
  remember (aexp_strong_progress) as HA.
  remember (bexp_strong_progress) as HB.
  intros c st. induction c; try eauto; right.
  try destruct (HA st a) as [HA'|HA']; try inversion HA'; subst; eauto.
  try destruct IHc1 as [Hc1|Hc1]; try destruct IHc2 as [Hc2|Hc2]; try inversion Hc1; try inversion Hc2; try inversion H;
  subst; eauto.
  try destruct (HB st b) as [[HB'|HB']|HB']; try inversion HB'; subst; try eauto.
  try destruct IHc1 as [Hc1|Hc1]; try destruct IHc2 as [Hc2|Hc2]; try inversion Hc1; try inversion Hc2; try inversion H;
  subst; try inversion H0; eauto.
Qed.

