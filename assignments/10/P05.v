Require Export P04.



(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)
Hint Constructors bstep.
Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  intros st b. induction b; eauto; right;
  try (destruct (aexp_strong_progress st a); destruct (aexp_strong_progress st a0);
  inversion H; inversion H0; subst; try eauto).
  try (destruct IHb as [[BT | BF] | [b' IB]]; try subst; try eauto).
  destruct IHb1 as [[ | ] | []]; destruct IHb2 as [[ | ] | []]; try subst; try eauto.
Qed.

