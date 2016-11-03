Require Export P04.

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool), 
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  rewrite -> x.
  rewrite -> x.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
