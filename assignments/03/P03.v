Require Export P02.



Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  intros X l. reflexivity.
Qed.

