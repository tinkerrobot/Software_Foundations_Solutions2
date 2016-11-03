Require Export P01.



Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  y = z.
Proof.
  intros X x y z l j H0 H1.
  inversion H0. inversion H1. apply H2.
Qed.

