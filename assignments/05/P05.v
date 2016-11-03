Require Export P04.



Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P Hall Hexist.
  destruct Hexist as [x HPnot].
  unfold not in HPnot. apply HPnot. apply Hall.
Qed.

