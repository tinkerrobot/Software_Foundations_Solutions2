Require Export P02.



(** It is a theorem of classical logic that the following two
    assertions are equivalent:

    ~ (exists x, ~ P x)
    forall x, P x

    The [dist_not_exists] theorem above proves one side of this
    equivalence. Interestingly, the other direction cannot be proved
    in constructive logic. Your job is to show that it is implied by
    the excluded middle. *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle. intros ex X f H x. unfold not in H. unfold not in ex.
  destruct (ex (f x)) as [H1 | H2]. apply H1. destruct H. exists x. apply H2.
Qed.


