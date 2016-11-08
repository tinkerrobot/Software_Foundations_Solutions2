Require Export P01.



(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)

Fixpoint beq_list {A} (beq : A -> A -> bool)
         (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [] , [] => true
  | _  , [] => false
  | [] , _  => false
  | h1 :: t1 , h2 :: t2 => if(beq h1 h2) then beq_list beq t1 t2 else false
  end.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
  intros A beq H l1 l2. split.
  - (* -> *) generalize dependent l2. generalize dependent l1. intros l1. induction l1 as [| h1 l1' IHl1'].
    + induction l2 as [| h2 l2' IHl2'].
      { reflexivity. }
      { simpl. intros H1. inversion H1. }
    + induction l2 as [| h2 l2' IHl2'].
      { simpl. intros H1. inversion H1. }
      { simpl. intros H1. destruct (beq h1 h2) eqn:Heq.
        + apply H in Heq. rewrite <- Heq.
          assert (l1' = l2' -> h1 :: l1' = h1 :: l2') as H2.
          { intros H3. rewrite H3. reflexivity. } apply H2. apply IHl1'. apply H1.
        + inversion H1. }
  - (* <- *) generalize dependent l2. generalize dependent l1. intros l1. induction l1 as [| h1 l1' IHl1'].
    + induction l2 as [| h2 l2' IHl2'].
      { simpl. reflexivity. }
      { simpl. intros H1. inversion H1. }
    + induction l2 as [| h2 l2' IHl2'].
      { simpl. intros H1. inversion H1. }
      { simpl. intros H1. destruct (beq h1 h2) eqn:Heq.
        + apply IHl1'. apply H in Heq. rewrite Heq in H1.
          assert (h1 :: l1' = h1 :: l2' -> l1' = l2') as H2.
          { intros H3. inversion H1. reflexivity. } apply H2. rewrite Heq. apply H1.
        + inversion H1. apply H in H2. rewrite H2 in Heq. symmetry. apply Heq. }
Qed.

