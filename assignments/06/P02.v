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
  intros A beq H l1 l2. generalize dependent l2.
  induction l1 as [| h1 l1' IHl1']; induction l2 as [| h2 l2' IHl2'].
  - simpl. split; auto.
  - simpl. split; intros Hcontra; inversion Hcontra.
  - simpl. split; intros Hcontra; inversion Hcontra.
  - simpl. split; intros; destruct (beq h1 h2) eqn: Hbeq.
    + apply H in Hbeq. apply IHl1' in H0. subst. reflexivity.
    + inversion H0. 
    + apply H in Hbeq. apply IHl1'. subst. inversion H0. reflexivity.
    + inversion H0. subst. rewrite <- Hbeq. apply H. reflexivity.
Qed.
