Require Export P07.



(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l. split.
  - (* -> *) intros H. induction l.
    + simpl. auto.
    + simpl. split.
      { apply H. simpl. left. reflexivity. }
      { apply IHl. intros x0 H0. apply H. simpl. right. apply H0. }
  - (* <- *) intros H. induction l.
    + simpl. intros x0 H0. contradiction.
    + simpl. intros x0 H0. destruct H0 as [|H1 H2].
      { simpl in H. apply proj1 in H. rewrite H0 in H. apply H. }
      { simpl in H. apply proj2 in H. apply IHl with x0 in H. apply H. apply H1. }
Qed.