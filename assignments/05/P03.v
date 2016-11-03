Require Export P02.



Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HQnot.
  unfold not. unfold not in HQnot. intros P'. apply HQnot. apply H. apply P'.
Qed.

