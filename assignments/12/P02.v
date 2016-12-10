Require Export P01.



Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T He Hs. intros [Hn Hv].
  induction Hs. destruct (progress x T He). 
  - apply Hv in H. destruct H.
  - apply Hn in H. destruct H.
  - apply IHHs; eauto. eapply preservation. apply He. apply H.
Qed.

