Require Export P06.



(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof.
  unfold cequiv.
  intros.
  split; intros.
  - (* -> *)
    inversion H1. subst. apply H in H4. apply H0 in H7. apply E_Seq with st'0.
    + assumption.
    + assumption.
  - (* <- *)
    inversion H1. subst. apply H in H4. apply H0 in H7. apply E_Seq with st'0.
    + assumption.
    + assumption.
Qed.