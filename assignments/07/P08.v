Require Export P07.



(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI)
         (IFB b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv,cequiv.
  intros b b' c1 c1' c2 c2' Hbe Hc1e Hc2e st st'.
  split; intros H.
  - (* -> *)
    remember (IFB b THEN c1 ELSE c2 FI) as cif
      eqn:Heqcif.
    induction H; inversion Heqcif; subst.
    + (* IfTrue *) apply E_IfTrue.
      * rewrite <- (Hbe st). assumption.
      * apply Hc1e. assumption.
    + (* IfFalse *) apply E_IfFalse.
      * rewrite <- (Hbe st). assumption.
      * apply Hc2e. assumption.
  - (* <- *)
    remember (IFB b' THEN c1' ELSE c2' FI) as cif
      eqn:Heqcif.
    induction H; inversion Heqcif; subst.
    + (* IfTrue *) apply E_IfTrue.
      * rewrite (Hbe st). assumption.
      * apply Hc1e. assumption.
    + (* IfFalse *) apply E_IfFalse.
      * rewrite (Hbe st). assumption.
      * apply Hc2e. assumption.
Qed.

