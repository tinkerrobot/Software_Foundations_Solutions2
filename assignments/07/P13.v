Require Export P12.



Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply optimize_0plus_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (optimize_0plus_bexp b)). {
      apply optimize_0plus_bexp_sound. }
    destruct (optimize_0plus_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
  - (* WHILE *)
    assert (bequiv b (optimize_0plus_bexp b)). {
      apply optimize_0plus_bexp_sound. }
    destruct (optimize_0plus_bexp b) eqn:Heqb;
      try (apply CWhile_congruence; assumption). Qed.
