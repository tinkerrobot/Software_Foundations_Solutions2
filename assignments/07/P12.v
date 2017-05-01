Require Export P11.



Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b; simpl;
    try reflexivity;
    try (rewrite <- optimize_0plus_aexp_sound; rewrite <- optimize_0plus_aexp_sound; reflexivity).
  - (* BNot *) rewrite IHb. reflexivity.
  - (* BAnd *) rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

