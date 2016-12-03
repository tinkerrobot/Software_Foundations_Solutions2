Require Export P11.



Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* BTrue and BFalse are immediate *)
    try reflexivity.
  - (* BEq *)
    rename a into a1. rename a0 into a2. simpl.
    remember (optimize_0plus_aexp a1) as a1' eqn:Heqa1'.
    remember (optimize_0plus_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- optimize_0plus_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- optimize_0plus_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
  - (* BLe *)
    rename a into a1. rename a0 into a2. simpl.
    remember (optimize_0plus_aexp a1) as a1' eqn:Heqa1'.
    remember (optimize_0plus_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- optimize_0plus_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
        (subst a2'; rewrite <- optimize_0plus_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
  - (* BNot *)
    simpl. remember (optimize_0plus_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (optimize_0plus_bexp b1) as b1' eqn:Heqb1'.
    remember (optimize_0plus_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.

