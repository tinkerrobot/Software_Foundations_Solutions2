Require Export P09.

Lemma WHILE_true_nonterm : forall b c st st',
     bequiv b BTrue ->
     ~( (WHILE b DO c END) / st \\ st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember (WHILE b DO c END) as cw eqn:Heqcw.
  induction H;
    (* Most rules don't apply, and we can rule them out
       by inversion *)
    inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for WHILE loops: *)
  - (* E_WhileEnd *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. inversion H.
  - (* E_WhileLoop *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof.
  intros b c Hb st st'.
  split; intros H; apply WHILE_true_nonterm in H; try contradiction.
  - (* -> *) assumption.
  - (* -> *) unfold bequiv. reflexivity.
Qed.    

Theorem WHILE_false : forall b c,
     bequiv b BFalse ->
     cequiv
       (WHILE b DO c END)
       SKIP.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H; subst.
    + (* E_WhileEnd *)
      apply E_Skip.
    + (* E_WhileLoop *)
      rewrite Hb in H2. inversion H2.
  - (* <- *)
    inversion H; subst.
    apply E_WhileEnd.
    rewrite Hb.
    reflexivity.  Qed.

(** **** Exercise: 3 stars (fold_constants_com_sound)  *)
(** Complete the [WHILE] case of the following proof. *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* SKIP *) apply refl_cequiv.
  - (* ::= *) apply CAss_congruence.
              apply fold_constants_aexp_sound.
  - (* ;; *) apply CSeq_congruence; assumption.
  - (* IFB *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).

      (** (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)

    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply IFB_true; assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply IFB_false; assumption.
  - (* WHILE *)
    assert (bequiv b (fold_constants_bexp b)). { apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CWhile_congruence; assumption).    
    + (* b always true *)
      apply WHILE_true. assumption.
    + (* b always false *)
      apply WHILE_false. assumption.
Qed.

