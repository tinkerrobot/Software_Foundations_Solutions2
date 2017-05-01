Require Export P02.



(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  induction t.
    - (* C *) left. apply v_const.
    - (* P *) right. inversion IHt1.
      + (* l *) inversion IHt2.
        * (* l *) inversion H. inversion H0.
          exists (C (n + n0)).
          apply ST_PlusConstConst.
        * (* r *) inversion H0 as [t' H1].
          exists (P t1 t').
          inversion H. subst. apply ST_Plus2. apply H1.
      + (* r *) inversion H as [t' H0].
          exists (P t' t2).
          apply ST_Plus1. apply H0.  Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
  { (* Proof of assertion *) apply strong_progress. }
  inversion G.
    + (* l *) apply H0.
    + (* r *) exfalso. apply H. assumption.  Qed.

Hint Constructors eval.

(** **** Exercise: 3 stars (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t \\ n.
Proof.
  intros t t' [H Hnf]. apply nf_is_value in Hnf.
  inversion Hnf. eexists. split.
  - reflexivity.
  - induction H; subst.
    + eauto.
    + eapply step__eval. apply H. apply IHmulti. assumption. reflexivity.
Qed.          

