Require Export P01.

Hint Constructors eval.

(** **** Exercise: 3 stars (step__eval)  *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' \\ n ->
     t \\ n.
Proof.
  intros t t' n Hs. generalize dependent n. 
  induction Hs; intros; inversion H; subst; eauto.
Qed.