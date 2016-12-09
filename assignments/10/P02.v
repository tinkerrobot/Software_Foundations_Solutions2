Require Export P01.



(** **** Exercise: 3 stars (step__eval)  *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' \\ n ->
     t \\ n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs; intros n Hn; inversion Hn; subst.
  - apply E_Plus; apply E_Const.
  - apply E_Plus. apply IHHs. assumption. assumption.
  - apply E_Plus. assumption. apply IHHs. assumption.
Qed.

