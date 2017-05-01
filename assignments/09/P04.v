Require Export P03.



(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  intros. unfold is_wp. split.
  - apply hoare_asgn.
  - unfold hoare_triple, assert_implies, assn_sub. intros.
    apply H with st. apply E_Ass. reflexivity. assumption.
Qed.

