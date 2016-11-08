Require Export P06.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H. apply le_n. apply le_S. apply IHle.
Qed.

Lemma plus_Sn_m : forall n m,
    S n + m = S (n + m).
Proof.
  intros n m. reflexivity.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m H. 
  split.
  - induction H.
   + apply n_le_m__Sn_le_Sm. induction n1.
     { simpl. induction n2.
       - auto.
       - apply le_S. apply IHn2. }
     { rewrite plus_Sn_m. apply n_le_m__Sn_le_Sm. apply IHn1. }
   + apply le_S. apply IHle.
  - induction H.
    + apply n_le_m__Sn_le_Sm. induction n1.
      { simpl. apply le_n. }
      { rewrite plus_Sn_m. apply le_S. apply IHn1. }
    + apply le_S. apply IHle.
Qed.
