Require Export P03.

(** **** Exercise: 3 stars, advanced (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for [X] = [2]
   (the latter is trickier than you might expect). *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity. Qed.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros A m x v. unfold t_update.
  rewrite <- beq_id_refl. reflexivity. Qed.

Definition pup_to_n : com := 
  (Y ::= (ANum 0) ;; (WHILE (BLe (ANum 1) (AId X))
                            DO (Y ::= (APlus (AId X) (AId Y)) ;; X ::= (AMinus (AId X) (ANum 1))) END)).

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  unfold pup_to_n. apply E_Seq with (t_update (t_update empty_state X 2) Y 0).
  - apply E_Ass. simpl. reflexivity.
  - apply E_WhileLoop with (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1).
    + simpl. reflexivity.
    + apply E_Seq with (t_update (t_update (t_update empty_state X 2) Y 0) Y 2).
      * apply E_Ass. simpl. rewrite t_update_eq. reflexivity.
      * apply E_Ass. simpl. reflexivity.
    + apply E_WhileLoop with (t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
      * simpl. reflexivity.
      * apply E_Seq with (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3).
        { apply E_Ass. simpl. rewrite t_update_shadow. rewrite t_update_permute.
          - rewrite t_update_eq. reflexivity.
          - unfold not. intros. inversion H. }
        { apply E_Ass. simpl. reflexivity. }
      * apply E_WhileEnd. simpl. reflexivity.
Qed.