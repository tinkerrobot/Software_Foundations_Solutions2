Require Export P02.

(** **** Problem #3 : 2 stars (mult_S_1) *)
Theorem mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  simpl.
  rewrite -> H.
  reflexivity.
Qed.

(*-- Check --*)

Check mult_S_1 : forall n m : nat,
  m = S n -> 
  m * (1 + n) = m * m.