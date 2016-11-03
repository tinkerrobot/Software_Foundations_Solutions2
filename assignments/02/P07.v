Require Export P06.



(** **** Problem #3 : 3 stars (list_exercises) *)
(** More practice with lists. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
  intros l. induction l as [| n l].
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.  

