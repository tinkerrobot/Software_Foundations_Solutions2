Require Export D.




(** **** Problem #7 : 2 stars (split) *)
(** The function [split] is the right inverse of combine: it takes a
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)

Fixpoint add_prod {X Y : Type} (p : X * Y) (pl : list X * list Y) : list X * list Y
  := (cons (fst p) (fst pl), cons (snd p) (snd pl)).

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | h :: t => add_prod h (split t)
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Check @map.
Print map.

Theorem split_map: forall X Y (l: list (X*Y)),
   fst (split l) = map fst l.
Proof.
  intros X Y l. induction l as [| (a, b)].
  - reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.

