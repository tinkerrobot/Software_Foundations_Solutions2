Require Export P01.



(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{ c = 0 + 0 + c }}
  X ::= 0;;
    {{ c = X + 0 + c }}
  Y ::= 0;;
    {{ c = X + Y + c }}
  Z ::= c;;
    {{ Z = X + Y + c }}
  WHILE X <> a DO
      {{ Z = X + Y + c /\ X <> a }} ->>
      {{ (Z+1) = (X+1) + Y + c }}
    X ::= X + 1;;
      {{ (Z+1) = X + Y + c }}
    Z ::= Z + 1
      {{ Z = X + Y + c }}
  END;;
    {{ Z = X + Y + c /\ X = a }} ->>
    {{ Z = a + Y + c }}
  WHILE Y <> b DO
      {{ Z = a + Y + c /\ Y <> b }} ->>
      {{ (Z+1) = a + (Y+1) + c }}
    Y ::= Y + 1;;
      {{ (Z+1) = a + Y + c }}
    Z ::= Z + 1
      {{ Z = a + Y + c }}
  END
    {{ Z = a + Y + c /\ Y = b }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros a b c.
  apply hoare_consequence with (P' := fun st => c = c) (Q' := fun st => st Z = a + st Y + c /\ st Y = b).
  - apply hoare_seq with (Q := fun st => c = st X + c).
    apply hoare_seq with (Q := fun st => c = st X + st Y + c).
    apply hoare_seq with (Q := fun st => st Z = st X + st Y + c).
    apply hoare_seq with (Q := fun st => st Z = a + st Y + c).
    * eapply hoare_consequence_post. apply hoare_while.
      { apply hoare_consequence_pre with (P' := fun st => st Z + 1 = a + (st Y + 1) + c).
        - apply hoare_seq with (Q := fun st => st Z + 1 = a + st Y + c).
          + eapply hoare_consequence_pre. eapply hoare_asgn.
            unfold assert_implies, assn_sub. intros. simpl.
            rewrite t_update_eq. rewrite t_update_neq. assumption.
            unfold not. intros. inversion H0.
          + eapply hoare_consequence_pre. eapply hoare_asgn.
            unfold assert_implies, assn_sub. intros. simpl.
            rewrite t_update_eq. rewrite t_update_neq. assumption.
            unfold not. intros. inversion H0.
        - unfold assert_implies. intros st [H HY]. omega. }
      { unfold assert_implies. intros st [H HY]. split.
        - assumption.
        - unfold not, bassn in HY. simpl in HY. rewrite negb_true_iff in HY.
          apply eq_false_true_abs in HY. apply beq_nat_true in HY. assumption. }
    * eapply hoare_consequence_post. apply hoare_while.
      { apply hoare_consequence_pre with (P' := fun st => st Z + 1 = (st X + 1) + st Y + c).
        - apply hoare_seq with (Q := fun st => st Z + 1 = st X + st Y + c).
          + unfold hoare_triple. intros st st' HZ H. inversion HZ. subst. simpl.
            rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_neq. assumption.
            unfold not. intros Hcontra. inversion Hcontra.
            unfold not. intros Hcontra. inversion Hcontra.
          + unfold hoare_triple. intros st st' HX H. inversion HX. subst. simpl.
            rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_neq. assumption.
            unfold not. intros Hcontra. inversion Hcontra.
            unfold not. intros Hcontra. inversion Hcontra.
        - unfold assert_implies. intros st [H HX]. omega. }
      { unfold assert_implies. intros st [H HX].
        unfold not, bassn in HX. simpl in HX. rewrite negb_true_iff in HX.
        apply eq_false_true_abs in HX. apply beq_nat_true in HX. omega. }
    * unfold hoare_triple. intros st st' HZ H. inversion HZ. subst n x a1 st0 st'. simpl.
      rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_neq. assumption.
      unfold not. intros Hcontra. inversion Hcontra.
      unfold not. intros Hcontra. inversion Hcontra.
    * unfold hoare_triple. intros st st' HY H. inversion HY. subst n x a1 st0 st'. simpl.
      rewrite t_update_eq. rewrite t_update_neq. omega.
      unfold not. intros Hcontra. inversion Hcontra.
    * unfold hoare_triple. intros st st' HX H. inversion HX. subst. reflexivity.
  - unfold assert_implies. intros. reflexivity.
  - unfold assert_implies. intros st [H HY]. rewrite <- HY. assumption.
Qed.