Require Export D.



(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros m.
  apply hoare_seq with (fun st => st Y * fact (st X) = fact m).
  eapply hoare_consequence_post. eapply hoare_while.
  - eapply hoare_seq. eapply hoare_asgn. eapply hoare_consequence_pre.
    apply hoare_asgn. unfold assert_implies. 
    intros st H. inversion H as [HI HB]. unfold assn_sub. simpl.
    repeat (rewrite t_update_eq). rewrite <- HI.
    rewrite t_update_neq; try apply beq_id_false_iff; try reflexivity.
    rewrite t_update_eq.
    rewrite t_update_neq; try apply beq_id_false_iff; try reflexivity.
    inversion HB. destruct (st X). inversion H1. simpl. rewrite <- minus_n_O.
    rewrite <- mult_assoc. rewrite Nat.mul_succ_l. rewrite Nat.add_comm. reflexivity.
  - unfold assert_implies. intros st H. inversion H as [HI HB].
    unfold not in HB. unfold bassn in HB. simpl in HB. rewrite negb_true_iff in HB.
    destruct (beq_nat (st X) 0) eqn:eq. apply beq_nat_true in eq. rewrite <- HI. rewrite eq.
    simpl. omega. destruct HB. reflexivity.
  - eapply hoare_consequence_pre. apply hoare_asgn. unfold assert_implies.
    intros st H. unfold assn_sub. subst.
    rewrite t_update_eq. rewrite t_update_neq. simpl. omega.
    apply beq_id_false_iff. reflexivity.
Qed.

