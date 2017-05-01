Require Export P02.



(** ** Exercise: Power Series *)

(** **** Exercise: 4 stars, optional (dpow2_down)  *)
(** Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

  X ::= 0;;
  Y ::= 1;;
  Z ::= 1;;
  WHILE X <> m DO
    Z ::= 2 * Z;;
    Y ::= Y + Z;;
    X ::= X + 1
  END

I = > Y = 2^X - 1 + Z /\ Z = 2^X                                    

    {{ True }} ->>
    {{ I [X |-> 0] [Y |-> 1] [Z |-> 1] }} // {{ 1 = 1 /\ 1 = 1}}
  X ::= 0;;
    {{ I [Y |-> 1] [Z |-> 2 * Z] }} // {{ 1 = 2^X /\ 1 = 2^X}}
  Y ::= 1;;
    {{ I [Z |-> 1] }} // {{ Y = 2^X /\ 1 = 2^X }}
  Z ::= 1;;
    {{ I }} // {{ Y = 2^X - 1 + Z /\ Z = 2^X }}
  WHILE X <> m DO
      {{ I /\ X <> m}} ->>
      {{ I [Z |-> 2 * Z] [Y |-> Y + Z] [X |-> X + 1] }} // {{ Y + 2 * Z = 2^(X+1) - 1 + 2 * Z /\ 2 * Z = 2^(X+1) }}
    Z ::= 2 * Z;;
      {{ I [Y |-> Y + Z] [X |-> X + 1] }} // {{ Y + Z = 2^(X+1) - 1 + Z /\ Z = 2^(X+1) }}
    Y ::= Y + Z;;
      {{ I [X |-> X + 1] }} // {{ Y = 2^(X+1) - 1 + Z /\ Z = 2^(X+1) }}
    X ::= X + 1
      {{ I }} // {{ Y = 2^X - 1 + Z /\ Z = 2^X }}
  END;;
    {{ I /\ X = m}} ->>  // {{ Y = 2^X - 1 + Z /\ Z = 2^X /\ X = m }}
    {{ Y = 2^(m+1) - 1 }}

    Write a decorated program for this. *)

Lemma pow_2_S : forall n,
    pow 2 (S n) = 2 * pow 2 n.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma pow_2_plus1 : forall n,
    pow 2 (n + 1) = 2 * pow 2 n.
Proof.
  intros. rewrite (Nat.add_1_r n). apply pow_2_S.
Qed.

Theorem dopw2_down_correct: forall m,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 1;;
  Z ::= ANum 1;;
  WHILE BNot (BEq (AId X) (ANum m)) DO
    Z ::= AMult (ANum 2) (AId Z);;
    Y ::= APlus (AId Y) (AId Z);;
    X ::= APlus (AId X) (ANum 1)
  END
  {{ fun st => st Y = pow 2 (S m) - 1 }}.
Proof.
  intros m. apply hoare_consequence with (P' := fun st => 1 = 1 /\ 1 = 1) (Q' := fun st => st Y = pow 2 (st X) - 1 + st Z /\ st Z = pow 2 (st X) /\  st X = m).
  - apply hoare_seq with (Q := fun st => 1 = pow 2 (st X) /\ 1 = pow 2 (st X)).
    apply hoare_seq with (Q := fun st => st Y = pow 2 (st X) /\ 1 = pow 2 (st X)).
    apply hoare_seq with (Q := fun st => st Y = pow 2 (st X) - 1 + st Z /\ st Z = pow 2 (st X)).
    + eapply hoare_consequence_post. apply hoare_while.
      * apply hoare_consequence_pre with (P' := fun st => st Y + 2 * (st Z) = pow 2 (st X + 1) - 1 + 2 * st Z /\ 2 * st Z = pow 2 (st X + 1)).
        apply hoare_seq with (Q := fun st => st Y + st Z = pow 2 (st X + 1) - 1 + st Z /\ st Z = pow 2 (st X + 1)).
        apply hoare_seq with (Q := fun st => st Y = pow 2 (st X + 1) - 1 + st Z /\ st Z = pow 2 (st X + 1)).
        { eapply hoare_consequence_pre. apply hoare_asgn.
          - unfold assert_implies, assn_sub. intros st H. simpl.
            rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_neq. assumption.
            unfold not. intros Hcontra. inversion Hcontra.
            unfold not. intros Hcontra. inversion Hcontra. }
        { eapply hoare_consequence_pre. apply hoare_asgn.
          - unfold assert_implies, assn_sub. intros st H. simpl.
            rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_neq. assumption.
            unfold not. intros Hcontra. inversion Hcontra.
            unfold not. intros Hcontra. inversion Hcontra. }
        { eapply hoare_consequence_pre. apply hoare_asgn.
          - unfold assert_implies, assn_sub. intros st H. simpl.
            rewrite t_update_eq. rewrite t_update_neq. rewrite t_update_neq. assumption.
            unfold not. intros Hcontra. inversion Hcontra.
            unfold not. intros Hcontra. inversion Hcontra. }
        { unfold assert_implies. intros st [[H HZ] HX]. split.
          - rewrite pow_2_plus1. rewrite H. rewrite HZ. omega.
          - rewrite pow_2_plus1. rewrite HZ. reflexivity. }
      * unfold assert_implies. intros st [[H HZ] HX]. split.
        { assumption. }
        { split.
          - assumption.
          - unfold not, bassn in HX. simpl in HX. rewrite negb_true_iff in HX.
            apply eq_false_true_abs in HX. apply beq_nat_true in HX. omega. }
    + unfold hoare_triple. intros st st' HZ [HY H]. inversion HZ. subst. simpl. split.
      * rewrite t_update_neq. rewrite t_update_neq. rewrite t_update_eq. omega.
        unfold not. intros Hcontra. inversion Hcontra.
        unfold not. intros Hcontra. inversion Hcontra.
      * rewrite t_update_eq. rewrite t_update_neq. assumption.
        unfold not. intros Hcontra. inversion Hcontra.
    + unfold hoare_triple. intros st st' HZ [HY H]. inversion HZ. subst. simpl. split.
      * rewrite t_update_eq. rewrite t_update_neq. assumption.
        unfold not. intros Hcontra. inversion Hcontra.
      * rewrite t_update_neq. assumption.
        unfold not. intros Hcontra. inversion Hcontra.
    + unfold hoare_triple. intros st st' H _. inversion H. subst. split.
      * rewrite t_update_eq. reflexivity.
      * rewrite t_update_eq. reflexivity.
  - unfold assert_implies. intros. split. reflexivity. reflexivity.
  - unfold assert_implies. intros st [HY [HZ HX]]. rewrite pow_2_S. subst. simpl. rewrite <- plus_n_O. omega.    
Qed.

