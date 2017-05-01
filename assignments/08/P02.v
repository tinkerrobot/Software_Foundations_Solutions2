Require Export P01.



(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if_wp]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_if_wp.
    + (* THEN *)
      apply hoare_asgn.
    + (* ELSE *)
      apply hoare_asgn.
  - intros st H. simpl. split.
    + intros Htrue. apply leb_complete in Htrue.
      unfold assn_sub, t_update, beq_id. simpl.
      apply le_plus_minus. assumption.
    + intros Hfalse. unfold assn_sub, t_update, beq_id. reflexivity.
Qed.